#!/usr/bin/env python3
"""Check for broken markdown links and anchors.

BLD Structure:
  B: LinkKind, ErrorKind - partition link/error types
  L: extract_links → process_file → validate_inter_file
  D: Files (async generator), Links per file (generator)

All functions return/yield data. Only main() handles IO.
"""

import bisect
import collections
import dataclasses
import enum
import os
import re
import sys
import typing

import anyio

DOCS_ROOT = anyio.Path(__file__).parent.parent.parent.parent / "docs"
EXTERNAL_PREFIXES = ("http://", "https://", "mailto:")
SKIP_SUFFIXES = (".png", ".jpg", ".jpeg", ".gif", ".svg", ".pdf", "/")
MAX_CONCURRENT_IO = 32

# Compiled regex patterns
INLINE_LINK_PATTERN = re.compile(r"\[([^\]]*)\]\(([^)]+)\)")
REF_LINK_PATTERN = re.compile(r"\[([^\]]*)\]\[([^\]]+)\]")
REF_DEF_PATTERN = re.compile(r"^\[([^\]]+)\]:\s*(\S+)", re.MULTILINE)
HEADER_PATTERN = re.compile(r"^#{1,6}\s+(.+)$", re.MULTILINE)
CODE_FENCE_PATTERN = re.compile(r"```")
CODE_REF_PATTERN = re.compile(r"^[a-z_]+$")
STRIP_MD_PATTERN = re.compile(r"\*\*([^*]+)\*\*|\*([^*]+)\*|`([^`]+)`|\[([^\]]+)\]\([^)]+\)")


class LinkKind(enum.Enum):
    INLINE = "inline"
    REFERENCE = "reference"
    UNDEFINED_REF = "undefined"


class ErrorKind(enum.Enum):
    UNDEFINED_REF = "undefined_ref"
    FILE_NOT_FOUND = "file_not_found"
    ANCHOR_NOT_FOUND = "anchor_not_found"


@dataclasses.dataclass(slots=True)
class Link:
    kind: LinkKind
    text: str
    url: str
    line: int
    ref: str | None = None

    def format_for_error(self) -> str:
        if self.kind == LinkKind.UNDEFINED_REF:
            return f"[...][{self.ref}]"
        if self.kind == LinkKind.REFERENCE:
            return f"[{self.text}][{self.ref}] → {self.url}"
        return self.url


@dataclasses.dataclass(slots=True)
class Error:
    kind: ErrorKind
    file: str
    line: int
    link: str
    message: str


@dataclasses.dataclass(slots=True)
class FileData:
    anchors: frozenset[str]
    inter_file_links: tuple[Link, ...]


Files = dict[anyio.Path, FileData]


def _in_code_block(pos: int, blocks: list[tuple[int, int]]) -> bool:
    for start, end in blocks:
        if start <= pos < end:
            return True
        if start > pos:
            break
    return False


def _should_skip(url: str, text: str) -> bool:
    return (
        url.startswith(EXTERNAL_PREFIXES)
        or url.endswith(SKIP_SUFFIXES)
        or " " in url
        or bool(CODE_REF_PATTERN.match(text) and not url.endswith(".md") and "#" not in url)
    )


def _build_code_blocks(content: str) -> list[tuple[int, int]]:
    blocks, in_block, start = [], False, 0
    for m in CODE_FENCE_PATTERN.finditer(content):
        if in_block:
            blocks.append((start, m.end()))
            in_block = False
        else:
            start = m.start()
            in_block = True
    return blocks


def extract_links(content: str) -> typing.Iterator[Link]:
    """Yield links from markdown content."""
    blocks = _build_code_blocks(content)
    line_starts = [0] + [m.end() for m in re.finditer(r"\n", content)]
    ref_defs = {m.group(1).lower(): m.group(2) for m in REF_DEF_PATTERN.finditer(content)}

    for m in INLINE_LINK_PATTERN.finditer(content):
        pos = m.start()
        if _in_code_block(pos, blocks):
            continue
        text, url = m.group(1), m.group(2)
        if _should_skip(url, text):
            continue
        yield Link(LinkKind.INLINE, text, url, bisect.bisect_right(line_starts, pos))

    for m in REF_LINK_PATTERN.finditer(content):
        pos = m.start()
        if _in_code_block(pos, blocks):
            continue
        text, ref = m.group(1), m.group(2).lower()
        line = bisect.bisect_right(line_starts, pos)
        if ref not in ref_defs:
            yield Link(LinkKind.UNDEFINED_REF, text, "", line, ref=ref)
            continue
        url = ref_defs[ref]
        if _should_skip(url, text):
            continue
        yield Link(LinkKind.REFERENCE, text, url, line, ref=ref)


def header_to_anchor(header: str) -> str:
    """Convert header text to GitHub-compatible anchor."""
    header = STRIP_MD_PATTERN.sub(
        lambda m: m.group(1) or m.group(2) or m.group(3) or m.group(4), header
    )
    anchor = "".join(c for c in header.lower() if c.isalnum() or c in " -_")
    return anchor.replace(" ", "-").replace("_", "-").strip("-")


def extract_headers(content: str) -> typing.Iterator[str]:
    """Yield header anchors from content."""
    for m in HEADER_PATTERN.finditer(content):
        yield header_to_anchor(m.group(1).strip())


def find_similar(anchor: str, valid: frozenset[str], limit: int = 3) -> list[str]:
    """Find similar anchors for error hints."""
    n = anchor.replace("-", "")
    return [h for h in valid if n in h.replace("-", "") or h.replace("-", "") in n][:limit]


def validate_anchor(
    anchor: str, anchors: frozenset[str], source: anyio.Path, link: Link
) -> Error | None:
    if anchor in anchors:
        return None
    similar = find_similar(anchor, anchors)
    hint = f" Similar: {similar}" if similar else ""
    return Error(
        ErrorKind.ANCHOR_NOT_FOUND,
        str(source),
        link.line,
        link.format_for_error(),
        f"Anchor #{anchor} not found.{hint}",
    )


def process_file(
    path: anyio.Path, content: str
) -> tuple[FileData, typing.Iterator[Error]]:
    """Process file, return data and yield intra-file errors."""
    anchors = frozenset(extract_headers(content))
    inter_file: list[Link] = []

    def errors() -> typing.Iterator[Error]:
        for link in extract_links(content):
            if link.kind == LinkKind.UNDEFINED_REF:
                yield Error(
                    ErrorKind.UNDEFINED_REF,
                    str(path),
                    link.line,
                    link.format_for_error(),
                    f"Reference [{link.ref}] is not defined",
                )
            elif link.url.startswith("#"):
                if err := validate_anchor(link.url[1:], anchors, path, link):
                    yield err
            else:
                inter_file.append(link)

    err_iter = errors()
    errs = list(err_iter)  # Must consume to populate inter_file
    return FileData(anchors, tuple(inter_file)), iter(errs)


def resolve_target(
    link: Link, source: anyio.Path, docs_root: anyio.Path
) -> tuple[anyio.Path, str | None]:
    file_part, _, anchor_part = link.url.partition("#")
    anchor = anchor_part or None
    if file_part.startswith("/"):
        return docs_root / file_part[1:], anchor
    return anyio.Path(os.path.normpath(source.parent / file_part)), anchor


def validate_inter_file(
    files: Files, docs_root: anyio.Path
) -> typing.Iterator[Error]:
    """Yield errors for broken inter-file links."""
    for source, data in files.items():
        for link in data.inter_file_links:
            target, anchor = resolve_target(link, source, docs_root)
            if target not in files:
                yield Error(
                    ErrorKind.FILE_NOT_FOUND,
                    str(source),
                    link.line,
                    link.format_for_error(),
                    f"File not found: {link.url.split('#')[0]}",
                )
            elif anchor and (
                err := validate_anchor(anchor, files[target].anchors, source, link)
            ):
                yield err


async def collect_files(
    docs_root: os.PathLike[str],
) -> typing.AsyncIterator[tuple[anyio.Path, FileData, list[Error]]]:
    """Yield (path, data, errors) as each file is processed."""
    docs_root = anyio.Path(docs_root)
    sem = anyio.Semaphore(MAX_CONCURRENT_IO)
    send, recv = anyio.create_memory_object_stream[
        tuple[anyio.Path, FileData, list[Error]]
    ](32)

    async def process_one(path: anyio.Path) -> None:
        async with sem:
            content = await path.read_text()
        norm = await path.resolve()
        data, errs = process_file(norm, content)
        await send.send((norm, data, list(errs)))

    async def producer() -> None:
        async with send:
            async with anyio.create_task_group() as tg:
                async for path in docs_root.rglob("*.md"):
                    tg.start_soon(process_one, path)

    async with anyio.create_task_group() as tg:
        tg.start_soon(producer)
        async with recv:
            async for item in recv:
                yield item


async def check(docs_root: os.PathLike[str]) -> tuple[int, typing.Iterator[Error]]:
    """Check all files, return (file_count, error_iterator)."""
    docs_root = anyio.Path(docs_root)
    files: Files = {}
    intra_errors: list[Error] = []

    async for path, data, errs in collect_files(docs_root):
        files[path] = data
        intra_errors.extend(errs)

    def all_errors() -> typing.Iterator[Error]:
        yield from intra_errors
        yield from validate_inter_file(files, docs_root)

    return len(files), all_errors()


def format_errors(errors: typing.Iterator[Error]) -> typing.Iterator[str]:
    """Format errors grouped by file, yield output lines."""
    by_file: dict[str, list[Error]] = collections.defaultdict(list)
    for e in errors:
        by_file[e.file].append(e)

    if not by_file:
        yield "No broken links found!"
        return

    total = sum(len(errs) for errs in by_file.values())
    yield f"Found {total} broken links in {len(by_file)} files:\n"

    for path, errs in sorted(by_file.items()):
        yield f"\n{path}:"
        for e in errs:
            yield f"  L{e.line}: {e.link}"
            yield f"         {e.message}"


async def async_main() -> int:
    docs_root = await DOCS_ROOT.resolve()
    if not await docs_root.exists():
        print(f"Error: docs root not found: {docs_root}", file=sys.stderr)
        return 2

    file_count, errors = await check(docs_root)
    print(f"Checking {file_count} markdown files...\n", file=sys.stderr)

    errors_list = list(errors)
    for line in format_errors(iter(errors_list)):
        print(line)

    return 1 if errors_list else 0


def main() -> int:
    return anyio.run(async_main)


if __name__ == "__main__":
    sys.exit(main())
