#!/usr/bin/env python3
"""Check for broken markdown links and anchors.

BLD Structure:
  B: LinkKind (inline/reference/undefined), ErrorKind (undefined_ref/file_not_found/anchor_not_found)
  L: extract_links → process_content → validate_inter_file_links
  D: Files (async), Links per file, Patterns (inline/reference)

  Phase 1: collect_files → process_content per file → (anchors, errors, inter_file_links)
  Phase 2: validate_inter_file_links → resolve targets → check anchors
"""

import anyio
import bisect
import collections
import dataclasses
import enum
import os
import pathlib
import re

DOCS_ROOT = pathlib.Path(__file__).parent.parent.parent.parent / "docs"
EXTERNAL_PREFIXES = ('http://', 'https://', 'mailto:')
SKIP_SUFFIXES = ('.png', '.jpg', '.jpeg', '.gif', '.svg', '.pdf', '/')
MAX_CONCURRENT_IO = 32

RE_INLINE_LINK = re.compile(r'\[([^\]]*)\]\(([^)]+)\)')
RE_REF_LINK = re.compile(r'\[([^\]]*)\]\[([^\]]+)\]')
RE_REF_DEF = re.compile(r'^\[([^\]]+)\]:\s*(\S+)', re.MULTILINE)
RE_HEADER = re.compile(r'^#{1,6}\s+(.+)$', re.MULTILINE)
RE_CODE_FENCE = re.compile(r'```')
RE_CODE_REF = re.compile(r'^[a-z_]+$')
RE_STRIP_MD = re.compile(r'\*\*([^*]+)\*\*|\*([^*]+)\*|`([^`]+)`|\[([^\]]+)\]\([^)]+\)')


class LinkKind(enum.Enum):
    INLINE = "inline"
    REFERENCE = "reference"
    UNDEFINED_REF = "undefined"


class ErrorKind(enum.Enum):
    UNDEFINED_REF = "undefined_ref"
    FILE_NOT_FOUND = "file_not_found"
    ANCHOR_NOT_FOUND = "anchor_not_found"


@dataclasses.dataclass
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


@dataclasses.dataclass
class Error:
    kind: ErrorKind
    file: str
    line: int
    link: str
    message: str


@dataclasses.dataclass
class FileData:
    anchors: set[str]
    inter_file_links: list[Link]


Files = dict[pathlib.Path, FileData]


def _in_code_block(pos: int, blocks: list[tuple[int, int]]) -> bool:
    for start, end in blocks:
        if start <= pos < end:
            return True
        if start > pos:
            break
    return False


def _should_skip(url: str, text: str) -> bool:
    return (url.startswith(EXTERNAL_PREFIXES) or url.endswith(SKIP_SUFFIXES)
            or ' ' in url or (RE_CODE_REF.match(text) and not url.endswith('.md') and '#' not in url))


def _build_code_blocks(content: str) -> list[tuple[int, int]]:
    blocks, in_block, start = [], False, 0
    for m in RE_CODE_FENCE.finditer(content):
        if in_block:
            blocks.append((start, m.end()))
            in_block = False
        else:
            start = m.start()
            in_block = True
    return blocks


def extract_links(content: str) -> list[Link]:
    """Extract all links from markdown content."""
    blocks = _build_code_blocks(content)
    line_starts = [0] + [m.end() for m in re.finditer(r'\n', content)]
    ref_defs = {m.group(1).lower(): m.group(2) for m in RE_REF_DEF.finditer(content)}
    links = []

    for m in RE_INLINE_LINK.finditer(content):
        pos = m.start()
        if _in_code_block(pos, blocks):
            continue
        text, url = m.group(1), m.group(2)
        if _should_skip(url, text):
            continue
        links.append(Link(LinkKind.INLINE, text, url, bisect.bisect_right(line_starts, pos)))

    for m in RE_REF_LINK.finditer(content):
        pos = m.start()
        if _in_code_block(pos, blocks):
            continue
        text, ref = m.group(1), m.group(2).lower()
        line = bisect.bisect_right(line_starts, pos)
        if ref not in ref_defs:
            links.append(Link(LinkKind.UNDEFINED_REF, text, "", line, ref=ref))
            continue
        url = ref_defs[ref]
        if _should_skip(url, text):
            continue
        links.append(Link(LinkKind.REFERENCE, text, url, line, ref=ref))

    return links


def header_to_anchor(header: str) -> str:
    """Convert header text to GitHub-compatible anchor."""
    header = RE_STRIP_MD.sub(lambda m: m.group(1) or m.group(2) or m.group(3) or m.group(4), header)
    anchor = ''.join(c for c in header.lower() if c.isalnum() or c in ' -_')
    return anchor.replace(' ', '-').replace('_', '-').strip('-')


def extract_headers(content: str) -> set[str]:
    return {header_to_anchor(m.group(1).strip()) for m in RE_HEADER.finditer(content)}


def find_similar(anchor: str, valid: set[str], limit: int = 3) -> list[str]:
    """Find similar anchors for error hints."""
    n = anchor.replace('-', '')
    return [h for h in valid if n in h.replace('-', '') or h.replace('-', '') in n][:limit]


def validate_anchor(anchor: str, anchors: set[str], source: pathlib.Path, link: Link) -> Error | None:
    if anchor in anchors:
        return None
    similar = find_similar(anchor, anchors)
    hint = f" Similar: {similar}" if similar else ""
    return Error(ErrorKind.ANCHOR_NOT_FOUND, str(source), link.line,
                link.format_for_error(), f"Anchor #{anchor} not found.{hint}")


def process_content(path: pathlib.Path, content: str) -> tuple[FileData, list[Error]]:
    """Process a single file: extract links, validate intra-file anchors."""
    anchors = extract_headers(content)
    errors, inter_file = [], []

    for link in extract_links(content):
        if link.kind == LinkKind.UNDEFINED_REF:
            errors.append(Error(ErrorKind.UNDEFINED_REF, str(path), link.line,
                               link.format_for_error(), f"Reference [{link.ref}] is not defined"))
        elif link.url.startswith('#'):
            if err := validate_anchor(link.url[1:], anchors, path, link):
                errors.append(err)
        else:
            inter_file.append(link)

    return FileData(anchors, inter_file), errors


def resolve_target(link: Link, source: pathlib.Path, docs_root: pathlib.Path) -> tuple[pathlib.Path, str | None]:
    file_part, _, anchor = link.url.partition('#')
    anchor = anchor or None
    if file_part.startswith('/'):
        return docs_root / file_part[1:], anchor
    return pathlib.Path(os.path.normpath(source.parent / file_part)), anchor


def validate_inter_file_links(files: Files, docs_root: pathlib.Path) -> list[Error]:
    errors = []
    for source, data in files.items():
        for link in data.inter_file_links:
            target, anchor = resolve_target(link, source, docs_root)
            if target not in files:
                errors.append(Error(ErrorKind.FILE_NOT_FOUND, str(source), link.line,
                                   link.format_for_error(), f"File not found: {link.url.split('#')[0]}"))
            elif anchor and (err := validate_anchor(anchor, files[target].anchors, source, link)):
                errors.append(err)
    return errors


async def collect_files(docs_root: pathlib.Path) -> tuple[Files, list[Error]]:
    paths = list(docs_root.rglob("*.md"))
    sem = anyio.Semaphore(MAX_CONCURRENT_IO)
    results: list[tuple[pathlib.Path, FileData, list[Error]]] = []

    async def process_one(path: pathlib.Path):
        async with sem:
            content = await anyio.Path(path).read_text()
        norm = pathlib.Path(os.path.normpath(path))
        data, errs = process_content(norm, content)
        results.append((norm, data, errs))

    async with anyio.create_task_group() as tg:
        for p in paths:
            tg.start_soon(process_one, p)

    return {p: d for p, d, _ in results}, [e for _, _, errs in results for e in errs]


def report(errors: list[Error]) -> int:
    if not errors:
        print("No broken links found!")
        return 0

    by_file = collections.defaultdict(list)
    for e in errors:
        by_file[e.file].append(e)

    print(f"Found {len(errors)} broken links in {len(by_file)} files:\n")
    for path, errs in sorted(by_file.items()):
        print(f"\n{path}:")
        for e in errs:
            print(f"  L{e.line}: {e.link}\n         {e.message}")
    return 1


def run(docs_root: pathlib.Path = DOCS_ROOT) -> int:
    files, intra = anyio.run(collect_files, docs_root)
    print(f"Checking {len(files)} markdown files...\n")
    return report(intra + validate_inter_file_links(files, docs_root))


def main() -> int:
    docs_root = DOCS_ROOT.resolve()
    if not docs_root.exists():
        raise FileNotFoundError(f"Docs root not found: {docs_root}")
    return run(docs_root)


if __name__ == "__main__":
    exit(main())
