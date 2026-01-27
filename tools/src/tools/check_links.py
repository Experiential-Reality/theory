#!/usr/bin/env python3
"""Check for broken markdown links and anchors.

BLD Structure:
  B (Boundaries): Link types partition extraction/error behavior
  L (Links): Handler connects pattern → match → Link → validation → Error
  D (Dimensions): Files (D1), Links per file (D2), Handlers (D3)

  Phase 1 (D1 parallel): file_path → read → parse → (anchors, errors, links)
  Phase 2 (D2 parallel): (source, link) → resolve → lookup → error?
"""

from __future__ import annotations

import anyio
import bisect
import collections
import dataclasses
import enum
import os
import pathlib
import re
from typing import Protocol

# === Constants ===

DOCS_ROOT = pathlib.Path(__file__).parent.parent.parent.parent / "docs"

EXTERNAL_PREFIXES = ('http://', 'https://', 'mailto:')
SKIP_SUFFIXES = ('.png', '.jpg', '.jpeg', '.gif', '.svg', '.pdf', '/')
KEEP_CHARS: frozenset[str] = frozenset()

MAX_CONCURRENT_IO = 32
QUEUE_SIZE = 64
NUM_WORKERS = 4

# === Patterns (shared) ===

RE_BOLD = re.compile(r'\*\*([^*]+)\*\*')
RE_ITALIC = re.compile(r'\*([^*]+)\*')
RE_CODE = re.compile(r'`([^`]+)`')
RE_LINK_TEXT = re.compile(r'\[([^\]]+)\]\([^)]+\)')
RE_HEADER = re.compile(r'^#{1,6}\s+(.+)$', re.MULTILINE)
RE_CODE_REF = re.compile(r'^[a-z_]+$')
RE_CODE_FENCE = re.compile(r'```')
RE_NEWLINE = re.compile(r'\n')


# =============================================================================
# B: BOUNDARIES - Link Types
# =============================================================================

class LinkKind(enum.Enum):
    """Link type boundary - partitions extraction and error behavior."""
    INLINE = "inline"           # [text](url)
    REFERENCE = "reference"     # [text][ref] with [ref]: url
    UNDEFINED_REF = "undefined" # [text][ref] without definition


@dataclasses.dataclass
class Link:
    """A link extracted from markdown."""
    kind: LinkKind
    text: str
    url: str
    line: int
    pos: int
    ref: str | None = None  # For reference links

    def format_for_error(self) -> str:
        """Format link for error messages (type-specific)."""
        if self.kind == LinkKind.UNDEFINED_REF:
            return f"[...][{self.ref}]"
        elif self.kind == LinkKind.REFERENCE:
            return f"[{self.text}][{self.ref}] → {self.url}"
        else:
            return self.url


@dataclasses.dataclass
class Error:
    """A validation error."""
    file: str
    line: int
    link: str
    message: str


# =============================================================================
# L: LINKS - Handlers connect pattern → match → Link
# =============================================================================

Span = tuple[int, int]


@dataclasses.dataclass
class ContentIndex:
    """Pre-computed indices for a file's content."""
    content: str
    code_blocks: list[Span]
    line_starts: list[int]
    ref_defs: dict[str, str]  # [ref] → url


class LinkHandler(Protocol):
    """Protocol for link type handlers."""
    kind: LinkKind
    pattern: re.Pattern[str]

    def extract(self, match: re.Match[str], idx: ContentIndex) -> Link | None:
        """Extract link from match. Return None to skip."""
        ...


def _is_in_code_block(pos: int, blocks: list[Span]) -> bool:
    for start, end in blocks:
        if start <= pos < end:
            return True
        if start > pos:
            break
    return False


def _should_skip_url(url: str, text: str) -> bool:
    return (url.startswith(EXTERNAL_PREFIXES)
            or url.endswith(SKIP_SUFFIXES)
            or ' ' in url
            or (RE_CODE_REF.match(text) and not url.endswith('.md') and '#' not in url))


def _get_line(pos: int, line_starts: list[int]) -> int:
    return bisect.bisect_right(line_starts, pos)


# --- Inline Link Handler ---

class InlineLinkHandler:
    """Handler for [text](url) links."""
    kind = LinkKind.INLINE
    pattern = re.compile(r'\[([^\]]*)\]\(([^)]+)\)')

    def extract(self, match: re.Match[str], idx: ContentIndex) -> Link | None:
        pos = match.start()
        if _is_in_code_block(pos, idx.code_blocks):
            return None

        text, url = match.group(1), match.group(2)
        if _should_skip_url(url, text):
            return None

        return Link(
            kind=self.kind,
            text=text,
            url=url,
            line=_get_line(pos, idx.line_starts),
            pos=pos,
        )


# --- Reference Link Handler ---

class ReferenceLinkHandler:
    """Handler for [text][ref] links."""
    kind = LinkKind.REFERENCE
    pattern = re.compile(r'\[([^\]]*)\]\[([^\]]+)\]')

    def extract(self, match: re.Match[str], idx: ContentIndex) -> Link | None:
        pos = match.start()
        if _is_in_code_block(pos, idx.code_blocks):
            return None

        text = match.group(1)
        ref = match.group(2).lower()
        line = _get_line(pos, idx.line_starts)

        # Check if reference is defined
        if ref not in idx.ref_defs:
            return Link(
                kind=LinkKind.UNDEFINED_REF,
                text=text,
                url="",
                ref=ref,
                line=line,
                pos=pos,
            )

        url = idx.ref_defs[ref]
        if _should_skip_url(url, text):
            return None

        return Link(
            kind=LinkKind.REFERENCE,
            text=text,
            url=url,
            ref=ref,
            line=line,
            pos=pos,
        )


# =============================================================================
# D: DIMENSIONS - Uniform iteration over handlers
# =============================================================================

LINK_HANDLERS: list[LinkHandler] = [
    InlineLinkHandler(),
    ReferenceLinkHandler(),
]


def extract_all_links(idx: ContentIndex) -> list[Link]:
    """D3: Iterate all handlers uniformly to extract links."""
    links = []
    for handler in LINK_HANDLERS:
        for match in handler.pattern.finditer(idx.content):
            if link := handler.extract(match, idx):
                links.append(link)
    return links


# =============================================================================
# Supporting functions
# =============================================================================

def _build_code_block_index(content: str) -> list[Span]:
    blocks = []
    in_block = False
    start = 0
    for match in RE_CODE_FENCE.finditer(content):
        if in_block:
            blocks.append((start, match.end()))
            in_block = False
        else:
            start = match.start()
            in_block = True
    return blocks


def _extract_ref_definitions(content: str) -> dict[str, str]:
    """Extract [ref]: url definitions."""
    pattern = re.compile(r'^\[([^\]]+)\]:\s*(\S+)', re.MULTILINE)
    return {m.group(1).lower(): m.group(2) for m in pattern.finditer(content)}


def build_content_index(content: str) -> ContentIndex:
    """Build all indices for a file."""
    return ContentIndex(
        content=content,
        code_blocks=_build_code_block_index(content),
        line_starts=[0] + [m.end() for m in RE_NEWLINE.finditer(content)],
        ref_defs=_extract_ref_definitions(content),
    )


def _strip_markdown(text: str) -> str:
    text = RE_BOLD.sub(r'\1', text)
    text = RE_ITALIC.sub(r'\1', text)
    text = RE_CODE.sub(r'\1', text)
    text = RE_LINK_TEXT.sub(r'\1', text)
    return text


def header_to_anchor(header: str) -> str:
    """Convert header text to GitHub-compatible anchor."""
    header = _strip_markdown(header)
    anchor = ''.join(
        c for c in header.lower()
        if c.isalnum() or c in ' -_' or c in KEEP_CHARS
    )
    return anchor.replace(' ', '-').replace('_', '-').strip('-')


def extract_headers(content: str) -> set[str]:
    """Extract all header anchors from content."""
    anchors = set()
    for match in RE_HEADER.finditer(content):
        header = match.group(1).strip()
        anchors.add(header_to_anchor(header))
    return anchors


# =============================================================================
# Data structures for file processing
# =============================================================================

@dataclasses.dataclass
class FileData:
    """Extracted data from a markdown file."""
    anchors: set[str]
    inter_file_links: list[Link]


Files = dict[pathlib.Path, FileData]


# =============================================================================
# Validation
# =============================================================================

def find_similar(anchor: str, valid: set[str], limit: int = 3) -> list[str]:
    """Find similar anchors for error hints."""
    normalized = anchor.replace('-', '')
    return [
        h for h in valid
        if normalized in h.replace('-', '') or h.replace('-', '') in normalized
    ][:limit]


def validate_anchor(anchor: str, anchors: set[str], source: pathlib.Path, link: Link) -> Error | None:
    """Validate anchor exists, return Error if not."""
    if anchor not in anchors:
        similar = find_similar(anchor, anchors)
        hint = f" Similar: {similar}" if similar else ""
        return Error(str(source), link.line, link.format_for_error(),
                    f"Anchor #{anchor} not found.{hint}")
    return None


# =============================================================================
# Processing
# =============================================================================

def process_content(path: pathlib.Path, content: str) -> tuple[FileData, list[Error]]:
    """Process a single file: extract links, validate intra-file anchors."""
    idx = build_content_index(content)
    anchors = extract_headers(content)

    errors = []
    inter_file_links = []

    for link in extract_all_links(idx):
        # Handle undefined references immediately
        if link.kind == LinkKind.UNDEFINED_REF:
            errors.append(Error(
                str(path), link.line, link.format_for_error(),
                f"Reference [{link.ref}] is not defined"
            ))
            continue

        # Validate intra-file anchors, collect inter-file links
        if link.url.startswith('#'):
            if error := validate_anchor(link.url[1:], anchors, path, link):
                errors.append(error)
        else:
            inter_file_links.append(link)

    return FileData(anchors, inter_file_links), errors


def resolve_target(link: Link, source: pathlib.Path, docs_root: pathlib.Path) -> tuple[pathlib.Path, str | None]:
    """Resolve link URL to target file and optional anchor."""
    if '#' in link.url:
        file_part, anchor = link.url.split('#', 1)
    else:
        file_part, anchor = link.url, None

    if file_part.startswith('/'):
        target = docs_root / file_part[1:]
    else:
        target = pathlib.Path(os.path.normpath(source.parent / file_part))
    return target, anchor


def validate_inter_file_links(files: Files, docs_root: pathlib.Path) -> list[Error]:
    """Phase 2: Validate all inter-file links."""
    errors = []
    for source, data in files.items():
        for link in data.inter_file_links:
            target_file, anchor = resolve_target(link, source, docs_root)

            if target_file not in files:
                errors.append(Error(str(source), link.line, link.format_for_error(),
                            f"File not found: {link.url.split('#')[0]}"))
                continue

            if anchor:
                if error := validate_anchor(anchor, files[target_file].anchors, source, link):
                    errors.append(error)
    return errors


# =============================================================================
# Collection (Phase 1)
# =============================================================================

async def collect_files_async(docs_root: pathlib.Path) -> tuple[Files, list[Error]]:
    """Phase 1: Load and process all files with bounded concurrency."""
    paths = list(docs_root.rglob("*.md"))
    io_sem = anyio.Semaphore(MAX_CONCURRENT_IO)
    send_stream, receive_stream = anyio.create_memory_object_stream[tuple[pathlib.Path, str]](
        max_buffer_size=QUEUE_SIZE
    )
    results: list[tuple[pathlib.Path, FileData, list[Error]]] = []

    async def load_one(path: pathlib.Path):
        async with io_sem:
            apath = anyio.Path(os.path.normpath(path))
            content = await apath.read_text()
        async with send_stream.clone() as stream:
            await stream.send((pathlib.Path(os.path.normpath(path)), content))

    async def producer():
        async with send_stream:
            async with anyio.create_task_group() as tg:
                for path in paths:
                    tg.start_soon(load_one, path)

    async def worker():
        async with receive_stream.clone() as stream:
            async for path, content in stream:
                file_data, errors = process_content(path, content)
                results.append((path, file_data, errors))

    async with anyio.create_task_group() as tg:
        tg.start_soon(producer)
        for _ in range(NUM_WORKERS):
            tg.start_soon(worker)

    files = {path: data for path, data, _ in results}
    errors = [e for _, _, errs in results for e in errs]
    return files, errors


def collect_files_sync(docs_root: pathlib.Path) -> tuple[Files, list[Error]]:
    """Sequential version for benchmarking."""
    files: Files = {}
    errors: list[Error] = []

    for path in docs_root.rglob("*.md"):
        path = pathlib.Path(os.path.normpath(path))
        content = path.read_text(encoding='utf-8')
        file_data, file_errors = process_content(path, content)
        files[path] = file_data
        errors.extend(file_errors)

    return files, errors


# =============================================================================
# Reporting
# =============================================================================

def report(errors: list[Error]) -> int:
    """Report errors grouped by file."""
    if not errors:
        print("No broken links found!")
        return 0

    by_file = collections.defaultdict(list)
    for err in errors:
        by_file[err.file].append(err)

    print(f"Found {len(errors)} broken links in {len(by_file)} files:\n")
    for filepath, file_errors in sorted(by_file.items()):
        print(f"\n{filepath}:")
        for err in file_errors:
            print(f"  L{err.line}: {err.link}")
            print(f"         {err.message}")

    return 1


# =============================================================================
# Entry points
# =============================================================================

def run_async(docs_root: pathlib.Path = DOCS_ROOT) -> int:
    files, intra_errors = anyio.run(collect_files_async, docs_root)
    print(f"Checking {len(files)} markdown files...\n")
    inter_errors = validate_inter_file_links(files, docs_root)
    return report(intra_errors + inter_errors)


def run_sync(docs_root: pathlib.Path = DOCS_ROOT) -> int:
    files, intra_errors = collect_files_sync(docs_root)
    print(f"Checking {len(files)} markdown files...\n")
    inter_errors = validate_inter_file_links(files, docs_root)
    return report(intra_errors + inter_errors)


def main() -> int:
    docs_root = DOCS_ROOT.resolve()
    if not docs_root.exists():
        docs_root = pathlib.Path("docs").resolve()
    return run_async(docs_root)


if __name__ == "__main__":
    exit(main())
