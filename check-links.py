#!/usr/bin/env python3
"""Check for broken markdown links and anchors in docs/

Two parallel dimensions:
  D1: per-file (intra-file links validated immediately)
  D2: per-link (inter-file links validated after all files loaded)

Cost optimizations:
  - Code block detection: O(n) precompute, O(b) lookup where b = blocks
  - Line numbers: O(n) precompute, O(log n) lookup
  - Regex patterns: compiled once at module level
"""

import bisect
import collections
import dataclasses
import os
import pathlib
import re

# === Constants ===

DOCS_ROOT = pathlib.Path("docs").resolve()

EXTERNAL_PREFIXES = ('http://', 'https://', 'mailto:')
SKIP_SUFFIXES = ('.png', '.jpg', '.jpeg', '.gif', '.svg', '.pdf', '/')
KEEP_CHARS = frozenset('×')

# === Patterns ===

RE_BOLD = re.compile(r'\*\*([^*]+)\*\*')
RE_ITALIC = re.compile(r'\*([^*]+)\*')
RE_CODE = re.compile(r'`([^`]+)`')
RE_LINK = re.compile(r'\[([^\]]+)\]\([^)]+\)')
RE_HEADER = re.compile(r'^#{1,6}\s+(.+)$', re.MULTILINE)
RE_EXPLICIT_ANCHOR = re.compile(r'\{#([^}]+)\}')
RE_ANCHOR_SYNTAX = re.compile(r'\s*\{#[^}]+\}')
RE_MD_LINK = re.compile(r'\[([^\]]*)\]\(([^)]+)\)')
RE_CODE_REF = re.compile(r'^[a-z_]+$')
RE_CODE_FENCE = re.compile(r'```')
RE_NEWLINE = re.compile(r'\n')


# === Data structures ===

@dataclasses.dataclass
class Link:
    text: str
    url: str
    line: int
    pos: int

@dataclasses.dataclass
class Error:
    file: str
    line: int
    link: str
    message: str

# Type aliases
Span = tuple[int, int]  # (start, end) position

@dataclasses.dataclass
class ContentIndex:
    """Precomputed indices for O(1) lookups."""
    content: str
    code_blocks: list[Span]
    line_starts: list[int]

@dataclasses.dataclass
class FileData:
    """Per-file data needed for inter-file validation."""
    anchors: set[str]
    inter_file_links: list[Link]

Files = dict[pathlib.Path, FileData]


# === Index builders ===

def build_code_block_index(content: str) -> list[Span]:
    """Find all code block ranges. O(n) once."""
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

def build_content_index(content: str) -> ContentIndex:
    """Build all indices for a file."""
    return ContentIndex(
        content=content,
        code_blocks=build_code_block_index(content),
        line_starts=[0] + [m.end() for m in RE_NEWLINE.finditer(content)]
    )


# === Skip predicates ===

def is_code_reference(text: str, url: str) -> bool:
    return (RE_CODE_REF.match(text)
            and not url.endswith('.md')
            and '#' not in url)

def is_in_code_block(pos: int, blocks: list[Span]) -> bool:
    """O(b) where b = code blocks (typically <20). Early-break on sorted blocks."""
    for start, end in blocks:
        if start <= pos < end:
            return True
        if start > pos:
            break
    return False

def should_skip(link: Link, blocks: list[Span]) -> bool:
    url = link.url
    return (url.startswith(EXTERNAL_PREFIXES)
            or url.endswith(SKIP_SUFFIXES)
            or ' ' in url
            or is_code_reference(link.text, url)
            or is_in_code_block(link.pos, blocks))


# === Transformations ===

def strip_markdown(text: str) -> str:
    """Remove markdown formatting."""
    text = RE_BOLD.sub(r'\1', text)
    text = RE_ITALIC.sub(r'\1', text)
    text = RE_CODE.sub(r'\1', text)
    text = RE_LINK.sub(r'\1', text)
    return text

def header_to_anchor(header: str) -> str:
    """Convert header to GitHub anchor."""
    header = strip_markdown(header)
    anchor = ''.join(
        c for c in header.lower()
        if c.isalnum() or c in ' -_' or c in KEEP_CHARS
    )
    return anchor.replace(' ', '-').replace('_', '-').strip('-')

# === Extraction ===

def extract_headers(content: str) -> set[str]:
    """Extract all anchors from content."""
    anchors = set()
    for match in RE_HEADER.finditer(content):
        header = match.group(1).strip()
        explicit = RE_EXPLICIT_ANCHOR.search(header)
        if explicit:
            anchors.add(explicit.group(1))
            header = RE_ANCHOR_SYNTAX.sub('', header)
        anchors.add(header_to_anchor(header))
    return anchors

def extract_links(idx: ContentIndex) -> list[Link]:
    """Extract links with O(log n) line lookup."""
    links = []
    for match in RE_MD_LINK.finditer(idx.content):
        pos = match.start()
        link = Link(
            text=match.group(1),
            url=match.group(2),
            line=bisect.bisect_right(idx.line_starts, pos),
            pos=pos
        )
        if not should_skip(link, idx.code_blocks):
            links.append(link)
    return links


# === Resolution ===

def resolve_target(link: Link, source: pathlib.Path) -> tuple[pathlib.Path, str | None]:
    """Parse inter-file link into (file, anchor). Uses normpath to avoid syscalls."""
    if '#' in link.url:
        file_part, anchor = link.url.split('#', 1)
    else:
        file_part, anchor = link.url, None

    if file_part.startswith('/'):
        target = DOCS_ROOT / file_part[1:]
    else:
        target = pathlib.Path(os.path.normpath(source.parent / file_part))
    return target, anchor

def find_similar(anchor: str, valid: set[str], limit: int = 3) -> list[str]:
    """Find likely typos."""
    normalized = anchor.replace('-', '')
    return [
        h for h in valid
        if normalized in h.replace('-', '') or h.replace('-', '') in normalized
    ][:limit]

def validate_anchor(anchor: str, anchors: set[str], source: pathlib.Path, link: Link) -> Error | None:
    """Validate anchor exists in anchor set."""
    if anchor not in anchors:
        similar = find_similar(anchor, anchors)
        hint = f" Similar: {similar}" if similar else ""
        return Error(str(source), link.line, link.url,
                    f"Anchor #{anchor} not found.{hint}")
    return None


# === Main ===

def process_content(path: pathlib.Path, content: str) -> tuple[FileData, list[Error]]:
    """CPU: process already-loaded content."""
    index = build_content_index(content)
    anchors = extract_headers(content)

    errors = []
    inter_file_links = []

    for link in extract_links(index):
        if link.url.startswith('#'):
            if error := validate_anchor(link.url[1:], anchors, path, link):
                errors.append(error)
        else:
            inter_file_links.append(link)

    return FileData(anchors, inter_file_links), errors

def process_batch(items: list[tuple[pathlib.Path, str]]) -> list[tuple[pathlib.Path, FileData, list[Error]]]:
    """Process a batch of files. Runs in thread."""
    return [(path, *process_content(path, content)) for path, content in items]

async def collect_files_async() -> tuple[Files, list[Error]]:
    """Load all files, then process in parallel batches."""
    # Phase 1: Load all files (sync I/O, fast)
    items = [
        (pathlib.Path(os.path.normpath(p)), p.read_text(encoding='utf-8'))
        for p in DOCS_ROOT.rglob("*.md")
    ]

    # Phase 2: Process in parallel batches
    num_workers = 4
    batch_size = (len(items) + num_workers - 1) // num_workers
    batches = [items[i:i + batch_size] for i in range(0, len(items), batch_size)]

    batch_results = await asyncio.gather(*[
        asyncio.to_thread(process_batch, batch) for batch in batches
    ])

    # Flatten results
    files: Files = {}
    errors: list[Error] = []
    for batch in batch_results:
        for path, file_data, file_errors in batch:
            files[path] = file_data
            errors.extend(file_errors)

    return files, errors

def collect_files() -> tuple[Files, list[Error]]:
    """Entry point for sync callers."""
    return asyncio.run(collect_files_async())

def validate_inter_file_links(files: Files) -> list[Error]:
    """Validate inter-file links. D2: embarrassingly parallel per link."""
    errors = []
    for source, data in files.items():
        for link in data.inter_file_links:
            target_file, anchor = resolve_target(link, source)

            # Direct lookup - paths already normalized via normpath
            if target_file not in files:
                errors.append(Error(str(source), link.line, link.url,
                            f"File not found: {link.url.split('#')[0]}"))
                continue

            if anchor:
                if error := validate_anchor(anchor, files[target_file].anchors, source, link):
                    errors.append(error)
    return errors

def report(errors: list[Error]) -> int:
    """Print report."""
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

def main() -> int:
    files, intra_errors = collect_files()  # D1: per-file (parallel)
    print(f"Checking {len(files)} markdown files...\n")
    inter_errors = validate_inter_file_links(files)  # D2: per-link (parallel)
    return report(intra_errors + inter_errors)


if __name__ == "__main__":
    exit(main())
