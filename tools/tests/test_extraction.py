"""Tests for link and header extraction."""

import pytest

from tools.check_links import (
    build_content_index,
    extract_all_links,
    extract_headers,
    header_to_anchor,
    LinkKind,
)


class TestHeaderToAnchor:
    """Tests for GitHub-compatible anchor generation."""

    def test_simple_text(self):
        assert header_to_anchor("Hello World") == "hello-world"

    def test_with_special_chars(self):
        assert header_to_anchor("Hello & World!") == "hello--world"

    def test_with_unicode(self):
        assert header_to_anchor("Fine Structure Constant") == "fine-structure-constant"

    def test_unicode_superscript(self):
        result = header_to_anchor("3.1 Fine Structure Constant")
        assert result == "31-fine-structure-constant"

    def test_strips_trailing_dashes(self):
        assert header_to_anchor("Hello World!") == "hello-world"

    def test_code_in_header(self):
        assert header_to_anchor("The `foo` Method") == "the-foo-method"

    def test_bold_in_header(self):
        assert header_to_anchor("The **Important** Part") == "the-important-part"

    def test_link_in_header(self):
        assert header_to_anchor("See [here](url) for more") == "see-here-for-more"


class TestExtractHeaders:
    """Tests for header extraction."""

    def test_single_header(self):
        content = "# Hello World"
        anchors = extract_headers(content)
        assert "hello-world" in anchors

    def test_multiple_levels(self):
        content = """# Level 1
## Level 2
### Level 3
"""
        anchors = extract_headers(content)
        assert "level-1" in anchors
        assert "level-2" in anchors
        assert "level-3" in anchors

    def test_header_with_content(self):
        content = """# Introduction

Some text here.

## Methods

More text.
"""
        anchors = extract_headers(content)
        assert len(anchors) == 2
        assert "introduction" in anchors
        assert "methods" in anchors


class TestExtractLinks:
    """Tests for inline link extraction."""

    def test_inline_link(self):
        content = "[link text](./file.md)"
        idx = build_content_index(content)
        links = extract_all_links(idx)
        assert len(links) == 1
        assert links[0].kind == LinkKind.INLINE
        assert links[0].text == "link text"
        assert links[0].url == "./file.md"

    def test_link_with_anchor(self):
        content = "[section](./file.md#section-one)"
        idx = build_content_index(content)
        links = extract_all_links(idx)
        assert len(links) == 1
        assert links[0].url == "./file.md#section-one"

    def test_internal_anchor_only(self):
        content = "[jump](#section)"
        idx = build_content_index(content)
        links = extract_all_links(idx)
        assert len(links) == 1
        assert links[0].url == "#section"

    def test_skips_external_links(self):
        content = "[Google](https://google.com)"
        idx = build_content_index(content)
        links = extract_all_links(idx)
        assert len(links) == 0

    def test_skips_image_suffixes(self):
        content = "[logo](./image.png)"
        idx = build_content_index(content)
        links = extract_all_links(idx)
        assert len(links) == 0

    def test_skips_code_blocks(self):
        content = """Normal text

```python
[this is ignored](./ignored.md)
```

[this is found](./found.md)
"""
        idx = build_content_index(content)
        links = extract_all_links(idx)
        assert len(links) == 1
        assert links[0].url == "./found.md"

    def test_multiple_links(self):
        content = "[one](./a.md) and [two](./b.md)"
        idx = build_content_index(content)
        links = extract_all_links(idx)
        assert len(links) == 2

    def test_line_numbers(self):
        content = """Line 1
[link](./file.md)
Line 3
"""
        idx = build_content_index(content)
        links = extract_all_links(idx)
        assert links[0].line == 2


class TestExtractReferenceLinks:
    """Tests for reference-style link extraction."""

    def test_reference_link_resolved(self):
        content = """[link text][ref1]

[ref1]: ./file.md
"""
        idx = build_content_index(content)
        links = extract_all_links(idx)

        ref_links = [l for l in links if l.kind == LinkKind.REFERENCE]
        assert len(ref_links) == 1
        assert ref_links[0].text == "link text"
        assert ref_links[0].url == "./file.md"
        assert ref_links[0].ref == "ref1"

    def test_undefined_ref_detected(self):
        content = "[text][undefined]"
        idx = build_content_index(content)
        links = extract_all_links(idx)

        undefined = [l for l in links if l.kind == LinkKind.UNDEFINED_REF]
        assert len(undefined) == 1
        assert undefined[0].ref == "undefined"

    def test_reference_in_code_block_ignored(self):
        content = """```
[ignored][ref]
```
[ref]: ./file.md
"""
        idx = build_content_index(content)
        links = extract_all_links(idx)
        # Should not find any links (the only reference is in code block)
        assert len(links) == 0

    def test_case_insensitive_ref_lookup(self):
        content = """[text][REF]

[ref]: ./file.md
"""
        idx = build_content_index(content)
        links = extract_all_links(idx)

        ref_links = [l for l in links if l.kind == LinkKind.REFERENCE]
        assert len(ref_links) == 1
        assert ref_links[0].url == "./file.md"

    def test_reference_link_format_for_error(self):
        content = """[text][ref]

[ref]: ./file.md
"""
        idx = build_content_index(content)
        links = extract_all_links(idx)

        ref_link = next(l for l in links if l.kind == LinkKind.REFERENCE)
        formatted = ref_link.format_for_error()
        assert "[text][ref]" in formatted
        assert "./file.md" in formatted

    def test_undefined_ref_format_for_error(self):
        content = "[text][undefined]"
        idx = build_content_index(content)
        links = extract_all_links(idx)

        undefined = next(l for l in links if l.kind == LinkKind.UNDEFINED_REF)
        formatted = undefined.format_for_error()
        assert "[undefined]" in formatted
