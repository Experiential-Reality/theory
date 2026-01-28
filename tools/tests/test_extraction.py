"""Tests for link and header extraction."""

from tools.check_links import (
    extract_links,
    extract_headers,
    header_to_anchor,
    LinkKind,
)


class TestHeaderToAnchor:
    def test_simple_text(self):
        assert header_to_anchor("Hello World") == "hello-world"

    def test_with_special_chars(self):
        assert header_to_anchor("Hello & World!") == "hello--world"

    def test_with_unicode(self):
        assert header_to_anchor("Fine Structure Constant") == "fine-structure-constant"

    def test_unicode_superscript(self):
        assert header_to_anchor("3.1 Fine Structure Constant") == "31-fine-structure-constant"

    def test_strips_trailing_dashes(self):
        assert header_to_anchor("Hello World!") == "hello-world"

    def test_code_in_header(self):
        assert header_to_anchor("The `foo` Method") == "the-foo-method"

    def test_bold_in_header(self):
        assert header_to_anchor("The **Important** Part") == "the-important-part"

    def test_link_in_header(self):
        assert header_to_anchor("See [here](url) for more") == "see-here-for-more"


class TestExtractHeaders:
    def test_single_header(self):
        assert "hello-world" in extract_headers("# Hello World")

    def test_multiple_levels(self):
        anchors = extract_headers("# Level 1\n## Level 2\n### Level 3\n")
        assert {"level-1", "level-2", "level-3"} <= anchors

    def test_header_with_content(self):
        anchors = extract_headers("# Introduction\n\nText.\n\n## Methods\n")
        assert anchors == {"introduction", "methods"}


class TestExtractLinks:
    def test_inline_link(self):
        links = extract_links("[link text](./file.md)")
        assert len(links) == 1
        assert links[0].kind == LinkKind.INLINE
        assert links[0].text == "link text"
        assert links[0].url == "./file.md"

    def test_link_with_anchor(self):
        links = extract_links("[section](./file.md#section-one)")
        assert links[0].url == "./file.md#section-one"

    def test_internal_anchor_only(self):
        links = extract_links("[jump](#section)")
        assert links[0].url == "#section"

    def test_skips_external_links(self):
        assert extract_links("[Google](https://google.com)") == []

    def test_skips_image_suffixes(self):
        assert extract_links("[logo](./image.png)") == []

    def test_skips_code_blocks(self):
        content = "Text\n\n```python\n[ignored](./ignored.md)\n```\n\n[found](./found.md)"
        links = extract_links(content)
        assert len(links) == 1
        assert links[0].url == "./found.md"

    def test_multiple_links(self):
        assert len(extract_links("[one](./a.md) and [two](./b.md)")) == 2

    def test_line_numbers(self):
        links = extract_links("Line 1\n[link](./file.md)\nLine 3\n")
        assert links[0].line == 2


class TestExtractReferenceLinks:
    def test_reference_link_resolved(self):
        links = extract_links("[link text][ref1]\n\n[ref1]: ./file.md\n")
        ref_links = [l for l in links if l.kind == LinkKind.REFERENCE]
        assert len(ref_links) == 1
        assert ref_links[0].text == "link text"
        assert ref_links[0].url == "./file.md"
        assert ref_links[0].ref == "ref1"

    def test_undefined_ref_detected(self):
        links = extract_links("[text][undefined]")
        undefined = [l for l in links if l.kind == LinkKind.UNDEFINED_REF]
        assert len(undefined) == 1
        assert undefined[0].ref == "undefined"

    def test_reference_in_code_block_ignored(self):
        assert extract_links("```\n[ignored][ref]\n```\n[ref]: ./file.md\n") == []

    def test_case_insensitive_ref_lookup(self):
        links = extract_links("[text][REF]\n\n[ref]: ./file.md\n")
        ref_links = [l for l in links if l.kind == LinkKind.REFERENCE]
        assert ref_links[0].url == "./file.md"

    def test_reference_link_format_for_error(self):
        links = extract_links("[text][ref]\n\n[ref]: ./file.md\n")
        ref_link = next(l for l in links if l.kind == LinkKind.REFERENCE)
        formatted = ref_link.format_for_error()
        assert "[text][ref]" in formatted and "./file.md" in formatted

    def test_undefined_ref_format_for_error(self):
        links = extract_links("[text][undefined]")
        undefined = next(l for l in links if l.kind == LinkKind.UNDEFINED_REF)
        assert "[undefined]" in undefined.format_for_error()
