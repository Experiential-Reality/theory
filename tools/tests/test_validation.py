"""Tests for link validation logic."""

import pathlib

import tools.check_links


class TestValidateAnchor:
    def test_valid_anchor(self):
        anchors = frozenset({"section-one", "section-two"})
        link = tools.check_links.Link(kind=tools.check_links.LinkKind.INLINE, text="test", url="#section-one", line=1)
        error = tools.check_links.validate_anchor("section-one", anchors, pathlib.Path("test.md"), link)
        assert error is None

    def test_missing_anchor(self):
        anchors = frozenset({"section-one"})
        link = tools.check_links.Link(kind=tools.check_links.LinkKind.INLINE, text="test", url="#missing", line=1)
        error = tools.check_links.validate_anchor("missing", anchors, pathlib.Path("test.md"), link)
        assert error is not None
        assert "not found" in error.message

    def test_similar_anchor_hint(self):
        anchors = frozenset({"section-one", "section-two"})
        link = tools.check_links.Link(kind=tools.check_links.LinkKind.INLINE, text="test", url="#sectionone", line=1)
        error = tools.check_links.validate_anchor("sectionone", anchors, pathlib.Path("test.md"), link)
        assert error is not None
        assert "Similar" in error.message


class TestFindSimilar:
    def test_finds_similar_by_removing_dashes(self):
        anchors = frozenset({"section-one", "other-section"})
        similar = tools.check_links.find_similar("sectionone", anchors)
        assert "section-one" in similar

    def test_finds_substring_match(self):
        anchors = frozenset({"the-compensation-principle", "other"})
        similar = tools.check_links.find_similar("compensation-principle", anchors)
        assert "the-compensation-principle" in similar

    def test_limits_results(self):
        anchors = frozenset({f"section-{i}" for i in range(10)})
        similar = tools.check_links.find_similar("section", anchors, limit=3)
        assert len(similar) <= 3


class TestResolveTarget:
    def test_relative_path(self):
        link = tools.check_links.Link(kind=tools.check_links.LinkKind.INLINE, text="test", url="./other.md", line=1)
        source = pathlib.Path("/docs/folder/file.md")
        target, anchor = tools.check_links.resolve_target(link, source, pathlib.Path("/docs"))
        assert target == pathlib.Path("/docs/folder/other.md")
        assert anchor is None

    def test_relative_path_with_anchor(self):
        link = tools.check_links.Link(kind=tools.check_links.LinkKind.INLINE, text="test", url="./other.md#section", line=1)
        source = pathlib.Path("/docs/folder/file.md")
        target, anchor = tools.check_links.resolve_target(link, source, pathlib.Path("/docs"))
        assert target == pathlib.Path("/docs/folder/other.md")
        assert anchor == "section"

    def test_parent_directory(self):
        link = tools.check_links.Link(kind=tools.check_links.LinkKind.INLINE, text="test", url="../other.md", line=1)
        source = pathlib.Path("/docs/folder/file.md")
        target, anchor = tools.check_links.resolve_target(link, source, pathlib.Path("/docs"))
        assert target == pathlib.Path("/docs/other.md")

    def test_absolute_path(self):
        link = tools.check_links.Link(kind=tools.check_links.LinkKind.INLINE, text="test", url="/root/file.md", line=1)
        source = pathlib.Path("/docs/folder/file.md")
        target, anchor = tools.check_links.resolve_target(link, source, pathlib.Path("/docs"))
        assert target == pathlib.Path("/docs/root/file.md")

    def test_reference_link_resolution(self):
        """Reference links resolve the same way as inline links."""
        link = tools.check_links.Link(kind=tools.check_links.LinkKind.REFERENCE, text="test", url="./other.md", line=1, ref="ref1")
        source = pathlib.Path("/docs/folder/file.md")
        target, anchor = tools.check_links.resolve_target(link, source, pathlib.Path("/docs"))
        assert target == pathlib.Path("/docs/folder/other.md")
