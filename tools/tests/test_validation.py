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


class TestValidateExternalUrls:
    ORGS = frozenset({"Experiential-Reality", "rax-V", "leanprover-community"})

    def test_valid_github_org(self):
        content = "[repo](https://github.com/Experiential-Reality/theory)"
        errors = tools.check_links.validate_external_urls("test.md", content, self.ORGS)
        assert errors == []

    def test_invalid_github_org(self):
        content = "[repo](https://github.com/experiential-reality-org/bld)"
        errors = tools.check_links.validate_external_urls("test.md", content, self.ORGS)
        assert len(errors) == 1
        assert errors[0].kind == tools.check_links.ErrorKind.EXTERNAL_URL
        assert "experiential-reality-org" in errors[0].message

    def test_case_sensitive(self):
        content = "[repo](https://github.com/experiential-reality/theory)"
        errors = tools.check_links.validate_external_urls("test.md", content, self.ORGS)
        assert len(errors) == 1

    def test_non_github_skipped(self):
        content = "[site](https://example.com/some/path)"
        errors = tools.check_links.validate_external_urls("test.md", content, self.ORGS)
        assert errors == []

    def test_empty_allowlist_skips_all(self):
        content = "[repo](https://github.com/anything/repo)"
        errors = tools.check_links.validate_external_urls("test.md", content, frozenset())
        assert errors == []

    def test_code_block_ignored(self):
        content = "```\n[repo](https://github.com/bad-org/repo)\n```\n"
        errors = tools.check_links.validate_external_urls("test.md", content, self.ORGS)
        assert errors == []

    def test_multiple_orgs(self):
        content = (
            "[a](https://github.com/Experiential-Reality/theory) "
            "[b](https://github.com/rax-V/bld-circuits) "
            "[c](https://github.com/bad-org/repo)"
        )
        errors = tools.check_links.validate_external_urls("test.md", content, self.ORGS)
        assert len(errors) == 1
        assert "bad-org" in errors[0].message


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
