"""Integration tests for link checker."""

import pathlib

import pytest

from tools.check_links import check, process_file

pytestmark = pytest.mark.project


class TestProcessFile:
    def test_extracts_anchors_and_links(self, all_link_types_md: pathlib.Path):
        content = all_link_types_md.read_text()
        file_data, errors = process_file(str(all_link_types_md), content)

        # Should extract headers as anchors
        assert "valid-links" in file_data.anchors
        assert "section-one" in file_data.anchors

        # Should extract inter-file links
        urls = {link.url for link in file_data.inter_file_links}
        assert "./other.md" in urls
        assert "./nonexistent.md" in urls

    def test_validates_intra_file_anchors(self, all_link_types_md: pathlib.Path):
        content = all_link_types_md.read_text()
        file_data, errors = process_file(str(all_link_types_md), content)

        # Self anchor #valid-links should be valid (no error)
        error_anchors = [e.link for e in errors if e.link.startswith("#")]
        assert "#valid-links" not in error_anchors


class TestCheck:
    @pytest.mark.asyncio
    async def test_finds_all_fixture_files(self, fixtures_dir: pathlib.Path):
        file_count, errors = await check(fixtures_dir)
        assert file_count == 2

    @pytest.mark.asyncio
    async def test_detects_broken_links(self, fixtures_dir: pathlib.Path):
        file_count, errors = await check(fixtures_dir)
        all_errors = list(errors)

        # Should find broken inline link
        error_urls = {e.link for e in all_errors}
        assert "./nonexistent.md" in error_urls

        # Should find bad anchor
        bad_anchor_errors = [e for e in all_errors if "no-such-anchor" in e.link]
        assert len(bad_anchor_errors) > 0

    @pytest.mark.asyncio
    async def test_valid_links_no_errors(self, fixtures_dir: pathlib.Path):
        file_count, errors = await check(fixtures_dir)
        all_errors = list(errors)

        # Valid links should not appear in errors
        error_urls = {e.link for e in all_errors}
        assert "./other.md#section-one" not in error_urls
