"""Integration tests for link checker."""

import pathlib

import pytest

from tools.check_links import (
    collect_files_async,
    collect_files_sync,
    process_content,
    validate_inter_file_links,
)


class TestProcessContent:
    """Tests for single-file processing."""

    def test_extracts_anchors_and_links(self, all_link_types_md: pathlib.Path):
        content = all_link_types_md.read_text()
        file_data, errors = process_content(all_link_types_md, content)

        # Should extract headers as anchors
        assert "valid-links" in file_data.anchors
        assert "section-one" in file_data.anchors

        # Should extract inter-file links
        urls = {link.url for link in file_data.inter_file_links}
        assert "./other.md" in urls
        assert "./nonexistent.md" in urls

    def test_validates_intra_file_anchors(self, all_link_types_md: pathlib.Path):
        content = all_link_types_md.read_text()
        file_data, errors = process_content(all_link_types_md, content)

        # Self anchor #valid-links should be valid (no error)
        error_anchors = [e.link for e in errors if e.link.startswith("#")]
        assert "#valid-links" not in error_anchors


class TestCollectFilesSync:
    """Tests for synchronous file collection."""

    def test_finds_all_fixture_files(self, fixtures_dir: pathlib.Path):
        files, errors = collect_files_sync(fixtures_dir)
        assert len(files) == 2

        filenames = {p.name for p in files.keys()}
        assert "all_link_types.md" in filenames
        assert "other.md" in filenames

    def test_detects_broken_links(self, fixtures_dir: pathlib.Path):
        files, intra_errors = collect_files_sync(fixtures_dir)
        inter_errors = validate_inter_file_links(files, fixtures_dir)
        all_errors = intra_errors + inter_errors

        # Should find broken inline link
        error_urls = {e.link for e in all_errors}
        assert "./nonexistent.md" in error_urls

        # Should find bad anchor
        bad_anchor_errors = [e for e in all_errors if "no-such-anchor" in e.link]
        assert len(bad_anchor_errors) > 0

    def test_valid_links_no_errors(self, fixtures_dir: pathlib.Path):
        files, intra_errors = collect_files_sync(fixtures_dir)
        inter_errors = validate_inter_file_links(files, fixtures_dir)
        all_errors = intra_errors + inter_errors

        # Valid links should not appear in errors
        error_urls = {e.link for e in all_errors}
        assert "./other.md#section-one" not in error_urls


class TestCollectFilesAsync:
    """Tests for asynchronous file collection."""

    @pytest.mark.asyncio
    async def test_same_results_as_sync(self, fixtures_dir: pathlib.Path):
        # Sync
        sync_files, sync_errors = collect_files_sync(fixtures_dir)

        # Async
        async_files, async_errors = await collect_files_async(fixtures_dir)

        # Same files found
        assert set(sync_files.keys()) == set(async_files.keys())

        # Same anchors extracted
        for path in sync_files:
            assert sync_files[path].anchors == async_files[path].anchors

    @pytest.mark.asyncio
    async def test_detects_same_errors(self, fixtures_dir: pathlib.Path):
        sync_files, sync_intra = collect_files_sync(fixtures_dir)
        sync_inter = validate_inter_file_links(sync_files, fixtures_dir)

        async_files, async_intra = await collect_files_async(fixtures_dir)
        async_inter = validate_inter_file_links(async_files, fixtures_dir)

        sync_error_set = {(e.file, e.link) for e in sync_intra + sync_inter}
        async_error_set = {(e.file, e.link) for e in async_intra + async_inter}

        assert sync_error_set == async_error_set
