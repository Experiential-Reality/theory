"""Shared pytest fixtures."""

import pathlib

import pytest


@pytest.fixture
def fixtures_dir() -> pathlib.Path:
    """Path to test fixtures directory."""
    return pathlib.Path(__file__).parent / "fixtures"


@pytest.fixture
def all_link_types_md(fixtures_dir: pathlib.Path) -> pathlib.Path:
    """Path to the comprehensive link types fixture."""
    return fixtures_dir / "all_link_types.md"


@pytest.fixture
def other_md(fixtures_dir: pathlib.Path) -> pathlib.Path:
    """Path to the other.md fixture."""
    return fixtures_dir / "other.md"
