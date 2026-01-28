"""Shared pytest fixtures."""

import pathlib
import pytest


@pytest.fixture
def fixtures_dir() -> pathlib.Path:
    return pathlib.Path(__file__).parent / "fixtures"


@pytest.fixture
def all_link_types_md(fixtures_dir: pathlib.Path) -> pathlib.Path:
    return fixtures_dir / "all_link_types.md"
