"""Shared pytest fixtures."""

import os

# Must precede numpy import: prevents BLAS thread oversubscription with xdist workers.
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")

import pathlib

import numpy as np
import pytest

import tools.bld


@pytest.fixture(scope="session")
def so8() -> tools.bld.SO8:
    """Session-scoped: builds SO8 algebra state once for entire test suite."""
    return tools.bld.build_so8()


@pytest.fixture
def fixtures_dir() -> pathlib.Path:
    return pathlib.Path(__file__).parent / "fixtures"


@pytest.fixture
def all_link_types_md(fixtures_dir: pathlib.Path) -> pathlib.Path:
    return fixtures_dir / "all_link_types.md"


@pytest.fixture
def rng() -> np.random.Generator:
    return np.random.default_rng(42)
