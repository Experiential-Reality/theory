"""Shared test assertion helpers."""


def assert_all_pass(results):
    """Assert all results pass, with diagnostic output on failure."""
    failed = [r for r in results if not r.passes]
    assert not failed, [
        (r.name, f"sigma={r.sigma:.2f}") if hasattr(r, "sigma")
        else (r.name, getattr(r, "value", ""))
        for r in failed
    ]


def assert_none_pass(results):
    """Assert no results pass (for wrong-constants tests)."""
    passed = [r for r in results if r.passes]
    assert not passed, [r.name for r in passed]
