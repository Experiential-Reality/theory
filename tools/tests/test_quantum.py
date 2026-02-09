"""Unit tests for quantum infrastructure."""

import numpy as np

import tools.bld
import tools.quantum


def test_haar_random_state_normalized(rng: np.random.Generator) -> None:
    for dim in [2, 8, 32]:
        state = tools.bld.haar_random_state(dim, rng)
        assert abs(np.linalg.norm(state) - 1.0) < 1e-12


def test_haar_random_state_dimension(rng: np.random.Generator) -> None:
    for dim in [2, 8, 32]:
        state = tools.bld.haar_random_state(dim, rng)
        assert state.shape == (dim,)
        assert np.iscomplexobj(state)


def test_overlaps_orthogonal_sum(rng: np.random.Generator) -> None:
    M = 4
    pointers = tools.quantum.make_orthogonal_pointers(M, M, rng)
    O = tools.bld.haar_random_state(M, rng)
    ovlps = tools.quantum.overlaps(pointers.states, O)
    assert abs(ovlps.sum() - 1.0) < 1e-10


def test_selection_rule_picks_dominant(rng: np.random.Generator) -> None:
    a = np.array([0.9, 0.1])
    ovlp = np.array([0.5, 0.5])
    assert tools.quantum.selection_rule(a, ovlp) == 0

    ovlp2 = np.array([0.01, 0.99])
    assert tools.quantum.selection_rule(a, ovlp2) == 0


def test_chi2_test_uniform(rng: np.random.Generator) -> None:
    n = 10000
    counts = np.array([2500.0, 2500.0, 2500.0, 2500.0])
    expected = np.array([0.25, 0.25, 0.25, 0.25])
    result = tools.quantum.chi2_test(counts, expected, n)
    assert result.passes
    assert result.chi2_stat == 0.0
    assert result.p_value == 1.0


def test_chi2_test_biased_fails() -> None:
    n = 10000
    counts = np.array([9000.0, 500.0, 300.0, 200.0])
    expected = np.array([0.25, 0.25, 0.25, 0.25])
    result = tools.quantum.chi2_test(counts, expected, n)
    assert not result.passes


def test_make_orthogonal_pointers_orthogonality(rng: np.random.Generator) -> None:
    M = 4
    N_obs = 8
    pointers = tools.quantum.make_orthogonal_pointers(M, N_obs, rng)
    assert len(pointers.states) == M
    assert pointers.kind == tools.quantum.PointerKind.ORTHOGONAL

    for i in range(M):
        for j in range(i + 1, M):
            inner = np.abs(np.vdot(pointers.states[i], pointers.states[j]))
            assert inner < 1e-10


def test_stat_test_fields() -> None:
    st = tools.quantum.StatTest(chi2_stat=5.0, p_value=0.03, passes=True)
    assert st.chi2_stat == 5.0
    assert st.p_value == 0.03
    assert st.passes is True
