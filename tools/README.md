# BLD Theory Verification Tools

Computational verification of BLD theory predictions against experimental measurements. 144 tests across 17 files.

## Source modules

| Module | Role |
|--------|------|
| `bld.py` | Constants, measured values, prediction formulas, shared types — single source of truth |
| `quantum.py` | Selection rule: pointer sets, MC sampling, statistical tests |
| `check_links.py` | Markdown cross-reference link checker |

## bld.py

**Constants**: B=56, L=20, n=4, K=2, S=13, LAMBDA, V_EW, TAU_BOTTLE

**Tolerances**: SIGMA_THRESHOLD, FLOAT_EPSILON, IDENTITY_TOLERANCE, CONVERGENCE_RATIO, TRANSCENDENTAL_UNIQUENESS, IMPROVEMENT_THRESHOLD, FEIGENBAUM_DELTA_TOL, FEIGENBAUM_ALPHA_TOL

**Enums**: CorrectionTerm (6 K/X decomposition terms), CorrectionSign (traversal completeness)

**Types**: Measurement, Prediction (auto-computes sigma), TestResult

**Formulas**: alpha_inv, higgs_mass, planck_mass, mu_over_e, mp_over_me, tau_over_mu, sin2_theta_12/13/23, muon_g2, tau_beam, sin2_theta_w, z_mass, w_mass, alpha_s_inv, kappa_em/hadronic/w_coupling/lambda_coupling, bld_composites, reynolds_pipe/flat_plate/sphere/jet, feigenbaum_delta/alpha, she_leveque_zeta, haar_random_state(s)

## quantum.py

**Types**: PointerKind, PointerSet, OutcomeResult, StatTest

**Core**: selection_rule, run_selection_mc, chi2_test, overlaps, overlaps_batch, make_orthogonal_pointers, make_nonorthogonal_pointers_m2/m3, p_nonorthogonal

**Alternative rules**: rule_product, rule_max_overlap, rule_cdf_partition, rule_born_sample, selection_rule_tau

## Test coverage

| Domain | File | # | Verifies |
|--------|------|---|----------|
| Algebraic | test_algebra | 7 | Octonions, G2, SU(3), D4 triality, spacetime dim |
| Fine structure | test_predictions | 11 | α⁻¹, leptons, nucleon, mixing, g-2, lifetimes, masses |
| Electroweak | test_electroweak | 8 | sin²θ_W, Z/W, α_s, Higgs κ, consistency |
| K/X corrections | test_kx_corrections | 8 | Decomposition, convergence, signs, patterns |
| Structure | test_structure | 7 | 137 modes, L·D collapse, rigidity, uniqueness |
| Classical | test_classical | 8 | Reynolds, Kolmogorov, Feigenbaum, She-Leveque |
| Selection rule | test_selection_rule | 4 | Born recovery, product rule, overlap dist, independence |
| Controlled observer | test_controlled_observer | 6 | Determinism, bias, regime transition, finite-N |
| Math verification | test_math_verification | 12 | Edge cases, analytical proofs, symmetry |
| Physical measurement | test_physical_measurement | 1 | Non-orthogonal MC vs analytical (192 configs) |
| Collapse | test_collapse | 10 | No-cloning, no-communication, Trotter, irreversibility |
| Entanglement | test_entanglement | 7 | Bell/GHZ/W, concurrence, K uniqueness |
| Phase transition | test_phase_transition | 6 | Scaling, Binder crossing, 3D Ising |
| Quantum infra | test_quantum | 8 | Haar states, overlaps, chi2, pointers |
| Link checker | test_extraction/validation/integration | 31 | Link extraction, anchor validation, resolution |
