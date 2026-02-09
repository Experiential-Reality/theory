# BLD Theory: Lean 4 Formalization

**21 files. 2612 lines. 0 sorry. 0 admit. 2 axioms. Every proof machine-checked.**

The BLD calculus — a theory deriving physical constants from three structural primitives — formalized in [Lean 4](https://lean-lang.org/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

```bash
cd lean && lake build    # 2023 jobs, 0 errors, 0 warnings
```

---

## What is machine-verified?

Lean is a proof assistant. Unlike a paper proof that a reader must trust, every theorem here is checked by the Lean kernel — a small, trusted program that verifies each logical step. The `norm_num` tactic performs exact rational arithmetic: when we write `(K^2 : Q) / S = 4/13`, the kernel computes `2^2 / 13 = 4/13` and confirms it. There is no floating-point approximation, no rounding, no room for error.

**`sorry`** is Lean's escape hatch — it accepts any claim without proof. We have zero.

**`axiom`** declares an assumption without proof. We have exactly two, both well-known open formalization problems in Mathlib (see [Axiom Inventory](#axiom-inventory)).

---

## Derivation Chain

The core proof spine, from axioms to physics:

```
Axioms A1-A7          Type system (Ty)         Irreducibility
  Axioms.lean    --->   Basic.lean        --->   Irreducibility.lean
                        Term.lean                Sublanguage.lean
                        Subst.lean               SubIrred.lean
                                                      |
                                                      v
Constants               Operational semantics    Cardinality
  Constants.lean  <---   Semantics.lean           Cardinality.lean
  K=2 uniqueness         Progress                 ModeCount.lean
  alpha_inv=137          Preservation
       |                 Determinism
       v                 Type Safety
Lie theory                    |
  Classical.lean              v
  so8_finrank=28         Eval.lean
  (explicit basis)       (computable evaluation)
       |
       v
Exceptional.lean         Octonions.lean
  E7 Cartan matrix  ---> B=56 selects O
  det=2, simply-laced    Division algebra tower
       |                      |
       v                      v
Completeness.lean        Observer.lean
  so8 <-> BLD            K/X corrections
  correspondence         alpha^-1 decomposition
       |
       v
Predictions.lean
  12 exact rational predictions
```

---

## Machine-Verified Predictions

Every prediction below is a Lean `theorem` proved by `norm_num` — exact rational arithmetic, kernel-checked.

| Quantity | BLD Formula | Exact Fraction | Decimal | Observed | Sigma |
|----------|-------------|----------------|---------|----------|-------|
| sin^2 theta\_12 | K^2/S | 4/13 | 0.30769 | 0.307 +/- 0.012 | 0.06 |
| sin^2 theta\_13 | n^2/(n-1)^6 | 16/729 | 0.02195 | 0.02195 +/- 0.00058 | 0.00 |
| sin^2 theta\_23 | (S+1)/(L+n+1) | 14/25 | 0.56000 | 0.561 +/- 0.015 | 0.07 |
| sin^2 theta\_W | 3/S + K/(nLB) | 6733/29120 | 0.23122 | 0.23121 +/- 0.00004 | 0.14 |
| m\_p/m\_e | (S+n)(B+nS)+K/S | 23870/13 | 1836.154 | 1836.153 +/- 0.001 | 1.38 |
| tau\_beam/tau\_bottle | 1+K/S^2 | 171/169 | 1.01183 | 1.01173 +/- 0.003 | 0.04 |
| kappa\_gamma | 1+K/B | 29/28 | 1.03571 | 1.05 +/- 0.09 | 0.16 |
| kappa\_W | 1+K/(B+L) | 39/38 | 1.02632 | 1.04 +/- 0.08 | 0.17 |
| kappa\_b | 1+K/(n+L) | 13/12 | 1.08333 | 0.98 +/- 0.13 | 0.79 |
| **kappa\_lambda** | **1+K/(nL)** | **41/40** | **1.025** | **testable ~2040** | **HL-LHC** |
| alpha\_s^-1 | 137/n^2 - K/(n+L) | 407/48 | 8.47917 | 8.482 +/- 0.07 | 0.04 |
| Re\_pipe | nLB/K * (X+1)/X | 85120/37 | 2300.5 | 2300 +/- 1 | 0.54 |

**All 11 testable predictions fall within 1.4 sigma of measurement.**

The 12th (kappa\_lambda = 1.025, Higgs self-coupling) is a novel prediction testable at the HL-LHC around 2040.

All predictions derive from 5 constants: **B=56, L=20, n=4, K=2, S=13** — which are themselves derived from a single input: **K=2** (observation cost).

---

## Axiom Inventory

Only 2 axioms in the entire formalization:

| Axiom | File | Why |
|-------|------|-----|
| `hurwitz_theorem` | Octonions.lean | Only R, C, H, O are normed division algebras. Mathlib does not define octonions. |
| `cartan_classification_complete` | Lie/Completeness.lean | Every semisimple Lie algebra has a Cartan matrix. Mathlib has the Serre construction (forward direction) but not exhaustiveness. |

Both are well-established mathematical theorems (Hurwitz 1898, Cartan ~1894). They are axioms here only because Mathlib's formalization hasn't reached them yet.

---

## File Map

### Layer 0: Type System
| File | Lines | Content |
|------|-------|---------|
| Basic.lean | 25 | `Ty` inductive: unit, sum (B), fn (L), prod (D) |
| Term.lean | 77 | Intrinsically-typed terms, de Bruijn indices |
| Subst.lean | 102 | Substitution, renaming, weakening |

### Layer 1: Metatheory
| File | Lines | Content |
|------|-------|---------|
| Semantics.lean | 274 | Progress, Preservation, Determinism, Type Safety, 5 canonical forms |
| MultiStep.lean | 177 | Multi-step reduction, normal forms, value uniqueness |
| Eval.lean | 172 | Computable small-step evaluator, 6 verified examples |
| Sublanguage.lean | 180 | IsBD, IsBL, IsLD predicates, intersection = unit |
| Irreducibility.lean | 108 | B, L, D mutually irreducible (main structural theorem) |
| SubIrred.lean | 131 | Sublanguage safety: BD = data, BL = no tuples |
| Cardinality.lean | 114 | Cardinality function, positivity, sum >= 2 |
| ModeCount.lean | 88 | Mode count, alpha^-1 = 137 at type level |

### Layer 2: Constants and Axioms
| File | Lines | Content |
|------|-------|---------|
| Constants.lean | 100 | B=56, L=20, n=4, K=2, S=13, identity chain, K=2 uniqueness |
| Axioms.lean | 130 | Seven axioms (A1-A7) connected to Ty inductive |

### Layer 3: Lie Theory Bridge
| File | Lines | Content |
|------|-------|---------|
| Lie/Basic.lean | 49 | BLDDecomposition, BLDCorrespondence structures |
| Lie/Classical.lean | 165 | so(8) defined, **finrank = 28 proved** (explicit 28-element basis) |
| Lie/Exceptional.lean | 84 | E7 via Serre construction, det=2, simply-laced (from Mathlib) |
| Lie/Killing.lean | 65 | K=2 from Killing form, K^2 = n |
| Lie/Completeness.lean | 82 | so8 correspondence, Cartan classification axiom |

### Layer 4: Physics
| File | Lines | Content |
|------|-------|---------|
| Predictions.lean | 150 | 12 exact rational predictions (neutrino mixing, weak angle, couplings, Reynolds) |
| Observer.lean | 136 | K/X correction principle, alpha^-1 correction decomposition |
| Octonions.lean | 203 | Division algebra selection, B=56 uniquely selects octonions |

---

## Key Theorems

```
so8_finrank : Module.finrank Q (so8 Q) = 28
  -- Explicit basis of 28 skew-symmetric matrices, proved from scratch

only_octonion_gives_B56 : boundary_count_for a = BLD.B -> a = .octonion
  -- B=56 uniquely selects octonions among all 4 normed division algebras

K2_unique : 1 <= k -> k <= 5 -> alpha_from_K k = 137 -> k = 2
  -- K=2 is the only value giving alpha^-1 = 137

irreducibility :
    (forall t, IsLD t -> not (TypeEncoding (.sum .unit .unit) t)) /\
    (forall t, IsLD t -> t.cardinality = 1)
  -- B cannot be expressed in the LD fragment

progress : forall (e : Term [] a), Value e \/ exists e', Step e e'
  -- No closed term is stuck

type_safety : forall (e : Term [] a), Value e \/ exists e', Step e e' /\ ...
  -- Well-typed programs don't go wrong
```

---

## Building

Requires [Lean 4](https://lean-lang.org/) (v4.28.0-rc1) and internet access (to fetch Mathlib).

```bash
lake build          # Full build (~5 min first time, cached after)
lake build BLD      # Build everything
lake env printPaths # Verify Mathlib is resolved
```

---

## License

Lean formalization: MIT License. Documentation: CC BY 4.0.
