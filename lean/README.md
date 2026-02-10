# BLD Theory: Lean 4 Formalization

**24 files. 3430 lines. 0 sorry. 0 admit. 1 axiom.**

The BLD calculus formalized in [Lean 4](https://lean-lang.org/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/). Three structural primitives (Boundary, Link, Dimension) derive physical constants and predict experimental quantities.

```bash
cd lean && lake build    # 2027 jobs, 0 errors, 0 warnings
```

---

## What is machine-verified?

Every theorem is checked by the Lean kernel. The `norm_num` tactic performs exact rational arithmetic: `(K^2 : Q) / S = 4/13` is verified by computing `2^2 / 13 = 4/13`. No floating-point, no rounding.

- **`sorry`** (accept without proof): 0
- **`axiom`** (assume without proof): 1 — a well-known theorem not yet in Mathlib (see [Axiom Inventory](#axiom-inventory))

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
Exceptional.lean         Octonion.lean
  E7 Cartan matrix       Concrete 8-dim algebra
  det=2, simply-laced    normSq multiplicative
       |                      |
       v                      v
                         Octonions.lean
                    ---> B=56 selects O
                         Division algebra tower
       |                      |
       v                      v
Completeness.lean        Observer.lean
  so8 <-> BLD            K/X corrections
  correspondence         alpha^-1 decomposition
       |
       v
Predictions.lean         GeneticCode.lean
  12 exact rational        Same 5 constants
  predictions              predict genetic code
                                |
Normalization.lean              v
  Strong normalization     7 biology quantities
  (Tait's method)          (bases, codons, amino acids)
```

---

## Predictions

Each row is a Lean `theorem` proved by `norm_num` (exact rational arithmetic).

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

11 testable predictions fall within 1.4 sigma of measurement. The 12th (kappa\_lambda = 1.025, Higgs self-coupling) is testable at the HL-LHC (~2040).

All predictions derive from 5 constants: B=56, L=20, n=4, K=2, S=13 — themselves derived from K=2 (observation cost).

### Cross-Domain: Genetic Code

The same 5 constants determine the genetic code. Each theorem proved by `decide` (exact Nat arithmetic).

| Quantity | BLD Formula | Value | Observed |
|----------|-------------|-------|----------|
| Nucleotide bases | n | 4 | A, U/T, G, C |
| Base pairs | K | 2 | A-U, G-C |
| Codon length | n-1 | 3 | Triplet code |
| Total codons | n^3 | 64 | Complete codon table |
| Amino acids | n(n+1) = L | 20 | Standard amino acid set |
| Coding codons | L(n-1)+1 | 61 | 64 minus 3 stop codons |
| Degeneracy modulus | n(n-1) | 12 | All observed degeneracies {1,2,3,4,6} divide 12 |

L = 20 appears in three independent domains: Riemann tensor components (physics), amino acid count (biology), and BLD link count (Lie algebra structure constants).

---

## Axiom Inventory

| Axiom | File | Statement | Status |
|-------|------|-----------|--------|
| `cartan_classification_complete` | Lie/Completeness.lean | Every semisimple Lie algebra has a Cartan matrix | Cartan ~1894; Mathlib has Serre construction (forward) but not exhaustiveness |

The Hurwitz theorem (only 4 normed division algebras) was previously an axiom but is now replaced by a concrete octonion construction in `Octonion.lean` with `normSq` multiplicativity proved via Degen's eight-square identity.

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
| Semantics.lean | 272 | Progress, Preservation (free), Determinism, Type Safety, 5 canonical forms |
| MultiStep.lean | 177 | Multi-step reduction, normal forms, value uniqueness |
| Normalization.lean | 470 | Strong normalization via Tait's logical relations |
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
| Lie/Classical.lean | 165 | so(8) defined, finrank = 28 (explicit 28-element basis) |
| Lie/Exceptional.lean | 84 | E7 via Serre construction, det=2, simply-laced (from Mathlib) |
| Lie/Killing.lean | 65 | K=2 from Killing form, K^2 = n |
| Lie/Completeness.lean | 82 | so8 correspondence, Cartan classification axiom |

### Layer 4: Physics and Biology
| File | Lines | Content |
|------|-------|---------|
| Octonion.lean | 283 | Concrete 8-dim algebra, NonAssocRing, StarRing, normSq multiplicative |
| Octonions.lean | 197 | Division algebra selection, B=56 uniquely selects octonions |
| Predictions.lean | 150 | 12 exact rational predictions (neutrino mixing, weak angle, couplings, Reynolds) |
| Observer.lean | 136 | K/X correction principle, alpha^-1 correction decomposition |
| GeneticCode.lean | 73 | 7 genetic code quantities from BLD constants |

---

## Key Theorems

```
so8_finrank : Module.finrank Q (so8 Q) = 28
  -- Explicit basis of 28 skew-symmetric matrices, proved from scratch

normSq_mul : normSq (a * b) = normSq a * normSq b
  -- Octonion norm is multiplicative (via Degen's eight-square identity)

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

normalization : forall (e : Term [] a), exists v, Steps e v /\ Value v
  -- Every well-typed closed term reduces to a value (Tait's method)

genetic_code_complete :
    n = 4 /\ K = 2 /\ n-1 = 3 /\ n^3 = 64 /\
    n*(n+1) = L /\ L*(n-1)+1 = 61 /\ n*(n-1) = 12
  -- All 7 genetic code quantities from BLD constants
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
