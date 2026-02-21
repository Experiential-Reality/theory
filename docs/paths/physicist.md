---
status: FOUNDATIONAL
layer: reference
depends_on:
  - newcomer.md
used_by:
  - README.md
---

# Reading Path: Physicist

> Start here if you have a physics background and want to see what BLD actually predicts.

This path walks through the derivation chain in ~2 hours, from the observer correction framework through particle physics to testable predictions.

## Summary

**Physicist reading path — 7 steps through the derivation chain:**

1. Observer Corrections: the K/X framework that generates all corrections — [Step 1](#step-1-the-observer-correction-framework)
2. Fine Structure Constant: see the formula work (137.035999177) — [Step 2](#step-2-fine-structure-constant)
3. Lepton Masses: mass ratios from structural corrections — [Step 3](#step-3-lepton-masses)
4. Boson Masses: Higgs, W, Z from the same five constants — [Step 4](#step-4-boson-masses)
5. Quantum Foundations: Born rule from K=2 — [Step 5](#step-5-quantum-foundations)
6. Cross-Domain: turbulence constants from first principles — [Step 6](#step-6-cross-domain-turbulence-and-chaos)
7. Testable Predictions: what to look for at HL-LHC — [Step 7](#step-7-testable-predictions)

**Quick formula reference**: [Digest](../mathematics/digest.md) — all predictions on one page.

| Constant | Value | Derived From |
|----------|-------|--------------|
| K | 2 | Killing form (bidirectional observation) |
| n | 4 | sl(2,C) subset sl(2,O) reference fixing |
| L | 20 | n^2(n^2-1)/12 (Riemann tensor) |
| B | 56 | 2 x dim(Spin(8)) (triality closure) |
| S | 13 | (B-n)/n |

---

## Step 1: The Observer Correction Framework

**Read**: [Observer Corrections](../mathematics/cosmology/observer-correction.md)

**Key takeaway**: Every measurement has a traversal cost K/X, where K=2 (Killing form) and X depends on what structure the probe crosses. This single framework generates all corrections across EM, weak, strong, and gravity. The same five integers (K, n, L, B, S) appear everywhere.

**Why this first**: The K/X framework is the engine. Without it, the predictions look like numerology. With it, they're a systematic correction algebra.

---

## Step 2: Fine Structure Constant

**Read**: [Fine Structure Consistency](../mathematics/particle-physics/fine-structure-consistency.md)

**Key takeaway**: alpha^-1 = n*L + B + 1 + K/B + spatial - accumulated = 137.035999177. The integer 137 is a mode count (80 geometry + 56 boundary + 1 observer). The decimals are observation costs from the K/X framework. Zero free parameters.

**The derivation chain**: [E7 Derivation](../mathematics/particle-physics/e7-derivation.md) shows B=56 is derived from triality + Killing form, not fitted to alpha.

---

## Step 3: Lepton Masses

**Read**: [Lepton Masses](../mathematics/particle-physics/lepton-masses.md)

**Key takeaway**: The muon/electron ratio (206.768) and tau/muon ratio (16.817) follow from generation hierarchy with K/X corrections. Same five constants, same correction algebra.

---

## Step 4: Boson Masses

**Read**: [Boson Masses](../mathematics/particle-physics/boson-masses.md)

**Key takeaway**: Higgs (125.20 GeV), Z (91.187 GeV), W (80.373 GeV) all from the structural framework. The reference scale v is derived as a fixed point, not fitted.

**See also**: [Reference Scale Derivation](../mathematics/cosmology/reference-scale-derivation.md) for how v emerges.

---

## Step 5: Quantum Foundations

**Read**: [Born Rule](../mathematics/quantum/born-rule.md)

**Key takeaway**: P = |psi|^2 is not a postulate — it follows from K=2 (bidirectional observation). The "squaring" IS the forward x backward round trip. The selection mechanism uses Dirichlet-Gamma decomposition.

**See also**: [Selection Rule](../mathematics/quantum/selection-rule.md) for the single-event mechanism.

---

## Step 6: Cross-Domain (Turbulence and Chaos)

**Read**: [Von Karman Derivation](../mathematics/classical/von-karman-derivation.md), then [Feigenbaum Derivation](../mathematics/classical/feigenbaum-derivation.md)

**Key takeaway**: The same BLD framework derives turbulence constants (kappa = 0.384, Re_c = 2300) and chaos constants (delta = 4.6692, alpha_F = 2.5029) from first principles. These are first derivations — previously 100+ years empirical (von Karman), 45+ years numerical only (Feigenbaum).

**See also**: [Reynolds Derivation](../mathematics/classical/reynolds-derivation.md), [She-Leveque Derivation](../mathematics/classical/she-leveque-derivation.md).

---

## Step 7: Testable Predictions

**Read**: [Higgs Self-Coupling](../mathematics/particle-physics/higgs-self-coupling.md)

**Key takeaway**: BLD predicts kappa_lambda = 41/40 = 1.025, testable at HL-LHC (~2030). Also: [Muon g-2](../mathematics/particle-physics/muon-g2.md) (Delta a_mu = 250 x 10^-11), [Neutron Lifetime](../mathematics/particle-physics/neutron-lifetime.md) (beam-bottle discrepancy = K/S^2).

---

## What's Next?

After this path, you can:

- **Go deeper into foundations**: [Mathematician Path](./mathematician.md) — formal proofs, category theory
- **See the Lean formalization**: [lean/](../../lean/) — 63 files, 0 sorry, 0 axioms
- **Understand the method**: [Discovery Method](../meta/discovery-method.md) — the three questions
- **Check the accounting**: [Proof Status](../meta/proof-status.md) — what is proven vs. conjectured

---

## See Also

- [Digest](../mathematics/digest.md) — All formulas on one page
- [Observer Corrections](../mathematics/cosmology/observer-correction.md) — The unified K/X framework
- [Newcomer Path](./newcomer.md) — For the conceptual overview
- [Glossary](../glossary.md) — Term definitions
