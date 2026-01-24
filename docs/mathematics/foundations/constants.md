---
status: DERIVED
layer: 0
depends_on:
  - ../particle-physics/e7-derivation.md
  - ../lie-theory/lie-correspondence.md
  - ../lie-theory/killing-form.md
  - derivations/octonion-derivation.md
used_by:
  - definitions/bld-calculus.md
  - derivations/force-structure.md
  - derivations/energy-derivation.md
  - machine/universal-machine.md
  - machine/integer-machine.md
  - machine/detection-structure.md
  - definitions/ubit.md
---

# BLD Constants

**Status**: DERIVED — All constants derived from BLD axioms and genesis closure.

This file is the **authoritative source** for BLD numerical constants. Other files reference this rather than redefining.

---

## Quick Summary (D≈7 Human Traversal)

**The 5 core constants:**

1. **B = 56** — Boundary modes (from triality + Killing form)
2. **L = 20** — Riemann tensor components (geometric structure)
3. **n = 4** — Spacetime dimensions (from octonion reference fixing)
4. **K = 2** — Killing form (bidirectional observation cost)
5. **S = 13** — Structural intervals ((B-n)/n = 52/4)

**One formula**: α⁻¹ = n×L + B + 1 = 80 + 56 + 1 = 137

---

## The Constants

| Symbol | Value | Meaning | Derived From |
|--------|-------|---------|--------------|
| **B** | 56 | Boundary modes | 2 × dim(Spin(8)) = 2 × 28. See [E7 Derivation](../particle-physics/e7-derivation.md) |
| **L** | 20 | Riemann components | n²(n²-1)/12 = 16×15/12. See [Lie Correspondence](../lie-theory/lie-correspondence.md) |
| **n** | 4 | Spacetime dimensions | sl(2,ℂ) ⊂ sl(2,𝕆) from reference fixing. See [Octonion Derivation](derivations/octonion-derivation.md) |
| **K** | 2 | Killing form | Bidirectional observation (forward + back). See [Killing Form](../lie-theory/killing-form.md) |
| **S** | 13 | Structural intervals | (B - n)/n = (56 - 4)/4 = 13 |

---

## Derived Combinations

| Expression | Value | Appears In |
|------------|-------|------------|
| n × L | 80 | Geometric structure (fine structure base) |
| n × L + B | 136 | Structure without traverser |
| n × L + B + 1 | 137 | Full structure (α⁻¹ integer part) |
| n² × S | 208 | Generational structure (μ/e base) |
| K / B | 2/56 ≈ 0.036 | Boundary quantum (observer correction) |
| K / (n × L) | 2/80 = 0.025 | Geometric correction |
| n × L × B | 4480 | Full structure product |

---

## The Derivation Chain

```
Nothing is self-contradictory (logical necessity)
    ↓
B must exist (primordial distinction)
    ↓
traverse(-B, B) must CLOSE (self-consistency)
    ↓
Closure requires triality (stable 3-fold self-reference)
    ↓
Triality unique to Spin(8) → dim(so(8)) = 28
    ↓
K = 2 (Killing form, bidirectional)
    ↓
B = K × 28 = 56
    ↓
Octonions required → sl(2,𝕆) → sl(2,ℂ) → n = 4
    ↓
L = n²(n²-1)/12 = 20 (Riemann tensor)
    ↓
S = (B - n)/n = 13
```

---

## Usage in Other Files

When using these constants, include:

```markdown
## Constants
B=56, L=20, n=4, K=2, S=13. See [constants.md](constants.md) for derivations.
```

This preserves local context while avoiding redundant full definitions.

---

## References

- [E7 Derivation](../particle-physics/e7-derivation.md) — B = 56 from triality
- [Lie Correspondence](../lie-theory/lie-correspondence.md) — L = 20 from Riemann tensor
- [Octonion Derivation](derivations/octonion-derivation.md) — n = 4 from reference fixing
- [Killing Form](../lie-theory/killing-form.md) — K = 2 from bidirectional observation
- [Octonion Necessity](derivations/octonion-necessity.md) — Why these values are required (genesis closure)
