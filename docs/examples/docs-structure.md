---
status: FOUNDATIONAL
layer: 1
depends_on:
  - ../theory/structural-language.md
  - ../meta/discovery-method.md
  - ../glossary.md
used_by:
  - ../theory/structural-interest.md
  - ../glossary.md
---

# BLD Structure of This Documentation

## Quick Summary (D≈7 Human Traversal)

**Documentation structure in BLD in 7 steps:**

1. **B₁ (epistemic status)** — Partitions all docs: PROVEN | DERIVED | HYPOTHESIZED
2. **B₂ (audience)** — Partitions reading paths: newcomer | mathematician | practitioner
3. **L (glossary hub)** — Central node with ~50 inbound links from all sections
4. **L (depends_on)** — Each file declares what it builds upon
5. **D (file repetition)** — Same YAML template repeats across all .md files
6. **D (layer hierarchy)** — Layer 0 → 1 → 2 → application progression
7. **Self-application** — BLD applied to BLD docs demonstrates the framework

| Doc Component | BLD |
|---------------|-----|
| Status tags | B (partitions) |
| Cross-refs | L (links) |
| File array | D (repetition) |

---

> **Status**: Foundational

> **Note**: This document demonstrates BLD by applying it to itself.

This documentation is itself a structure. Here is its BLD analysis.

---

## The Complete Drawing

```
┌──────────────────────────────────────────────────────────────────────────────────┐
│                                                                                  │
│                         BLD DOCUMENTATION STRUCTURE                              │
│                                                                                  │
│  ════════════════════════════════════════════════════════════════════════════   │
│                                                                                  │
│                              BOUNDARIES (B)                                      │
│                                                                                  │
│   B₁: Epistemic Status (partitions ALL documents)                                │
│   ┌───────────────┐    ┌───────────────┐    ┌───────────────┐                   │
│   │    PROVEN     │    │    DERIVED    │    │  HYPOTHESIZED  │                   │
│   │               │    │               │    │               │                   │
│   │  foundations  │    │   particle    │    │    ideas      │                   │
│   │  lie-theory   │    │   cosmology   │    │  conjectures  │                   │
│   │               │    │   quantum     │    │               │                   │
│   └───────────────┘    └───────────────┘    └───────────────┘                   │
│                                                                                  │
│   B₂: Audience (partitions reading PATHS)                                        │
│   ┌───────────────┐    ┌───────────────┐    ┌───────────────┐                   │
│   │   NEWCOMER    │    │ MATHEMATICIAN │    │ PRACTITIONER  │                   │
│   │               │    │               │    │               │                   │
│   │   ~30 min     │    │   ~2 hours    │    │   ~1 hour     │                   │
│   │   concepts    │    │    proofs     │    │   methods     │                   │
│   └───────────────┘    └───────────────┘    └───────────────┘                   │
│                                                                                  │
│  ════════════════════════════════════════════════════════════════════════════   │
│                                                                                  │
│                                LINKS (L)                                         │
│                                                                                  │
│                            ┌──────────────┐                                      │
│                            │   GLOSSARY   │ ←── Central hub (L_max)              │
│                            │  ~50 inbound │     All sections connect here        │
│                            └──────┬───────┘                                      │
│                                   │                                              │
│          ┌────────────────────────┼────────────────────────┐                     │
│          │                        │                        │                     │
│          ▼                        ▼                        ▼                     │
│   ┌────────────┐           ┌────────────┐           ┌────────────┐              │
│   │   THEORY   │──────────▶│    MATH    │──────────▶│    APPS    │              │
│   │            │           │            │           │            │              │
│   │  concepts  │           │   proofs   │           │  validate  │              │
│   └────────────┘           └────────────┘           └────────────┘              │
│          │                        │                        │                     │
│          │                        ▼                        │                     │
│          │                 ┌────────────┐                  │                     │
│          └────────────────▶│  EXAMPLES  │◀─────────────────┘                     │
│                            │            │                                        │
│                            │  concrete  │                                        │
│                            └────────────┘                                        │
│                                                                                  │
│  ════════════════════════════════════════════════════════════════════════════   │
│                                                                                  │
│                              DIMENSIONS (D)                                      │
│                                                                                  │
│   D₀: Repository (extent = 1)                                                    │
│   └── D₁: Sections (extent = 7)                                                  │
│       ├── theory/           (8 docs)                                             │
│       ├── mathematics/                                                           │
│       │   └── D₂: Subgroups (extent = 6)                                         │
│       │       ├── foundations/      (6 docs)                                     │
│       │       ├── lie-theory/       (5 docs)                                     │
│       │       ├── derived/          (6 docs)                                     │
│       │       ├── quantum/          (8 docs)                                     │
│       │       ├── cosmology/        (6 docs)                                     │
│       │       └── particle-physics/ (6 docs)                                     │
│       ├── applications/                                                          │
│       │   └── D₃: Subgroups (extent = 3)                                         │
│       │       ├── code/             (7 docs)                                     │
│       │       ├── ml/               (4 docs)                                     │
│       │       └── physics/          (15 docs)                                    │
│       ├── examples/         (8 docs)                                             │
│       ├── meta/             (5 docs)                                             │
│       ├── analysis/         (2 docs)                                             │
│       └── paths/            (3 docs)                                             │
│                                                                                  │
│   Effective D at any navigation level: ≤ 7  ✓ (7±2 compliant)                    │
│                                                                                  │
└──────────────────────────────────────────────────────────────────────────────────┘
```

---

## Quantitative Summary

```
Total Documents: ~94

By Section:
┌─────────────────────┬───────┐
│ Section             │ Count │
├─────────────────────┼───────┤
│ theory/             │   8   │
│ mathematics/        │  41   │
│   foundations/      │   6   │
│   lie-theory/       │   5   │
│   derived/          │   6   │
│   quantum/          │   8   │
│   cosmology/        │   6   │
│   particle-physics/ │   6   │
│   (top-level)       │   4   │
│ applications/       │  26   │
│   code/             │   7   │
│   ml/               │   4   │
│   physics/          │  15   │
│ examples/           │   8   │
│ meta/               │   5   │
│ analysis/           │   2   │
│ paths/              │   3   │
│ glossary.md         │   1   │
└─────────────────────┴───────┘

Hub Centrality:
  glossary.md           : ~50 inbound  (highest - central hub)
  lie-correspondence    : ~20 inbound  (key result)
  octonion-derivation   : ~15 inbound  (foundational derivation)
  discovery-method      : ~12 inbound  (methodology)
```

---

## Reading Paths as L Chains

Each reading path is a sequence of links guiding traversal:

```
Newcomer Path (4 steps):
┌──────────┐     ┌──────────┐     ┌──────────┐     ┌──────────┐
│  Core    │────▶│ Struct.  │────▶│Irreducib.│────▶│ Why Lie  │
│  Thesis  │     │ Language │     │  Proof   │     │  Theory  │
└──────────┘     └──────────┘     └──────────┘     └──────────┘
  theory/          theory/         math/found.      math/lie/

Mathematician Path (7 steps):
┌──────────┐     ┌──────────┐     ┌──────────┐     ┌──────────┐
│ Struct.  │────▶│Irreducib.│────▶│  Octonion│────▶│   Lie    │────▶ ...
│ Language │     │  Proof   │     │ Derivation│    │  Corresp │
└──────────┘     └──────────┘     └──────────┘     └──────────┘

Practitioner Path (5 steps):
┌──────────┐     ┌──────────┐     ┌──────────┐     ┌──────────┐
│ Discovery│────▶│ BLD-Dev  │────▶│ [Domain] │────▶│   ZIP    │────▶ Why Lie
│  Method  │     │          │     │ App File │     │ Example  │
└──────────┘     └──────────┘     └──────────┘     └──────────┘
  meta/           apps/code/       apps/*/          examples/
```

---

## Human and LLM as Traversers

Both human readers and LLMs are BLD traversers. They align with structure using the same primitives.

```
T_human = (B_human, L_human, D_human)
T_llm   = (B_llm,   L_llm,   D_llm)

Reading_Cost = align(S_doc, T) = B_mismatch + D × L_mismatch
```

### Human Traverser Constraints

| Constraint | Value | Source |
|------------|-------|--------|
| Chunk capacity | 7 ± 2 items | Miller's Law |
| Working memory | ~4 chunks | Cognitive science |
| Session limit | ~2 hours | Attention fatigue |
| Depth limit | ~4 levels | Navigation complexity |

### LLM Traverser Constraints

| Constraint | Value | Source |
|------------|-------|--------|
| Context window | ~128K tokens | Model architecture |
| Attention heads | Fixed per layer | Transformer design |
| Position encoding | Bounded | Architecture limit |

### The Parallel

Both traversers satisfy BLD principles:

| Principle | Human | LLM |
|-----------|-------|-----|
| **D×L scaling** | More docs → more navigation | More tokens → O(D²) attention |
| **B invariance** | 7±2 limit constant | Attention heads constant |
| **Compensation** | Can re-read (L) to overcome depth (B) | Can attend widely (L) to overcome context (B) |

**Key insight**: Documentation optimized for human traversers also works well for LLMs — both are BLD traversers with similar structural constraints.

---

## D×L Scaling Demonstrated

**L scales with D** (geometric property):
- ~94 documents × ~6 links/doc = ~564 total links
- Adding more docs → proportionally more links needed
- D×L product determines total navigation complexity

**B is invariant** (topological property):
- Epistemic status = 5 categories (regardless of doc count)
- Audience types = 3 paths (regardless of content volume)
- Adding 100 more docs wouldn't change B

This validates D×L scaling: link count grows with dimension, boundaries don't.

---

## Self-Reference

```
┌─────────────────────────────────────────────────────────────────┐
│                        META-STRUCTURE                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  This document: docs/examples/docs-structure.md                 │
│                                                                 │
│  Position in B: Foundational (example/specification)            │
│  Position in D: examples/ section, document #8 of 8             │
│  Position in L: Links to glossary, discovery-method, theory     │
│                                                                 │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │                                                           │ │
│  │  This analysis IS an example of BLD analysis.             │ │
│  │                                                           │ │
│  │  The document demonstrates the framework by applying      │ │
│  │  it to itself. The structure it describes includes        │ │
│  │  this document. This is not circular—it's self-consistent.│ │
│  │                                                           │ │
│  │  BLD can describe any structure, including structures     │ │
│  │  that contain BLD descriptions.                           │ │
│  │                                                           │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

---

## See Also

- [Glossary](../glossary.md) — The central L hub
- [Discovery Method](../meta/discovery-method.md) — How to find structure
- [Structural Language](../theory/structural-language.md) — B/L/D specification
- [BLD Conservation](../mathematics/bld-conservation.md) — Noether's theorem connection
