---
status: EXPLORATORY
layer: application
depends_on:
  - ../../mathematics/derived/thermodynamics.md
  - ../../mathematics/lie-theory/lie-correspondence.md
  - ../../theory/structural-language.md
  - ../../meta/epistemic-honesty.md
used_by:
  - ../../theory/structural-language.md
  - ../../theory/README.md
  - thermodynamics-validation.md
  - ../../mathematics/derived/thermodynamics.md
---

# Protein Folding as Structural Alignment

> **Status**: Exploratory (no validation tests yet)

> **Epistemic Note**: This document provides a BLD **framework** for understanding protein folding, but contains no validated predictions. The claims are consistent with known protein physics but do not derive new results. Specific predictions (folding rate scaling, chaperone effects) need experimental validation. See [Epistemic Honesty](../../meta/epistemic-honesty.md).

## Summary

**Protein Folding as BLD Alignment:**

1. Folding = structural alignment between sequence and physics — [The Claim](#the-claim)
2. Sequence B: disorder regions, conformational switches; Physics B: hydrophobic interface, Ramachandran — [Algorithm](#the-algorithm-prp-sequence-structure) / [Traverser](#the-traverser-physics)
3. Sequence L: backbone, disulfides, H-bond potential; Physics L: collapse pathways, nucleation — [Algorithm](#the-algorithm-prp-sequence-structure) / [Traverser](#the-traverser-physics)
4. Sequence D: residues, repeats; Physics D: 3D space, phi/psi angles — [Algorithm](#the-algorithm-prp-sequence-structure) / [Traverser](#the-traverser-physics)
5. Folding is fast (Levinthal resolved) — alignment is LOCAL, gradient descent not search — [Why Folding is Fast](#why-folding-is-fast-levinthal-resolved)
6. Prions: template provides better traverser than physics alone — [Template Conversion](#the-template-conversion-process)
7. α-helix: angular compensation, 3.6 residues per turn closes at 2π — [Lie Theory](#the-lie-theory-connection)

| Component | BLD | Description |
|-----------|-----|-------------|
| Ramachandran boundaries | B | Allowed phi/psi regions — topological |
| H-bond/hydrophobic contacts | L | Coupling between residues — geometric |
| Residue count (chain length) | D | Repetition — determines folding complexity |

## The Claim

Protein folding is not a search problem. It's structural alignment between:
- **Algorithm**: The amino acid sequence (what wants to fold)
- **Traverser**: Physics (how folding happens)

Cost = free energy. Alignment = stability. The native state is the alignment minimum.

---

## Case Study: Prion Protein (PrP)

Why this is hard:
- Same sequence → two stable structures (PrPᶜ native, PrPˢᶜ pathogenic)
- PrPˢᶜ can template-convert PrPᶜ (structural contagion)
- The "wrong" fold is thermodynamically competitive

This breaks naive funnel models. There are TWO funnels.

---

## The Algorithm: PrP Sequence Structure

```
Structure(
    name="PrP_sequence",

    dimensions=[
        # The chain itself - 208 residues (human PrP)
        Dimension("residues", extent=208, properties=["sequential"]),

        # Repeated octapeptide region (residues 51-91) - copper binding
        Dimension("octarepeat", extent=4, properties=["homogeneous"]),

        # Hydrophobic core candidates (multiple possible)
        Dimension("hydrophobic_clusters", extent="variable", properties=["parallel"]),
    ],

    boundaries=[
        # Signal peptide (cleaved) - residues 1-22
        Boundary("signal", partitions=["pre:1-22", "mature:23-208"],
                 discriminator="cleavage"),

        # Unstructured N-terminus vs structured C-terminus
        Boundary("disorder", partitions=["disordered:23-124", "structured:125-228"],
                 discriminator="sequence_complexity"),

        # The critical region: can be helix OR sheet
        Boundary("conformational_switch", partitions=["helix_competent", "sheet_competent"],
                 discriminator="local_sequence_context"),

        # GPI anchor attachment - tethers to membrane
        Boundary("membrane_anchor", partitions=["soluble:23-230", "anchor:231-253"],
                 discriminator="GPI_signal"),
    ],

    links=[
        # Backbone connectivity (covalent, rigid)
        Link("backbone", from_="residue_i", to="residue_i+1",
             count=207, ops=0, deps=207, pattern="sequential"),

        # Disulfide bond (Cys179-Cys214) - locks structure
        Link("disulfide", from_="Cys179", to="Cys214",
             count=1, ops=0, deps=1, pattern="constraint"),

        # Hydrogen bond POTENTIAL - not actual bonds yet
        # These are the "offers" the sequence makes to physics
        Link("hbond_donor", from_="backbone_NH", to="?",
             count=208, ops=0, deps=0, pattern="broadcast"),
        Link("hbond_acceptor", from_="?", to="backbone_CO",
             count=208, ops=0, deps=0, pattern="reduce"),

        # Hydrophobic residues - want to cluster
        Link("hydrophobic_contact", from_="hydrophobic_residue", to="hydrophobic_residue",
             count=45, ops=0, deps=0, pattern="scatter"),  # Initially scattered

        # Charge pairs - salt bridges possible
        Link("charge_pair", from_="positive_residue", to="negative_residue",
             count=12, ops=0, deps=0, pattern="scatter"),
    ],

    barriers=0,  # No barriers in the sequence itself
)
```

---

## The Traverser: Physics

```
Traverser(
    name="aqueous_physics",

    dimensions=[
        # 3D space
        TraverserDimension("x", extent="continuous", properties=["parallel"]),
        TraverserDimension("y", extent="continuous", properties=["parallel"]),
        TraverserDimension("z", extent="continuous", properties=["parallel"]),

        # Backbone angles (phi, psi per residue)
        # Each angle is periodic: extent = 360° = 2π radians
        # This is SO(2) structure — π appears as the closure constant
        TraverserDimension("phi", extent=360, properties=["periodic"]),  # 360° = 2π
        TraverserDimension("psi", extent=360, properties=["periodic"]),  # 360° = 2π

        # Time / thermal fluctuations
        TraverserDimension("thermal", extent="continuous", properties=["stochastic"]),
    ],

    boundaries=[
        # CRITICAL: Hydrophobic effect boundary
        # This is the main driving force of folding
        TraverserBoundary("hydrophobic_interface",
                         temporal_scope="parallel",  # Acts on all residues simultaneously
                         partitions=["exposed_to_water", "buried"],
                         conflict_factor=4.0),  # High cost for exposed hydrophobics

        # Steric exclusion - atoms can't overlap
        TraverserBoundary("steric",
                         temporal_scope="parallel",
                         partitions=["allowed", "forbidden"],
                         conflict_factor=1000.0),  # Essentially infinite

        # Ramachandran allowed regions (phi/psi constraints)
        TraverserBoundary("ramachandran",
                         temporal_scope="parallel",
                         partitions=["alpha_helix", "beta_sheet", "coil", "forbidden"],
                         conflict_factor=10.0),

        # Hydrogen bond geometry requirements
        TraverserBoundary("hbond_geometry",
                         temporal_scope="parallel",
                         partitions=["satisfied", "unsatisfied"],
                         conflict_factor=2.0),  # ~2-5 kcal/mol per unsatisfied
    ],

    links=[
        # Hydrophobic collapse - scatter→coalesced transition
        TraverserLink("hydrophobic_collapse",
                     from_="scattered_hydrophobics", to="coalesced_core",
                     pattern="coalesced",
                     ns_per_access=1e6),  # Microseconds - this is slow

        # Hydrogen bond formation
        TraverserLink("hbond_formation",
                     from_="donor", to="acceptor",
                     pattern="matched",  # Must find geometric match
                     ns_per_access=1e3),  # Nanoseconds - fast when aligned

        # Local structure formation (helix nucleation)
        TraverserLink("helix_nucleation",
                     from_="coil", to="helix",
                     pattern="sequential",  # Propagates along chain
                     ns_per_access=1e4),

        # Sheet formation (requires non-local contacts)
        TraverserLink("sheet_formation",
                     from_="strand_i", to="strand_j",
                     pattern="scatter",  # Non-local = scattered
                     ns_per_access=1e7),  # Slower - requires search
    ],
)
```

---

## Alignment Analysis: Why PrPᶜ Forms (Native State)

### Link Alignment

| Sequence Link | Physics Link | Alignment |
|---------------|--------------|-----------|
| `hydrophobic_contact` (scatter) | `hydrophobic_collapse` (coalesced) | **MISALIGNED** → drives folding |
| `hbond_donor/acceptor` (broadcast/reduce) | `hbond_formation` (matched) | **PARTIAL** → satisfied in secondary structure |
| `backbone` (sequential, deps=207) | `helix_nucleation` (sequential) | **ALIGNED** → helix forms easily |
| `disulfide` (constraint) | steric boundary | **ALIGNED** → locks C-terminal structure |

### Boundary Alignment

| Sequence Boundary | Physics Boundary | Alignment |
|-------------------|------------------|-----------|
| `disorder` (disordered/structured) | `ramachandran` (helix/sheet/coil) | **PARTIAL** → N-terminus stays disordered |
| `conformational_switch` | `ramachandran` | **BISTABLE** → can align to helix OR sheet |

### The Native State (PrPᶜ)

```
Alignment(
    # Hydrophobics: scattered → coalesced (ALIGNED after folding)
    hydrophobic_alignment=ALIGNED,  # Core formed, cost minimized

    # H-bonds: satisfied in 3 alpha helices
    hbond_alignment=ALIGNED,  # ~60% satisfied

    # Ramachandran: residues 144-154, 173-194, 200-228 in helix region
    secondary_structure_alignment=ALIGNED,

    # The conformational_switch boundary aligned to "helix_competent"
    switch_state="helix",

    total_cost=LOW,  # This is a stable minimum
)
```

---

## Alignment Analysis: Why PrPˢᶜ Forms (Pathogenic State)

The SAME sequence, different alignment:

### The Key Misalignment That Enables Conversion

The `conformational_switch` boundary can align to EITHER `alpha_helix` or `beta_sheet` regions of Ramachandran space.

```
# In PrPᶜ:
conformational_switch.alignment = "helix_competent" → ramachandran.alpha_helix
# Alignment score: 0.85

# In PrPˢᶜ:
conformational_switch.alignment = "sheet_competent" → ramachandran.beta_sheet
# Alignment score: 0.82
```

Both are LOCAL MINIMA. The physics traverser has two stable alignment configurations.

### Why PrPˢᶜ is Competitive

| Property | PrPᶜ (helix) | PrPˢᶜ (sheet) |
|----------|---------------|----------------|
| Intramolecular H-bonds | More | Fewer |
| Intermolecular H-bonds | None | Many (aggregation) |
| Hydrophobic burial | Good | Better (in aggregate) |
| Entropy cost | Lower | Higher (ordered aggregate) |
| **Net stability** | Stable alone | Stable in aggregate |

The sheet alignment is WORSE for a single molecule but BETTER when you add:

```
Dimension("aggregation", extent=N, properties=["parallel", "templating"])
```

PrPˢᶜ creates a NEW DIMENSION that doesn't exist for PrPᶜ.

---

## The Template Conversion Process

This is where it gets interesting. PrPˢᶜ acts as a SECOND TRAVERSER.

```
Traverser(
    name="PrPSc_template",

    boundaries=[
        # The existing aggregate presents a structural template
        TraverserBoundary("template_interface",
                         temporal_scope="sequential",  # One molecule at a time
                         partitions=["unbound", "docked", "converted"],
                         conflict_factor=0.5),  # FAVORABLE - negative cost
    ],

    links=[
        # Template provides pre-formed H-bond partners
        TraverserLink("template_hbond",
                     from_="PrPC_donor", to="template_acceptor",
                     pattern="coalesced",  # Pre-organized!
                     ns_per_access=1e2),  # Fast - no search needed

        # Template guides conformational switch
        TraverserLink("template_switch",
                     from_="helix_competent", to="sheet_competent",
                     pattern="sequential",
                     ns_per_access=1e9),  # Slow but DIRECTED
    ],
)
```

### The Conversion as Re-Alignment

Native PrPᶜ is aligned to `aqueous_physics`.

When PrPˢᶜ template is present, there are now TWO traversers:

```
total_cost = align(PrPC, aqueous_physics) + align(PrPC, PrPSc_template)
```

The template traverser provides:
1. **Pre-organized H-bond acceptors** → scatter pattern becomes coalesced
2. **Conformational bias** → lowers barrier to sheet state
3. **Aggregation dimension** → new dimension with favorable alignment

The native state becomes a LOCAL minimum. The aggregate state becomes GLOBAL minimum.

---

## Why Folding is Fast (Levinthal Resolved)

In this model, speed comes from LOCALITY OF ALIGNMENT:

1. **Hydrophobic misalignment is local**: Each exposed hydrophobic residue feels immediate cost
2. **H-bond satisfaction is local**: Each unsatisfied donor/acceptor feels immediate cost
3. **Ramachandran is local**: Each residue's phi/psi is independently evaluated

The protein doesn't search 10^300 conformations because:
- 10^299 of them have LOCAL misalignments
- Local misalignment = local gradient signal
- Gradient descent, not random search

```python
def folding_step(structure, physics):
    for residue in structure.dimensions["residues"]:
        local_alignment = compute_local_alignment(residue, physics)
        if local_alignment.status == MISALIGNED:
            # Move down gradient
            residue.conformation = local_alignment.gradient_direction
    return structure
```

---

## Predictions from This Model

### 1. Mutations that break folding
Mutations that change the alignment landscape:
```
# Pathogenic mutation example
Link("hydrophobic_contact", ..., pattern="scatter")
# If mutation makes this unsatisfiable, no stable core forms
```

### 2. Chaperone function
Chaperones are ADDITIONAL TRAVERSER BOUNDARIES:
```
TraverserBoundary("chaperone_cage",
                 partitions=["inside", "outside"],
                 conflict_factor=0.1)  # Reduces cost of being unfolded
```
They flatten the landscape, preventing kinetic traps.

### 3. Intrinsically disordered proteins
IDPs have sequences where:
```
alignment_score(sequence, physics) ≈ alignment_score(sequence_shuffled, physics)
```
No strong alignment preference → no stable fold → functional disorder.

### 4. Temperature dependence
Temperature modifies the traverser:
```
TraverserDimension("thermal", extent=kT, properties=["stochastic"])
```
Higher T = larger thermal dimension = more states accessible = entropy dominates = unfolding.

### 5. Why prions are infectious
The PrPˢᶜ template IS STRUCTURE. When structure meets structure:
```
align(PrPC, PrPSc_template) < align(PrPC, aqueous_alone)
```
The template provides better alignment than water alone. Conversion is thermodynamically favored.

---

## The Manifold View

Each point on the manifold is a conformation (specific phi/psi values for all residues).

The metric at each point is the Hessian of the alignment cost:
```
g_ij = ∂²cost/∂φ_i∂ψ_j
```

Native states are MINIMA (zero gradient, positive curvature).

Transition states are SADDLE POINTS (zero gradient, mixed curvature).

Prion conversion crosses a saddle between two minima:
```
PrPᶜ minimum  →  transition saddle  →  PrPˢᶜ minimum
                        ↑
            Template lowers this saddle
```

The template doesn't change the minima. It changes the METRIC between them.

---

## The Lie Theory Connection

The physics traverser IS a Lie group—specifically the direct product of:
- **SO(3)**: Rotations in 3D space
- **R³**: Translations
- **SO(2)ⁿ**: Backbone dihedral angles (each periodic with period 2π)

The SO(2)ⁿ factor is where π enters protein structure: each residue has two dihedral angles (φ, ψ) that wrap around with period 2π. The Ramachandran plot partitions this 2π × 2π torus into allowed and forbidden regions—boundaries on a periodic dimension.

### The α-Helix: Angular Closure with Linear Extension

The α-helix is a **cylindrical helix** — a geometric structure demonstrating angular compensation (π mechanism) with linear growth along its axis.

**Parametric form** (cylindrical helix):
```
x(n) = r × cos(θn)
y(n) = r × sin(θn)
z(n) = a × n         ← LINEAR rise, not exponential
```

**In complex notation** (for xy-plane projection):
```
xy(n) = r × e^(iθn)   ← Angular: rotation via e^(iθ)
z(n) = a × n          ← Linear: NOT e^(an)

where:
  r = helix radius ≈ 2.3 Å
  a = rise per residue = 1.5 Å
  θ = rotation per residue = 100° = 2π/3.6 radians
  n = residue number
```

**Measured parameters** (validated by crystallography):

| Parameter | Value | BLD Interpretation |
|-----------|-------|-------------------|
| Residues per turn | 3.6 | D = 3.6 for angular closure |
| Rise per residue | 1.5 Å | LINEAR growth along axis |
| Rotation per residue | 100° | θ = angular increment |
| Pitch (rise per turn) | 5.4 Å | a × D = 1.5 × 3.6 |

**The angular closure**:
- After 3.6 residues: e^(i × 100° × 3.6) = e^(i × 360°) = e^(i2π) = 1 (angular closure)
- The helix closes rotationally (π mechanism) while extending linearly along its axis

**What this proves**: The α-helix demonstrates the **angular (π) mechanism** for rotation, achieving closure at 2π. The axial extension is **linear**, not exponential. This is a cylindrical helix, not a logarithmic spiral.

**Implication for BLD completeness**: The α-helix shows angular compensation clearly, but does NOT prove both mechanisms "coexist" in a single structure — the rise is simply linear, not exponentially compensated.

**Why α-helices are stable**: The (φ, ψ) ≈ (−60°, −45°) backbone angles are the Ramachandran-allowed region that satisfies:
1. Hydrogen bonding: i → i+4 pattern (Link satisfaction)
2. Steric avoidance: No atom overlap (Boundary satisfaction)
3. Rotational closure: 3.6 residues per turn (Angular compensation)

The helix minimizes alignment cost by simultaneously satisfying all three BLD constraints through the spiral geometry.

The sequence structure specifies what transformations preserve its properties. The physics traverser specifies what transformations are physically realizable.

**Folding is alignment = Lie homomorphism.**

A perfect fold would be a structure-preserving map from the sequence's symmetries to the physics' symmetries. The native state is where the homomorphism obstruction is minimized.

| Concept | Lie Theory | Protein Folding |
|---------|------------|-----------------|
| Structure | Lie algebra | Sequence constraints |
| Traverser | Lie group | Physical transformations |
| Alignment | Homomorphism | Folding pathway |
| Cost | Obstruction | Free energy |
| Minimum | Image of homomorphism | Native state |

The template conversion in prions is a change of Lie group—the aggregate provides additional symmetries (translation along the fibril axis) that the monomer physics lacks.

See [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) and [Constructive Lie](../../mathematics/lie-theory/constructive-lie.md) for the mathematical foundation.

---

## Conclusion

Protein folding in three primitives:

| Primitive | Sequence (Algorithm) | Physics (Traverser) |
|-----------|---------------------|---------------------|
| **Boundary** | Disorder regions, conformational switches, anchor sites | Hydrophobic interface, steric exclusion, Ramachandran regions |
| **Link** | Backbone, disulfides, H-bond potential, hydrophobic contacts | Collapse pathways, H-bond formation, nucleation |
| **Dimension** | Residue count, repeats, hydrophobic clusters | 3D space, phi/psi angles, thermal fluctuations |

Folding = alignment descent.
Native state = alignment minimum.
Misfolding = alternative minimum.
Prion conversion = template provides better traverser.

Same DSL. Same geometry. Same cost function.

---

## Validation Needs

This exploratory analysis requires the following tests before upgrading to validated:

| Prediction | Test | Status |
|------------|------|--------|
| Folding rate scales with chain length (D×L) | Compare folding times for proteins of different lengths | NOT TESTED |
| Chaperones act as L compensation | Measure folding with/without chaperones | NOT TESTED |
| Prion template provides lower-cost traverser | Compare energy landscapes | NOT TESTED |
| Dihedral angles cluster at Ramachandran B regions | Statistical analysis of PDB | CONSISTENT (known result) |

**Proposed validation repo**: `bld-protein-test`

### What Would Falsify This Framework

1. Folding rate NOT correlated with D×L structure
2. Chaperones work through mechanism unrelated to L compensation
3. Prion conversion doesn't involve template-assisted alignment
4. Energy landscape topology doesn't match B/L/D predictions

---

## See Also

- [Glossary](../../glossary.md) — Central definitions
- [Thermodynamics](../../mathematics/derived/thermodynamics.md) — Free energy on the manifold
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — Physics as Lie group
- [Structural Language](../../theory/structural-language.md) — B/L/D specification
- [Validation Roadmap](validation-roadmap.md) — Status of all physics claims
- [Epistemic Honesty](../../meta/epistemic-honesty.md) — Standards for claims
