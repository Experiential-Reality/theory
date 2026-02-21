---
status: VALIDATED
layer: application
depends_on:
  - ../../theory/structural-language.md
  - ../../theory/bld-as-language.md
  - ../../theory/human-language-structure.md
  - ../../mathematics/foundations/axioms.md
  - ../../mathematics/lie-theory/lie-correspondence.md
  - ../../mathematics/cosmology/observer-correction.md
  - ../../mathematics/foundations/proofs/completeness-proof.md
  - ../../mathematics/foundations/proofs/irreducibility-proof.md
  - ../../mathematics/foundations/definitions/bld-calculus.md
  - ../../mathematics/foundations/structural/factorization-calculus.md
  - ../../mathematics/foundations/structural/canonical-hardness.md
  - ../../mathematics/foundations/structural/compensation-principle.md
  - ../../mathematics/geometry/manifold-foundations.md
  - ../../mathematics/lie-theory/boundary-derivation.md
---

# Lossless Translation via BLD Homomorphism

> **Status**: Validated — lossless round-trip translation demonstrated across English, Japanese, and Arabic. 200+ tests passing.

## Summary

**Natural language translation is a group homomorphism in BLD, not a statistical approximation:**

1. Three function calls: `translate = write ∘ lex ∘ read` — [The Core Formula](#the-core-formula)
2. Languages differ only in calibration (φ); the universal space is shared — [Why Lossless](#why-lossless)
3. B partitions word space (POS, roles, word order); L links concepts (dependencies, synsets); D encodes features (tense, voice, number) — [B](#b-boundaries-in-translation), [L](#l-links-in-translation), [D](#d-dimensions-in-translation)
4. Joint edge disambiguation scores synsets bidirectionally on dependency structure — [L](#l-links-in-translation)
5. Translation is measurement: observer correction framework decomposes errors into structural, apparatus, and language-pair layers — [Translation as Measurement](#translation-as-measurement)
6. Current heuristics are scaffolding; the same methodology that derives α⁻¹ = 137.036 should derive translation costs from structure — [Future: Deriving Constants from Structure](#future-deriving-constants-from-structure)

| Component | BLD | In bld-translate |
|-----------|-----|------------------|
| POS tags, word order, role assignment | B (Boundary) | `bld_structure.py`, `calibration.py` |
| Dependencies, synset links, morphological rules | L (Link) | `traverser.py`, `concept_lexicon.py`, `morphology.py` |
| Morphological features (tense, voice, number...) | D (Dimension) | `dimensions.py`, `io.py`, `universal.py` |
| Per-language mapping (φ and φ⁻¹) | Calibration | `calibration.py`, `io.py` |
| Lemma substitution in universal space | lex | `concept_lexicon.py` |

---

## The Core Formula

```
Translation = φ₂ ∘ lex ∘ φ₁⁻¹
```

Where:
- **φ⁻¹ = read** : Language → Universal BLD (de-calibrate)
- **φ = write** : Universal BLD → Language (calibrate)
- **lex** = lexicon substitution in universal space

```python
def translate(tokens, source_cal, target_cal, lexicon):
    universal = read(tokens, source_cal)        # φ₁⁻¹
    translated = lexicon.translate(universal)    # lex : U → U
    target = write(translated, target_cal)       # φ₂
    return target
```

Three function calls. The traverser is IDENTICAL for all language pairs. All language-specific knowledge lives in calibration data.

This is a **homomorphism**, not a heuristic:
- The read/write pair uses the SAME calibration data in opposite directions (aux_to_feature ↔ feature_to_aux)
- Lexicon substitution preserves B (roles unchanged), L (links unchanged), D (features unchanged) — only lemmas change
- Structure is preserved: BLD(target) = BLD(source)

### The Write Algorithm: Plan-Map-Output

The write function (φ) reconstructs language-specific form from universal BLD in three phases:

1. **Plan** (B): order tokens by `word_order` permutation. Insert generated function words — determiners before nouns, particles before verbs, auxiliaries after verbs — based on D features.
2. **Map** (L): compute old_id → new_id bijection for content tokens only. Generated tokens (aux, det, part) get fresh IDs outside this bijection.
3. **Output** (D): realize each token's surface form via morphology, with head pointers remapped through the bijection.

Each phase touches exactly one primitive. The separation is not accidental — it mirrors the irreducibility of B, L, D.

---

## B: Boundaries in Translation

B partitions word space into regions. In the translator:

### POS Tags as Partitions

Every token carries a POS tag (NOUN, VERB, ADJ, ...) that partitions the space of possible meanings. The boundary between content words (translated) and function words (preserved) is the fundamental B in translation:

```
Content: {NOUN, VERB, ADJ, ADV} → translated via lexicon
Function: {AUX, DET, PART, ADP, SCONJ, CCONJ} → preserved or regenerated
```

This boundary is a gradient, not a binary. Light verbs ("take a walk"), complex predicates, and copulas sit between content and function. The partition is **per-language calibration**, not universal: English "have" is function (auxiliary), Japanese "持つ" (motsu) is content. Each language's `aux_to_feature`/`feature_to_aux` pairs declare which lemmas are functional — a per-language B decision stored in calibration data.

### Word Order as Group Action

S₅ is the symmetry group of role permutations — each language occupies one point in it. The calibration stores each language's canonical order:

```
English: (S, V, O)        "The cat ate the fish"
Japanese: (S, O, V)       "猫が魚を食べた"
Arabic: (V, S, O)         "أكل القط السمك"
```

The `permute_roles()` transform works for any permutation in S₅, but natural languages cluster in a subgroup. Not all permutations are attested at scale — no OVS-dominant language has more than ~1M speakers. Greenberg's Universal 1 (S precedes O in dominant order for ~97% of languages) constrains the actual landscape. The group action is real; the inhabited region is small.

### Zero-Copula Detection

When the root token is a NOUN or ADJ with a subject dependent, the translator detects a **zero-copula** structure and assigns the root to the V (verb) role rather than the S (subject) role. This is a B decision: where does the predicate boundary fall?

```
"The sky [is] blue" → root=blue (ADJ) has nsubj=sky → treat blue as V
```

Languages like Arabic and Russian regularly omit copulas. The translator handles this structurally, not as a special case.

### Pro-Drop

Pro-drop (omitting pronoun subjects) is an independent B flag — separate from verb agreement. Japanese drops pronouns without verb agreement marking; Spanish drops them because verb morphology carries the information. The translator treats these as orthogonal:

- **pro_drop = true**: omit pronoun subjects on write
- **verb_agreement**: propagate Number/Person features from subject to verb

Both are B decisions (what appears vs. what's elided), but they're independent calibration parameters.

### Auxiliary Absorption

Languages encode features differently. English uses auxiliary verbs ("was eaten"), Japanese uses suffixes ("食べられた"). The calibration partitions features into:
- Those expressed by function words (absorbed on read, regenerated on write)
- Those expressed by morphology (carried through in D)

Absorption is a **projection**, not deletion: auxiliary tokens disappear from the universal representation, but their features transfer to the head verb. Features are orthogonal (different names — Voice, Tense, Caus — so stacking never collides). The inverse (write) regenerates auxiliaries from the feature bundle.

---

## L: Links in Translation

L connects concepts. In the translator:

### Dependency Structure

Each token carries a head pointer and relation label, forming a dependency tree. This IS the link structure:

```python
@dataclasses.dataclass(frozen=True)
class UniversalToken:
    id: int
    lemma: str
    pos: str
    head: int        # L: what this links to
    relation: str    # L: how it links
```

Links are preserved through translation — the dependency tree passes through unchanged.

### ILI Synset Links

The `ConceptLexicon` connects equivalent concepts across languages via Interlingual Index (ILI) synsets:

```
source_lemma → [analyze] → ILI synset → [realize] → target_lemma
```

This is an L operation: linking meaning nodes across the language boundary.

### Idioms and Non-Compositional Meaning

Idioms ("kick the bucket") are opaque to lemma-by-lemma substitution. The `ConceptLexicon` handles these via `IdiomEntry` (multi-word expressions mapped to single synsets) and context disambiguation rules (dependency context → specific sense). When a concept gap exists in the target language, `handle_gap` provides a cascade of fallbacks: explicit gap strategies, spectral nearest-neighbor in whitened space, gloss decomposition via ILI components, and raw gloss. Where MWE detection fails (idiom not in lexicon), the output is grammatically correct but semantically wrong — a coverage issue to address by expanding the ConceptLexicon, not a framework limitation.

### Joint Edge Disambiguation

When a lemma maps to multiple synsets (polysemy), the traverser disambiguates using **structural context**, not statistical co-occurrence.

The algorithm distinguishes two cases by relation type — an asymmetric B partition within the L structure:

- **Argument relations** (nsubj, obj, iobj, obl): both the dependent AND head synsets are jointly optimized. This locks both ends of the dependency edge simultaneously.
- **Modifier relations** (amod, advmod, nmod): only the dependent synset is selected; the head is taken as given context.

The cost function for both:

```
Cost = ½ log(1 + d²_Mahal)
```

where d²_Mahal is the Mahalanobis distance between synset feature vectors in whitened space. The whitening is canonical — Cholesky factorization of the covariance of all synset spectral embeddings, pre-computed at load time. This makes the metric the **canonical distance on the semantic manifold**, not an ad-hoc similarity score.

For unknown synsets (not in the spectral embedding), the system interpolates from hypernym/hyponym graph neighbors. If no neighbors exist, it falls back to the neutral vector (mean of all embeddings) — graph smoothing that keeps the representation continuous.

The traverser processes in **post-order** (leaves before heads), accumulating whitened context vectors bottom-up. When disambiguating a head, its dependents' spectral vectors are already resolved. This is D structure: depth of processing mirrors depth of the dependency tree.

---

## D: Dimensions in Translation

D captures what repeats. In the translator:

### Morphological Features as Product of Finite Groups

Each token carries a feature bundle — a point in a product of finite groups:

```
{Tense: Past, Voice: Pass, Number: Sing, Person: 3}
∈ Tense × Voice × Number × Person
```

These features are drawn from a universal inventory (UD defines the full space), but each language selects a subset. English marks definiteness; Japanese doesn't. Turkish marks evidentiality; English doesn't. When the source has features the target lacks, information is lost — quantifiable via K/X at the feature scale. The feature bundle passes through translation unchanged; the surface realization and feature coverage are language-specific.

### Feature Agreement Propagation

Agreement rules propagate features across linked tokens. In English, subject-verb agreement copies Number from subject to verb:

```
"The cats eat" → Number=Plur propagates from nsubj to head
```

Agreement rules are per-language calibration, not universal logic.

### Required Features with Defaults

When the source language doesn't encode a feature the target requires, defaults fill the gap:

```
Japanese lacks articles → English write inserts DET with Definite=Def (default)
```

This is D in action: the dimension exists in the universal space even when a particular language doesn't traverse it. Defaults bridge the gap but lose optionality — "a dog" vs "the dog" is a real distinction in English that Japanese structurally lacks. The default (Definite=Def) is a guess, and the K/X cost of that guess is quantifiable.

### Morphological Realization (FST)

Surface forms are realized by a three-level FST (finite state transducer), each level a B partition of the lemma space:

1. **Irregulars** — exception partition (eat → ate, be → was). Hardcoded, finite.
2. **Class-based rules** — verb class → transformation mapping. Each class (e.g., Japanese stem-る verbs) has a transformation dict: feature path → (match, replace).
3. **Pattern fallback** — suffix-based rules for unclassified lemmas.

The fallback layer is scaffolding. With complete training data, it should be **empty** — all lemmas would be classified and use class-based rules. This mirrors the theory's progression from heuristic to derived: the pattern rules are placeholders for a complete class discovery.

---

## Why Lossless

Three mathematical guarantees:

### 1. Read/Write Are True Inverses

```
read(write(bld, cal), cal) = bld   (exact equality)
```

The same calibration data drives both directions. This is tested by round-trip validation across all supported languages.

### 2. Lex Preserves Structure

Lexicon substitution operates ONLY on lemmas:
- B (roles) — unchanged
- L (links) — unchanged
- D (features) — unchanged

It substitutes content, not structure.

### 3. BLD Is Complete and Irreducible

The [Completeness Proof](../../mathematics/foundations/proofs/completeness-proof.md) (Theorem 3.5) shows that all computable types decompose into Sum (B) + Function (L) + Product (D). No fourth primitive is needed. If read extracts all three, and write reconstructs from all three, nothing is lost.

The [Irreducibility Proof](../../mathematics/foundations/proofs/irreducibility-proof.md) shows each primitive is necessary — no two can express the third:

| Drop | Sublanguage | What Breaks | Translation Consequence |
|------|-------------|-------------|------------------------|
| B | LD-calculus | All types have cardinality 1 — can't express choice | Can't distinguish word senses (no variant selection) |
| L | BD-calculus | No function application — can't express traversal | Can't follow dependencies (no head-dependent linking) |
| D | BL-calculus | No parametric families — can't express repetition | Can't handle agreement, feature bundles, or arrays of tokens |

**Falsifiable prediction**: a translator missing any one primitive will fail on the corresponding structure class. This is a mathematical impossibility, not an engineering limitation.

### What Lossless Means (and Doesn't)

**Lossless** means structural preservation: `read(write(bld, cal), cal) = bld`. The B, L, D components survive the round trip. This is proven, tested, and falsifiable.

**Not preserved**: pragmatic meaning, register, quantifier scope (∀∃ vs ∃∀), implicature, speech acts, information structure (topic/focus/given/new). These live outside B/L/D — they are K/X observation costs, the gap between structure and full meaning.

The gap is quantifiable. At the pragmatic scale, X is very large (the full discourse context), so K/X per unit is small — but it's real. "The cat ate the fish" preserves structure perfectly in translation; "Can you pass the salt?" (request, not question) loses its speech act. The structural translation is correct; the pragmatic interpretation requires world knowledge the translator doesn't model.

Frame: translation is **structurally lossless** with **quantifiable pragmatic loss**. The loss is K/X at scales the translator doesn't yet traverse.

---

## BLD at Three Scales

The same three primitives recurse at every structural level. The translator implements all three:

| Scale | B (Partition) | L (Link) | D (Repetition) |
|-------|---------------|----------|-----------------|
| **Token** | POS tag | head pointer + relation | feature bundle {Tense, Voice, ...} |
| **Sentence** | grammatical roles {S, V, O, Q, ADV} | dependency tree | agreement propagation across links |
| **Document** | paragraph boundaries (topic shifts) | coreference chains (entity links) | sentence sequence |

At each scale, the translator applies the same pattern:
- **read** extracts B, L, D from the language-specific form
- **write** reconstructs the language-specific form from B, L, D

Document-level translation (`translate_discourse`) is a nested homomorphism: φ_doc wraps φ_sentence. The three-phase extraction mirrors the primitives:
1. D: read each sentence to UniversalBLD
2. L: detect coreference chains across sentences
3. B: record paragraph boundaries as topic shifts

---

## Cost Conservation

```
C(S) = C(FACTOR(S))
```

Factorization reveals hidden structure without changing total complexity.

### Factorization as Levi Decomposition

The translator's `draw_bld = discover + factor` IS the [Factorization Calculus](../../mathematics/foundations/structural/factorization-calculus.md) — the three factorization rules map directly to its canonicalization steps:

| Rule | Translator Implementation | What It Does |
|------|--------------------------|--------------|
| B-Factor | `_canonicalize_partitions` | Consecutive same-POS tokens → one partition |
| L-Factor | `_canonicalize_links` | Sort dependency links to canonical DAG order |
| D-Factor | `_canonicalize_dimensions` | Sort features to homogeneous products per dimension |

The key theorem — `eval(S) = eval(FACTOR(S))` — is already enforced: the translator verifies cost conservation within 1% tolerance after factorization. This corresponds to the Levi decomposition in Lie theory: structure decomposes uniquely into irreducible B × L × D components.

Note: `factorization.py` currently uses simplified cost formulas (`(len-1)×0.5` for B, flat weights for L) rather than the exact formulas in `cost.py`. This gap is addressed in [Canonical Hardness](#canonical-hardness-why-some-heuristics-are-necessary).

The primitive costs:

| Primitive | Formula | What It Measures |
|-----------|---------|------------------|
| C_B | ½ log(1 + d²_Mahal) | Partition separation |
| C_L | −½ ln(1 − ρ²) | Dependency correlation strength |
| C_D | n × C(element) | Repetition extent |

The B cost decomposes further. From the [Boundary Derivation](../../mathematics/lie-theory/boundary-derivation.md):

```
d²_Mahal = sep² × g(ρ,θ)

where g(ρ,θ) = (1 - ρ sin(2θ)) / (1 - ρ²)
```

Here θ is the angle between the mode separation vector and the correlation principal axis of the concept graph. When synset senses are **aligned** with the graph's main variation (θ ≈ 0), disambiguation cost drops by ~2.3×. When senses are **orthogonal** to the main variation (θ ≈ π/4), cost increases by ~2.3×. This predicts which polysemy cases are structurally hard: senses orthogonal to the concept graph's dominant correlation direction.

Complexity doesn't vanish — it moves. When auxiliary absorption hides a feature (reducing visible D), the calibration that absorbs it carries the cost. Total is conserved.

K = 2 appears here: bidirectional observation cost. Every measurement costs at least 2 links (query + response). Translation inherits this — source→universal and universal→target are the two traversals.

K/X sets a structural floor on translation uncertainty:

| Structure | X | K/X | Meaning |
|-----------|---|-----|---------|
| Boundary mapping | B = 56 | 2/56 ≈ 3.6% | Baseline partition uncertainty |
| Link mapping | n×L = 80 | 2/80 = 2.5% | Baseline dependency uncertainty |
| Full structure | n×L×B = 4480 | 2/4480 ≈ 0.04% | Baseline semantic uncertainty |

These are structural limits, not engineering limitations. If translation residuals are ~2-4%, you've hit the K/X floor for that scale.

### Compensation Principle

The [Compensation Principle](../../mathematics/foundations/structural/compensation-principle.md) establishes an asymmetry: L can compensate for B, but B cannot compensate for L. This is structural, not empirical — it follows from B being topological (local) and L being geometric (global).

For translation:
- A translator with rich linking (synset graph, dependency context, coreference chains) can disambiguate subtle sense distinctions even with weak boundary detection
- The reverse fails: no amount of POS tag refinement can disambiguate without dependency context

The translator already validates this. Joint edge disambiguation invests in L — it uses the full dependency graph to constrain synset selection. Attempting the same via B alone (finer POS categories, more partitions) would not reach cross-token information.

**Development priority**: invest in L (expand concept graph, strengthen coreference) before B (finer POS categories, more word classes). L problems need new connections; B problems need sharper local partitions. Only L can reach across the sentence.

---

## Translation as Measurement

Translation IS measurement — one language measuring structure through another. The theory's observer correction framework applies directly:

```
Translated = Structural × (1 + K/X_translator) × (1 + K/X_language_pair)
```

### Three Layers of Translation Cost

| Layer | What It Is | Source | Reducible? |
|-------|------------|--------|------------|
| Structural equivalence | What both languages can express | Pure math (the universal BLD) | No — it's the answer |
| K/X_translator | Systematic bias from our apparatus | Translator architecture | Yes — improve the translator |
| K/X_language_pair | Irreducible distance between languages | Linguistic typology | No — structural fact |

The first layer is the homomorphism — perfect by construction. The second is where heuristics live (POS distance matrix, dependency strengths, spectral dimension). The third is what makes Japanese-to-English harder than Spanish-to-English.

### The Structural Manifold

Translation lives on an information-geometric manifold ([Manifold Foundations](../../mathematics/geometry/manifold-foundations.md)). The three primitives have distinct geometric character:

| Primitive | Character | Scaling | In the Translator |
|-----------|-----------|---------|-------------------|
| B | Topological (mode structure) | O(1) — dimension-independent | POS partitions don't change with embedding dimension |
| L | Metric (correlation) | O(s) — scales with correlated pairs | Dependency count scales linearly |
| D | Multiplier | × on L (KL additivity) | Features multiply per-token L cost |

The Mahalanobis distance used in synset disambiguation IS the geodesic distance on the mean submanifold with the Fisher-Rao metric. The Cholesky whitening pre-computed in `concept_lexicon.py` converts Euclidean distance to Mahalanobis — this is computing manifold geodesics, not an ad-hoc metric. The optimal translation path between source and target concepts is the shortest geodesic on this manifold.

### The T ∩ S Detection Framework

When will translation fail? Apply the detection formalism:

- **T** = target language features (what the target can express)
- **S** = source structure (what needs expressing)
- Translation succeeds iff **T ∩ S ≠ ∅** for each structural unit

When T ∩ S = ∅, the structure is **untranslatable** — it requires paraphrase, which shifts complexity from one primitive to another. Example: Japanese honorific registers have no English equivalent → paraphrase via explanation (L increases, D decreases). The complexity moves; it doesn't vanish.

### Information Preservation

The [entanglement entropy formula](../../mathematics/quantum/entanglement-entropy.md) quantifies information preservation:

```
S = K × L = 2 × (−½ ln(1 − ρ²))
```

where ρ measures alignment between source and target structures. This gives a quantitative prediction:

- At high alignment (ρ → 1): L → ∞, so S → ∞ — perfect translation has unbounded cost
- At partial alignment (ρ < 1): loss is finite and quantifiable
- At zero alignment (ρ = 0): L = 0, S = 0 — no information transfers (languages share no structure)

The same formula governs entanglement entropy in quantum mechanics and black hole information. Translation information preservation follows the same K×L scaling because it's the same structural relationship: two systems (source, target) sharing correlated structure.

---

## Future: Deriving Constants from Structure

The theory derives physical constants from structural integers + K/X observer corrections:

```
α⁻¹ = n×L + B + 1 + K/B + higher-order = 137.035999...
```

No free parameters. Structure in, number out.

The same methodology should replace the translator's current heuristics — but not all of them. The [Canonical Hardness](../../mathematics/foundations/structural/canonical-hardness.md) result shows that finding the minimum BLD representation is NP-complete (via reduction from Minimum Grammar). Some approximation is mathematically necessary, not just engineering scaffolding.

### Canonical Hardness: Why Some Heuristics Are Necessary

The NP-completeness has a tractable special case: tree-structured systems are O(n). Dependency trees ARE trees, so sentence-level factorization is tractable. The NP-hardness appears at document level, where discourse structure has sharing and cycles (coreference creates graph structure from tree structure).

The translator's heuristics split into two categories:

**Derivable** — scaffolding to replace with derived values:

| Current Heuristic | File | BLD Derivation |
|-------------------|------|----------------|
| POS_DISTANCE matrix | cost.py | Spectral embedding of UD dependency graph — POS categories are B; distances come from graph Laplacian eigenvectors |
| DEP_STRENGTH values | cost.py | Information content per dependency type — mutual information between head and dependent |
| Relation priority ordering | traverser.py | Information gain ranking — which dependent best disambiguates the head |
| Required feature defaults | lang.toml | Corpus mode — most frequent value IS the structural default |
| Agreement rules | lang.toml | Auto-discover from corpus feature correlation |
| Binary script penalty | concept_lexicon.py | −log(borrowing_frequency) from corpus |
| Simplified cost formulas | factorization.py | Use exact formulas from cost.py (C_B, C_L, C_D) |

**Structurally necessary** — approximations required by NP-hardness:

| Current Heuristic | File | Why It's Necessary |
|-------------------|------|--------------------|
| Spectral dimension k=16 | concept_lexicon.py | Optimal k requires global comparison across all representations — NP-hard. Use spectral gap heuristic (smallest k where λ_k/λ_1 exceeds threshold) |
| Greedy factorization | factorization.py | Optimal factorization is NP-complete at document level. O(log n)-approximation is the best polynomial guarantee |
| Post-order disambiguation | traverser.py | Globally optimal synset assignment requires comparing all valid assignments — NP-hard. Greedy bottom-up is O(n) |

### K/X at Different Linguistic Scales

Forces in physics are K/X at different X values. The same applies to linguistic "forces":

| Level | X (Structure Traversed) | Error Magnitude | Implication |
|-------|------------------------|-----------------|-------------|
| Morphology | Small (inflection space) | Large per-unit | Rule-based, exact — cheap to fix |
| Syntax | Medium (reordering space) | Medium | Permutation group, well-understood |
| Semantics | Large (concept space) | Small per-unit | Needs full context, expensive |
| Pragmatics | Very large (discourse) | Tiny per-unit | Needs document-level structure |

**Prediction**: Error rate scales as K/X. Morphological errors are large but cheap to fix. Semantic errors are small but expensive. The current translator treats all levels uniformly — the theory says allocate resources proportional to 1/X at each scale.

### Bidirectional Disambiguation (Born Rule)

The Born rule derives P = |ψ|² from bidirectional alignment. For translation:

- Current approach scores forward only (source → candidate synset)
- Theory predicts: P(target | source) ∝ |forward_score × backward_score|
- Bidirectional scoring requires both source→target AND target→source consistency
- This is K=2: observation cost is always bidirectional

The traverser ALREADY does this for joint edge disambiguation — scoring synset pairs bidirectionally on dependency edges. This is where the theory is already working. The next step: extend bidirectional scoring to ALL disambiguation decisions.

### Transform Group Completion

Current `transforms.py` has 2 transforms: role permutation (S₅) and voice (Z₂). The theory predicts a full Lie algebra with closure:

| Missing Transform | Type | Theory Basis |
|-------------------|------|-------------|
| Argument alternation (transitive ↔ ditransitive) | B | Partition restructuring |
| Case marking transforms | D | Feature dimension operators |
| Aspect/modality operators | D | Feature group actions |
| Link strength modification | L | Connection weight transforms |
| Clause restructuring (embedding ↔ coordination) | B+L | Combined boundary + link transforms |
| Transform composition | All | Group closure — transforms should chain |

Transforms should form an algebra with closure, associativity, and identity. Currently they're isolated operations.

### Sublanguage Impossibilities

The [Irreducibility Proof](../../mathematics/foundations/proofs/irreducibility-proof.md) predicts what happens when a translator drops a primitive:

| Missing Primitive | Sublanguage | What Breaks in Translation |
|-------------------|-------------|---------------------------|
| B | LD-calculus | Cannot select between word senses — all candidates collapse to cardinality 1 |
| L | BD-calculus | Cannot follow dependency structure — no function application, no head-dependent linking |
| D | BL-calculus | Cannot handle feature bundles or agreement — parametric families require D |

These are **proven impossibilities**, not engineering trade-offs. Any translator architecture that implicitly drops a primitive (e.g., bag-of-words models drop L; simple dictionary lookup drops D) will fail on the corresponding structure class. The irreducibility proof tells you exactly which class and why.

### Discovery Independence

Current `discovery.py` is wired to UD annotations — it wraps Stanza parsing output. The theory says DRAW_BLD should discover B, L, D from ANY system:

- Implicit structure (zero anaphora, ellipsis, pragmatic implicature) is currently invisible
- The completeness proof guarantees B, L, D are sufficient — but only if we extract all three from the signal
- Discovery should be annotation-independent: derive partitions, links, and repetitions from the raw structure, not from a particular annotation scheme

### Scope and Pragmatics

Phenomena not yet modeled:

- **Quantifier scope**: "Every student read a book" (∀∃ vs ∃∀) is not captured by dependency structure alone — scope ambiguity requires a representation beyond head-dependent linking
- **Information structure**: topic/focus/given/new partitions the sentence pragmatically, not syntactically — this is a B that current calibration doesn't encode
- **Implicature and speech acts**: "Can you pass the salt?" is structurally a question, pragmatically a request — the speech act lives outside B/L/D

These are K/X costs at the pragmatic scale — quantifiable but not yet modeled. The compensation principle predicts these need L-investment (discourse linking, context accumulation) rather than B-refinement (finer syntactic categories).

---

## Validation

| Property | Test | Status |
|----------|------|--------|
| Lossless round-trip (eng) | read(write(bld, eng), eng) = bld | Validated |
| Lossless round-trip (jpn) | read(write(bld, jpn), jpn) = bld | Validated |
| Lossless round-trip (ara) | read(write(bld, ara), ara) = bld | Validated |
| Lexicon preserves structure | BLD(lex(universal)) = BLD(universal) | Validated |
| Voice transform reversibility | active(passive(bld)) = bld | Validated |
| Cost conservation | C(factored) ≈ C(original) | Validated |

200+ tests across 11 test files. Languages: English, Japanese, Arabic.

### Typological Coverage

Current validation covers nominative-accusative alignment, non-tonal prosody, and moderate inflection (English, Japanese, Arabic). Not yet tested:

| Type | Example | Specific Gap |
|------|---------|-------------|
| Tonal | Mandarin, Yoruba | Tone as a D feature — no calibration exists |
| Polysynthetic | Greenlandic Inuktitut | Word-level embedding of full clauses — current token model may not suffice |
| Ergative-absolutive | Basque, Dyirbal | Role assignment differs from nominative-accusative — S/O mapping needs calibration |
| Classifier systems | Mandarin, Thai | Numeral classifiers as a D between determiner and noun |
| Serial verb constructions | Yoruba, Thai | Multiple verbs sharing arguments — dependency tree may need augmentation |

The BLD framework should extend to all of these — completeness guarantees B, L, D are sufficient — but the calibration data and validation don't exist yet.

---

## No ML Required

The translator uses **no machine learning** for translation itself. The pipeline is deterministic: read (φ⁻¹) → lexicon substitution → write (φ). All language-specific knowledge is calibration data (TOML files), not trained weights. The disambiguation uses structural distance (Mahalanobis on spectral embeddings), not learned probabilities.

The one ML dependency is **parsing** — Stanza provides POS tags, dependency trees, and lemmatization. This is temporary scaffolding. A BLD parser (DRAW_BLD applied to raw text) is planned, which would eliminate the last ML component. The parser needs only to discover B (where does behavior change?), L (what connects to what?), and D (what repeats?) from the character stream — the same three questions applied at the sub-word level.

This distinguishes the approach from neural machine translation:

| | Neural MT | BLD Translation |
|---|-----------|-----------------|
| Training data | Millions of parallel sentences | Zero (calibration is hand-authored or derived from dictionaries) |
| Translation logic | Learned weights (opaque) | Three function calls (transparent) |
| New language | Retrain or fine-tune | Add calibration file |
| Failure mode | Fluent but wrong (hallucination) | Grammatically correct, semantically traceable |
| Round-trip | Not guaranteed | Exact (`read(write(bld)) = bld`) |
| Why it works | Statistical correlation | Mathematical homomorphism |

---

## See Also

- [Human Language Structure](../../theory/human-language-structure.md) — Natural language as BLD
- [BLD as Universal Language](../../theory/bld-as-language.md) — BLD compiles to any substrate
- [Cross-Language Compilation](../code/cross-language-compilation.md) — Same approach for code
- [Killing Form](../../mathematics/lie-theory/killing-form.md) — Why K=2
- [Observer Correction](../../mathematics/cosmology/observer-correction.md) — K/X principle
- [Force Structure](../../mathematics/foundations/derivations/force-structure.md) — K/X at different scales
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — BLD ↔ Lie algebra
- [Completeness Proof](../../mathematics/foundations/proofs/completeness-proof.md) — BLD captures all computable types
- [Irreducibility Proof](../../mathematics/foundations/proofs/irreducibility-proof.md) — Each primitive is necessary
- [BLD Calculus](../../mathematics/foundations/definitions/bld-calculus.md) — The type system
- [Entanglement Entropy](../../mathematics/quantum/entanglement-entropy.md) — S = K×L information formula
- [Factorization Calculus](../../mathematics/foundations/structural/factorization-calculus.md) — FACTOR = Levi decomposition
- [Canonical Hardness](../../mathematics/foundations/structural/canonical-hardness.md) — NP-completeness of minimal BLD
- [Compensation Principle](../../mathematics/foundations/structural/compensation-principle.md) — L compensates B, not vice versa
- [Manifold Foundations](../../mathematics/geometry/manifold-foundations.md) — Information-geometric manifold
- [Boundary Derivation](../../mathematics/lie-theory/boundary-derivation.md) — Exact B cost formula with g(ρ,θ)
- [Glossary](../../glossary.md) — Central definitions
