---
status: DERIVED
layer: example
depends_on:
  - ../theory/human-language-structure.md
  - ../theory/structural-language.md
used_by:
  - ../theory/human-language-structure.md
---

# Refusal Analysis: "I don't want to" as Reversible BLD

> **Status**: Derived — demonstrates BLD completeness via lossless bidirectional encoding.

This example demonstrates that natural language maps to BLD primitives through lossless, bidirectional encoding: English -> BLD -> English with round-trip fidelity.

---

## Summary

**"I don't want to" in BLD — lossless bidirectional encoding:**

1. Semantic primitives (B): person, number, polarity, tense, modality, aspect — [Semantic Primitives](#semantic-primitives-b)
2. Active configuration: first + singular + negative + present + desire + infinitive — [Active Configuration](#active-configuration)
3. Semantic links (L): subject→predicate, negation→auxiliary, modal→verb — [Semantic Links](#semantic-links-l)
4. Token dimension (D): 4 sequential words encode the structure — [Encoding Dimension](#encoding-dimension-d)
5. Round-trip: encode(decode(tokens)) = tokens (lossless) — [Round-Trip Verification](#round-trip-verification)
6. Cross-language: same B+L, different D — "I don't want to" (4) = "No quiero" (2) — [Cross-Language Invariance](#cross-language-invariance)

| Language | Encoding | D (tokens) |
|----------|----------|------------|
| English | "I don't want to" | 4 |
| Spanish | "No quiero" | 2 |
| German | "Ich will nicht" | 3 |

---

## Semantic Primitives (B)

The boundaries that partition semantic space:

| Primitive | Partitions | This Sentence |
|-----------|------------|---------------|
| **person** | first \| second \| third | first |
| **number** | singular \| plural | singular |
| **polarity** | negative \| positive | negative |
| **tense** | present \| past \| future | present |
| **modality** | desire \| obligation \| ability \| permission | desire |
| **aspect** | infinitive \| gerund \| participle \| finite | infinitive |

### Active Configuration

The sentence "I don't want to" activates:

```
person.first AND number.singular AND polarity.negative AND
tense.present AND modality.desire AND aspect.infinitive
```

---

## Semantic Links (L)

How primitives compose into meaning:

| Link | From | To | Dependencies |
|------|------|----|--------------|
| **subject** | (person, number) | predicate | 1 |
| **negation** | polarity | auxiliary | 1 |
| **temporal** | tense | auxiliary | 1 |
| **modal_verb** | modality | main_verb | 1 |
| **complement** | aspect | continuation | 1 |

Total L cost: 5 semantic links to compose a refusal.

---

## Encoding Dimension (D)

The token sequence that encodes the structure:

```
D tokens: 4 [sequential]

Slots:
  0: "I"
  1: "don't"
  2: "want"
  3: "to"
```

---

## Bidirectional Mapping

### ENCODE: Structure -> Tokens

| Slot | Structure | Token |
|------|-----------|-------|
| 0 | person.first AND number.singular | "I" |
| 1 | polarity.negative AND tense.present | "don't" |
| 2 | modality.desire | "want" |
| 3 | aspect.infinitive | "to" |

### DECODE: Tokens -> Structure

| Token | Structure |
|-------|-----------|
| "I" | person.first AND number.singular |
| "don't" | polarity.negative AND tense.present |
| "want" | modality.desire |
| "to" | aspect.infinitive |

### Round-Trip Verification

```
Input:  "I don't want to"
Parse:  ["I", "don't", "want", "to"]
Decode: {first, singular, negative, present, desire, infinitive}
Encode: ["I", "don't", "want", "to"]
Output: "I don't want to"

Lossless.
```

---

## Cross-Language Invariance

The structure is invariant. The encoding varies.

| Language | Encoding | D (tokens) |
|----------|----------|------------|
| English | "I don't want to" | 4 |
| Spanish | "No quiero" | 2 |
| French | "Je ne veux pas" | 4 |
| German | "Ich will nicht" | 3 |

**Same semantic structure (B + L), different dimensional encoding (D).**

This demonstrates the key BLD principle: meaning lives in B and L, encoding lives in D. You can change D without changing meaning.

---

## Key Insight

**Encoding is ONLY D.** The structure path -> tokens mapping is purely dimensional:

```
structure_path -> tokens

Where:
  structure_path = configuration of active B primitives + L composition
  tokens = D sequence of symbols
```

The mapping is bijective when the encoding is well-formed. This is why:
- Machine translation preserves meaning (same B+L) while changing D
- Paraphrase preserves meaning (same B+L) while changing D
- Compression works (fewer D tokens, same B+L structure)

---

## See Also

- [Human Language Structure](../theory/human-language-structure.md) - Full framework
- [Structural Language](../theory/structural-language.md) - B/L/D specification
