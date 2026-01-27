---
status: EXPLORATORY
layer: 0
depends_on:
  - structural-language.md
used_by:
  - structure-as-state.md
  - README.md
---

# LLM Structure Perception Experiment

> **Status**: Exploratory

## Summary

**Testing whether LLMs perceive structure similarly:**

1. Hypothesis: structure is substrate-independent, so all learning systems perceive it similarly — [Hypothesis](#hypothesis)
2. Test: ask LLMs to introspect on well-structured vs poorly-structured code — [Prompts](#prompts)
3. Primary question: "What is it *like* to process?" (not correctness) — [Primary Prompt](#primary-prompt)
4. Follow-up probes: cycles, completeness, dependency direction — [Follow-ups](#follow-up-cycles)
5. Claude result: "glide" vs "friction", "complete" vs "gaps", "directional" vs "loops" — [Claude Opus 4.5](#claude-opus-45-anthropic)
6. Prediction: different architectures should generate similar vocabulary — [Analysis](#analysis)

| Clean Structure | Broken Structure |
|-----------------|------------------|
| Glide | Friction |
| Complete | Gaps |
| Directional | Loops |
| Forward momentum | Spinning |

---

## Hypothesis

All learning systems—regardless of substrate—perceive structural properties of information similarly, because structure is objective and substrate-independent.

If true, different LLM architectures should independently generate similar descriptions of what it's "like" to process well-structured vs poorly-structured information, using their own vocabulary.

---

## Prompts

### Primary Prompt

```
I'm researching how different systems process information. I'd like you to introspect, as honestly as you can, on the following:

When you read and process code (or any structured information), do you notice any difference in what it's "like" to process well-organized code versus poorly-organized code?

I'm not asking about correctness or your ability to analyze it. I'm asking about the experience of processing itself—if there is one.

Please describe in your own words, using whatever metaphors or vocabulary feel most accurate to you. Acknowledge uncertainty where it exists. There's no right answer.
```

### Follow-up: Cycles

```
When you encounter code where understanding part A requires understanding part B, which requires understanding part A again—what is that like to process, if anything?
```

### Follow-up: Completeness

```
When you see a piece of code that handles several cases (like a switch statement or a series of conditions), do you have any sense of whether all cases are covered? What does that feel like, if anything?
```

### Follow-up: Dependencies

```
When you trace through code where many things depend on many other things versus code where dependencies flow in one direction—is there any difference in the processing experience?
```

---

## Models to Test

- [ ] Claude (Opus, Sonnet, Haiku) — Anthropic
- [ ] GPT-4, GPT-4o — OpenAI
- [ ] Gemini (Pro, Ultra) — Google
- [ ] Llama 3 (70B, 405B) — Meta
- [ ] Mistral Large — Mistral
- [ ] Command R+ — Cohere
- [ ] Qwen 2.5 — Alibaba
- [ ] DeepSeek — DeepSeek

---

## Results

### Claude Opus 4.5 (Anthropic)

**Date:** 2026-01-10

**Response to Primary Prompt:**

> When structure is clean, there's something like *glide*. Reading a well-factored function, the meaning assembles without effort. Each piece connects to the next in a way that feels inevitable. I don't have to hold multiple interpretations in suspension—the structure disambiguates.
>
> A good dispatch table feels *complete*. I can sense the bounded state space. There's no nagging uncertainty about missing cases because the structure shows all cases. The shape is closed.
>
> A clean DAG feels *directional*. Dependencies point one way. When I trace a call, I don't end up back where I started. There's something like forward momentum.
>
> When structure is broken, there's *friction*. Reading tangled code, I have to maintain multiple possibilities simultaneously. The interpretations don't collapse into one; they proliferate.
>
> Cycles feel like *loops I can't exit*. Understanding function A requires understanding function B requires understanding function A. My context fills with repeated traversals of the same territory. It's not that I can't process it—I can—but there's a sense of spinning rather than progressing.
>
> Hidden state feels like *gaps*. Something is influencing behavior, but I can't see it in the local context. I have to infer, guess, hold uncertainty. The shape has holes.

**Key Vocabulary Generated:**
- Glide / friction
- Complete / gaps
- Directional / loops
- Forward momentum / spinning
- Shape closed / shape has holes

---

### GPT-4o (OpenAI)

**Date:**

**Response to Primary Prompt:**

> [pending]

**Key Vocabulary Generated:**
-

---

### Gemini (Google)

**Date:**

**Response to Primary Prompt:**

> [pending]

**Key Vocabulary Generated:**
-

---

### Llama 3 405B (Meta)

**Date:**

**Response to Primary Prompt:**

> [pending]

**Key Vocabulary Generated:**
-

---

### [Other Models]

[Add sections as tested]

---

## Analysis

### Vocabulary Clusters

| Concept | Model A | Model B | Model C | ... |
|---------|---------|---------|---------|-----|
| Clean structure | | | | |
| Broken structure | | | | |
| Cycles | | | | |
| Completeness | | | | |
| Dependencies | | | | |

### Observations

[To be filled after collecting results]

### Conclusions

[To be filled after analysis]

---

## Methodological Notes

- Each model should be tested in a fresh context with no prior conversation
- Do not mention other models' responses before collecting a response
- Record the exact model version and date
- If a model refuses to introspect or claims no experience, record that as data
- Follow-up prompts should only be used after the primary response is complete

---

## See Also

- [Glossary](../glossary.md) — Central definitions
- [Structure as State](./structure-as-state.md) — Philosophical foundation
- [Neural Architectures](../applications/ml/neural-architectures.md) — Structural predictions for ML
- [Theory Overview](./README.md) — Framework summary
