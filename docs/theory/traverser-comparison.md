---
status: FOUNDATIONAL
layer: 0
depends_on: []
used_by: []
---

# Traverser Comparison

A traverser is structure that processes structure. Different traversers have different BLD capacities.

## Summary

**Traverser D varies within and across types:**

1. D is not fixed — varies by traverser type, individual, and context — [D Varies](#d-varies-within-and-across-types)
2. Humans: working memory 5-9 items, expertise increases effective D via chunking — [Human Traversers](#human-traversers)
3. LLMs: can read first ~100 lines from ALL files at once, enabling codebase-scale overview — [LLM Traversers](#llm-traversers)
4. Computational: GPUs have massive D for parallel work, limited D for divergent branching — [Computational Traversers](#computational-traversers)

---

## D Varies Within and Across Types

D (dimension capacity) is not fixed — it varies:
- Between traverser types (human vs LLM vs GPU)
- Within types (you vs me, Claude vs Gemini, RTX 4090 vs A100)
- By context (expert vs novice, fresh vs fatigued)

---

## Human Traversers

| Parameter | Range | Notes |
|-----------|-------|-------|
| Working memory (D) | 5-9 items | Miller's 7±2, varies by individual |
| Chunk size | Expertise-dependent | Grandmaster sees board patterns, novice sees pieces |
| Session duration | 30min - 4hrs | Varies by engagement, fatigue |
| Long-term retrieval (L) | Varies | Some people have better associative memory |

An expert has higher effective D in their domain because they chunk information differently. A chess grandmaster looking at a board position doesn't see 32 pieces — they see familiar patterns that compress into fewer chunks.

---

## LLM Traversers

| Model | Context (D) | Architecture | Notes |
|-------|-------------|--------------|-------|
| Claude | Large | Attention-based | Different from Gemini |
| Gemini | Large | Different attention | Different from Claude |
| GPT-4 | Large | Yet another | Each has unique D profile |

Same prompt, different traversal. The "capacity" includes not just context window but how attention distributes.

### How LLMs Use Summaries

LLMs benefit from summaries differently than humans:

**Scale advantage**: An LLM can't read all 104 full documents at once (context limit). But it CAN read the first ~100 lines from ALL 104 files simultaneously. This means well-designed summaries give the LLM a structural overview of the entire codebase in one read.

**Navigation**: Section links in summaries let the LLM jump directly to relevant content without reading the full document.

**Triage**: Summary helps decide if a full read is needed, or if the summary provides sufficient context.

**Efficiency**: Good summaries can eliminate the need for spawning explore agents or doing multiple read passes.

Summaries act as a structured index — the LLM can read the summary, identify which section matters, then read only that section.

---

## Computational Traversers

| Hardware | D Characteristics |
|----------|-------------------|
| x86 CPU | 16 GP registers, cache hierarchy (L1→L2→L3), branch prediction depth |
| GPU | Warp size (32-64), shared memory per SM, total thread count |
| TPU | Matrix unit size, HBM bandwidth |

A GPU has massive D for parallel uniform work (thousands of threads), but limited D for divergent branching (warp divergence penalty). An x86 CPU has limited D for parallelism but high D for complex branching.

---

## Why This Matters for Documentation

The summaries in this documentation are designed for multiple traverser types:

**For humans:**
- Keep within working memory (~7 items is a guideline, not a rule)
- Chunk related concepts together
- Front-load key information
- Section links enable quick navigation

**For LLMs:**
- First ~100 lines contain frontmatter + summary = quick file understanding
- Section links enable selective reading
- Structured format is easy to parse
- Scale: summaries from all files can be read together

The exact number of items in a summary should fit the content, not force content into a fixed count.

---

## See Also

- [Glossary](../glossary.md) — Central definitions
- [Structural Language](structural-language.md) — BLD foundations
