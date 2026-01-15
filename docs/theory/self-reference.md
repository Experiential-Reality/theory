---
status: FOUNDATIONAL
layer: 0
depends_on:
  - structural-language.md
used_by: []
---

# BLD Self-Reference: The Language That Defines Itself

> **Status**: Foundational

> BLD can define its own grammar using its own primitives. This is not circular dependency—it's structural recursion.

## Quick Summary (D≈7 Human Traversal)

**BLD Self-Reference in 7 steps:**

1. **Languages are structures** — Token types are B (boundaries), grammar rules are L (links), repetition is D (dimensions)
2. **BLD can describe BLD** — Because BLD describes any structure, it can describe its own grammar (bld.bld)
3. **The three questions apply** — Where does syntax partition? (B: decl_type, token) What connects? (L: parse rules) What repeats? (D: structures, declarations)
4. **Parsing is traversal** — A parser is a traverser over a grammar structure applied to a token stream
5. **D×L scaling applies** — Parse cost = B_grammar + D_tokens × L_match; boundaries are topological (fixed), links scale with input
6. **Bootstrap is recursion, not circularity** — Python parser reads bld.bld, generates Rust compiler, which can then compile bld.bld itself
7. **Self-reference proves universality** — If BLD couldn't describe itself, it couldn't describe everything; this is the same as Gödel and Church

| Component | BLD |
|-----------|-----|
| Token types (keyword, identifier) | B (Boundary) |
| Production rules (A -> B -> C) | L (Link) |
| Multiple structures/declarations | D (Dimension) |
| The parser itself | Traverser |

---

## The Meta-Structural Insight

A language **IS** a structure:

| Language Component | BLD Primitive | Example |
|-------------------|---------------|---------|
| Token types | Boundary (B) | `keyword \| identifier \| number \| symbol` |
| Grammar rules | Link (L) | `structure: keyword -> name -> body` |
| Repetition | Dimension (D) | `declarations[N]`, `partitions[K]` |

Because BLD can describe any structure, it can describe the structure of BLD itself.

---

## The Three Questions Applied to BLD

### Q1: Where does behavior partition? → Syntax Boundaries

```bld
# What kinds of tokens exist?
B token: keyword | identifier | number | string | symbol | newline | eof

# What kinds of declarations exist?
B decl_type: boundary | link | dimension | parameter | returns

# What kinds of extents exist?
B extent_type: fixed | symbolic | computed
```

These are **topological**—the set of declaration types doesn't change as files get larger.

### Q2: What connects to what? → Grammar Links

```bld
# How do we parse a boundary declaration?
L boundary_parse: B_keyword -> name -> colon -> partitions (deps=1)

# How do we parse a link declaration?
L link_parse: L_keyword -> name -> colon -> from -> arrow -> to (deps=1)
```

Each link is a **production rule**. The `deps` value encodes:
- `deps=0` → Choice (can match in any order)
- `deps=1` → Sequence (must match in order)

### Q3: What repeats? → Structural Dimensions

```bld
D structures: N [parallel]      # A file has multiple structures
D declarations: M [parallel]    # A structure has multiple declarations
D partitions: K [parallel]      # A boundary has multiple partitions
D properties: P [parallel]      # A declaration has multiple properties
```

These are **geometric**—they scale with input size.

---

## bld.bld: The Self-Referential Grammar

> **Implementation**: The self-hosted BLD compiler is being developed at [experiential-reality-org/bld](https://github.com/experiential-reality-org/bld).

The file `bld.bld` describes the BLD language using BLD itself:

```bld
structure BLDGrammar

# What repeats (D)
D structures: N [parallel]
D declarations: M [parallel]
D partitions: K [parallel]

# What partitions (B)
B decl_type: boundary | link | dimension | parameter | returns
B token: keyword | identifier | number | string | symbol
B extent_type: fixed | symbolic | computed

# What connects (L)
L file_parse: source -> structures (deps=0)
L structure_parse: keyword -> name -> body (deps=1)
L boundary_parse: B_keyword -> name -> partitions (deps=1)

returns: ParsedBLDFile
```

This structure **describes itself**:
- It has boundaries (decl_type, token, extent_type)
- It has links (file_parse, structure_parse, boundary_parse)
- It has dimensions (structures, declarations, partitions)

---

## The Parser IS a Traverser

The key insight: **parsing is traversing a grammar structure over a token stream**.

```
Grammar Structure (bld.bld)
        ↓
    Traverser
        ↓
Token Stream → Parse Result
```

The grammar defines:
- **What** elements exist (Boundaries)
- **How** they connect (Links with deps)
- **How many** can appear (Dimensions)

The parser traverses this structure, matching tokens against the grammar.

---

## D×L Scaling in Parsing

The cost formula applies to parsing itself:

```
Cost(parse) = B_grammar + D_tokens × L_match
```

Where:
- `B_grammar` = Number of production rules (fixed, topological)
- `D_tokens` = Number of tokens in source (scales with input)
- `L_match` = Cost to match one production (geometric)

**Validated**: The set of declaration types `{B, L, D, P, returns}` is invariant regardless of file size. This is the B component—it doesn't scale with D.

---

## The Bootstrap Circle

```
┌─────────────────────────────────────────────────────────────┐
│                                                             │
│   bld.bld ──────────────→ Python Parser ──────────────→    │
│      ↑                    (bld_format.py)                   │
│      │                          │                           │
│      │                          ↓                           │
│      │                    Parsed Structure                  │
│      │                          │                           │
│      │                          ↓                           │
│      │                  Rust Code Generator                 │
│      │                    (rust_gen.py)                     │
│      │                          │                           │
│      │                          ↓                           │
│      │                   bld_native (Rust)                  │
│      │                          │                           │
│      └──────────── can compile ─┘                           │
│                                                             │
└─────────────────────────────────────────────────────────────┘
```

This is **not circular dependency**—it's structural recursion:

1. `bld.bld` is a valid BLD file
2. The Python parser can parse it
3. The parsed structure describes how to parse BLD files
4. A Rust compiler generated from this can compile `bld.bld`
5. That compiler can then compile itself (self-hosting)

---

## Why This Works

BLD can define itself because **structure is universal**:

1. **Any** formal language has:
   - Finite token types (B)
   - Grammar rules (L)
   - Repetition (D)

2. BLD's three primitives can describe **any** structure

3. Therefore, BLD can describe the structure of BLD

This is the same reason mathematics can describe itself (Gödel), and why the lambda calculus can implement itself (Church).

---

## The Deeper Pattern

```
Structure describes structure.
The describer and the described share the same form.
This is not coincidence—it's necessity.

If BLD couldn't describe itself, it couldn't describe everything.
Self-reference is the proof of universality.
```

---

## Practical Implications

### 1. Language Evolution

To add a new feature to BLD:
1. Add it to `bld.bld` (the grammar)
2. The change is itself a BLD structure
3. The compiler can be regenerated to support it

### 2. Error Messages

The grammar structure enables precise error reporting:
- "Expected one of: boundary | link | dimension" (B)
- "After 'B' keyword, expected: name -> partitions" (L)
- "Partition list allows multiple partitions" (D)

### 3. IDE Support

The grammar structure enables:
- Syntax highlighting (from B token types)
- Auto-completion (from L productions)
- Folding (from D repetition)

---

## See Also

- [Lie Correspondence](../mathematics/lie-theory/lie-correspondence.md) — Why B, L, D are fundamental
- [BLD Implementation](https://github.com/experiential-reality-org/bld) — The self-hosted compiler (in development)
- [Glossary](../glossary.md) — Central definitions
