---
status: FOUNDATIONAL
layer: 1
depends_on:
  - ../theory/structural-language.md
  - ../meta/discovery-method.md
used_by:
  - ../theory/structural-language.md
  - ../theory/README.md
  - ../paths/practitioner.md
  - README.md
  - wgpu-jpeg-process.md
---

# ZIP Structure (Three Primitives)

## Quick Summary (D≈7 Human Traversal)

**ZIP file in BLD in 7 steps:**

1. **Signature = B** — Partitions entry type: 0x504B0304 (local), 0x504B0102 (central), 0x504B0506 (end)
2. **flags.bit3 = B** — Partitions size placement: inline (0) vs deferred (1)
3. **filename_len = L** — Links to filename extent
4. **compressed_size = L** — Links to data extent (or sentinel for ZIP64)
5. **local_file_entry = D[N]** — N files repeated in same structure
6. **central_dir = D[M]** — M directory entries repeated
7. **ZIP = nested BLD** — Boundaries partition types, links specify lengths, dimensions repeat entries

| ZIP Component | BLD Primitive |
|---------------|---------------|
| Signature magic | B (type partition) |
| Length fields | L (extent link) |
| File array | D (repetition) |

---

> **Status**: Foundational

> Drawn using only: **boundary** (partition), **link** (connect), **dimension** (repeat)

---

## The Three Primitives

| Primitive | What it is |
|-----------|-----------|
| **boundary** | Partitions value space into regions of meaning |
| **link** | Connects one value to another |
| **dimension** | Axis of repetition (with extent) |

---

## ZIP in Three Primitives

```
ZIP
│
├── boundary: signature value partitions entry type
│   │
│   │   signature == 0x504B0304 → local_file_entry
│   │   signature == 0x504B0102 → central_dir_entry
│   │   signature == 0x504B0506 → end_of_central_dir
│   │
│   └── (one boundary, three regions of meaning)
│
├── dimension[N]: local_file_entry
│   │             (N = number of files, extent determined by structure)
│   │
│   ├── boundary: flags.bit3 partitions size placement
│   │   │
│   │   │   bit3 == 0 → sizes inline
│   │   │   bit3 == 1 → sizes deferred
│   │   │
│   │   └── (value partitions, not bytes)
│   │
│   ├── link: filename_len → extent of filename
│   ├── link: extra_len → extent of extra
│   ├── link: compressed_size → extent of data (or sentinel)
│   │
│   └── boundary: compressed_size == 0xFFFFFFFF partitions size source
│       │
│       │   != sentinel → size is compressed_size
│       │   == sentinel → size is extra.zip64.size
│       │
│       └── link: to actual size value (wherever it lives)
│
├── dimension[M]: central_dir_entry
│   │             (M = entries_total from end record)
│   │
│   ├── link: local_offset → local_file_entry[?]
│   │         (connects index to data)
│   │
│   ├── link: filename_len → extent of filename
│   ├── link: extra_len → extent of extra
│   └── link: comment_len → extent of comment
│
└── end_of_central_dir (dimension[1] - exactly one)
    │
    ├── link: entries_total → extent of central_dir dimension
    ├── link: cd_offset → central_dir_entry[0]
    │         (entry point - where to start reading index)
    │
    └── link: comment_len → extent of comment
```

---

## Visual: Boundaries Partition Value Space

```
                    SIGNATURE VALUE SPACE
    ┌─────────────────┬─────────────────┬─────────────────┐
    │   0x504B0304    │   0x504B0102    │   0x504B0506    │
    │                 │                 │                 │
    │  local_file     │  central_dir    │  end_of_central │
    │  _entry         │  _entry         │  _dir           │
    └─────────────────┴─────────────────┴─────────────────┘

                    FLAGS.BIT3 VALUE SPACE
    ┌─────────────────────────┬─────────────────────────┐
    │          0              │           1             │
    │                         │                         │
    │    sizes inline         │    sizes deferred       │
    │    (in header)          │    (after data)         │
    └─────────────────────────┴─────────────────────────┘

                 COMPRESSED_SIZE VALUE SPACE
    ┌─────────────────────────┬─────────────────────────┐
    │     != 0xFFFFFFFF       │     == 0xFFFFFFFF       │
    │                         │                         │
    │   size = this value     │   size = extra.zip64    │
    └─────────────────────────┴─────────────────────────┘
```

---

## Visual: Links Connect Values

```
end_of_central_dir
    │
    ├── entries_total ─────────────────┐
    │   (value: N)                     │ link: determines dimension extent
    │                                  ▼
    ├── cd_offset ──────────────► central_dir_entry[0..N]
    │   (value: byte position)         │
    │                                  │
    │                    ┌─────────────┘
    │                    │
    │                    ▼
    │              local_offset ──────► local_file_entry[?]
    │              (value: byte position)
    │
    └── comment_len ──────► extent of comment
        (value: size)
```

---

## Visual: Dimensions Add Axes

```
                    ZIP FILE
                       │
         ┌─────────────┼─────────────┐
         │             │             │
         ▼             ▼             ▼
    ┌─────────┐  ┌─────────┐  ┌─────────────┐
    │ local   │  │ central │  │ end_of      │
    │ _file   │  │ _dir    │  │ _central    │
    │ _entry  │  │ _entry  │  │ _dir        │
    └─────────┘  └─────────┘  └─────────────┘
         │             │             │
    dimension[N]  dimension[M]  dimension[1]
         │             │
         │             └── M determined by link (entries_total)
         │
         └── N determined by structure (read until different signature)
```

---

## Observations

### 1. Boundaries partition meaning, not bytes
Every boundary is a VALUE comparison that selects interpretation.
The bytes are just how values are encoded.

### 2. Links connect everything
- Offsets are links (position → target)
- Lengths are links (count → extent of dimension)
- Discriminators are links (value → boundary partition)

### 3. Dimensions are axes of repetition
- local_file_entry[N] - N files
- central_dir_entry[M] - M index entries
- end_of_central_dir[1] - exactly one

Extent of dimension comes from a link (length field) or structure (read until boundary changes).

### 4. No "containment" primitive needed
What we called containment is just:
- A boundary (defines the region's meaning)
- Links (to what's "inside")
- Optionally a dimension (if contents repeat)

### 5. Scope emerges from boundaries
Things that share a boundary partition share fate.
The boundary defines scope. Scope isn't a separate concept.

---

## The Three Primitives - Final

| Primitive | ZIP Examples |
|-----------|--------------|
| **boundary** | signature selects entry type, flags.bit3 selects layout, sentinel selects size source |
| **link** | offsets point to entries, lengths define extents, discriminators select partitions |
| **dimension** | N local entries, M central entries, arrays of bytes |

Everything else is pattern:
- Containment = boundary + links
- Scope = shared boundary
- Extent = link to dimension size
- View/variant = boundary partition + links to interpretations

---

## See Also

- [Glossary](../glossary.md) — Central definitions
- [Structural Language](../theory/structural-language.md) — B/L/D specification
- [Discovery Method](../meta/discovery-method.md) — How to find structure
- [JPEG Pipeline](./wgpu-jpeg-process.md) — Another worked example
