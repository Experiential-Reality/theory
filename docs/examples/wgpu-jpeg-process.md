---
status: FOUNDATIONAL
layer: application
depends_on:
  - ../theory/structural-language.md
  - ../meta/discovery-method.md
used_by:
  - ../theory/structural-language.md
  - ../theory/README.md
  - zip.md
---

# wgpu-jpeg Decoding Process

## Quick Summary (D≈7 Human Traversal)

**JPEG decoding in BLD in 7 steps:**

1. **Process = D[6]** — Decoding is a dimension with 6 stages
2. **jpeg_bytes → parsed** — B partitions headers vs scan data
3. **parsed → dct_coeffs** — D[B] blocks × D[64] coefficients per block
4. **dct → dequantized** — L links quantization tables to coefficients
5. **dequantized → pixels** — IDCT transforms frequency → spatial
6. **pixels → rgb_image** — D[W×H] pixels × D[3] RGB channels
7. **Pipeline = sequential L** — Each stage links to next: element[i] → element[i+1]

| Stage | BLD Structure |
|-------|---------------|
| File bytes | D[N] homogeneous |
| Blocks | D[B]×D[64] nested |
| Output | D[W×H]×D[3] aligned |

---

> **Status**: Foundational

> Drawn using three primitives: **boundary**, **link**, **dimension**

---

## The Process as a Dimension

JPEG decoding is a process dimension with 6 intermediate structures:

```
decode: dimension[6]
│
├── element[0]: jpeg_bytes
│   └── dimension[N]: raw bytes
│       descriptors: contiguous, homogeneous, fixed(file_size)
│
├── element[1]: parsed_jpeg
│   ├── headers (quantization tables, Huffman tables, dimensions)
│   └── dimension[S]: scan_data (entropy-coded bitstream)
│       descriptors: contiguous, heterogeneous (variable-length codes)
│
├── element[2]: dct_coefficients
│   └── dimension[B]: blocks
│       └── dimension[64]: coefficients per block
│           descriptors: contiguous, homogeneous, fixed(64), aligned(4)
│
├── element[3]: dequantized_coefficients
│   └── dimension[B]: blocks
│       └── dimension[64]: coefficients per block
│           descriptors: (same as above)
│
├── element[4]: pixel_blocks
│   └── dimension[B]: blocks
│       └── dimension[64]: pixels per block (8×8)
│           descriptors: contiguous, homogeneous, fixed(64)
│
└── element[5]: rgb_image
    └── dimension[W×H]: pixels
        └── dimension[3]: RGB channels
            descriptors: contiguous, homogeneous, fixed(3), aligned(4)

links: element[i] → element[i+1] (sequential pipeline)
```

---

## Complexity Analysis

```
N = file size (bytes)
B = number of 8×8 blocks = (W×H)/64
W×H = image dimensions
```

### Stage Complexities

| Stage | Input Dimension | Output Dimension | Complexity |
|-------|----------------|------------------|------------|
| Parse | dimension[N] bytes | headers + dimension[S] scan | O(N) |
| Huffman decode | dimension[S] bits | dimension[B] × dimension[64] | O(S) ≈ O(N) |
| Dequantize | dimension[B] × dimension[64] | dimension[B] × dimension[64] | O(B × 64) = O(W×H) |
| IDCT | dimension[B] × dimension[64] | dimension[B] × dimension[64] | O(B × 64) = O(W×H) |
| Color convert | dimension[B] × dimension[64] | dimension[W×H] × dimension[3] | O(W×H) |

### Total: O(N + W×H)

Sequential stages ADD: O(N) + O(W×H) + O(W×H) + O(W×H) = O(N + W×H)

For typical JPEGs, N ≈ W×H/10 (10:1 compression), so effectively O(W×H).

---

## The GPU Parallelism Dimension

Here's where it gets interesting. The GPU adds a **parallel execution dimension**:

```
huffman_decode_gpu: dimension[B] blocks
│
├── boundary: chunk assignment partitions blocks across threads
│
├── dimension[T]: threads (T = num GPU threads)
│   │
│   │   Each thread processes dimension[B/T] blocks
│   │
│   └── Within thread: dimension[B/T] × dimension[64]
│       └── Sequential: O(B/T × 64)
│
└── Total wall-clock: O(B × 64 / T) = O(W×H / T)
```

**The parallelism is a dimension too.** The GPU spreads the work across a dimension of threads.

```
Sequential:  dimension[B] × dimension[64]           → O(B × 64)
Parallel:    dimension[T] × dimension[B/T] × dimension[64] → O(B × 64 / T) wall-clock
```

The total work is the same. The wall-clock time divides by the thread dimension.

---

## Boundary: The Self-Synchronization Property

The paper's key insight is about a BOUNDARY in the Huffman bitstream:

```
huffman_bitstream
│
├── boundary: synchronization points
│   │
│   │   After decoding a complete code, you're at a code boundary.
│   │   This boundary is RECOGNIZABLE - you can verify you're synced.
│   │
│   └── partition: {synced, unsynced}
│
└── dimension[C]: codes (variable-length)
    │
    └── link: each code → next code (chain of variable-length jumps)
```

The problem: If you start in the middle of the bitstream, you might land mid-code (unsynced).

The solution: Start decoding speculatively. After enough codes, you WILL hit a sync boundary (self-synchronizing property of Huffman codes).

```
speculative_decode: dimension[overlap]
│
├── boundary: sync_detected partitions {still_unsynced, now_synced}
│
└── link: sync_point → continue from verified position
```

This is why parallel Huffman decoding works - the boundary eventually resolves, regardless of where you start.

---

## Links: The Data Flow DAG

```
                    ┌─────────────┐
                    │ jpeg_bytes  │
                    └──────┬──────┘
                           │ parse
                           ▼
              ┌────────────────────────┐
              │      parsed_jpeg       │
              │  ┌──────┐  ┌────────┐  │
              │  │tables│  │scandata│  │
              │  └──┬───┘  └───┬────┘  │
              └─────┼──────────┼───────┘
                    │          │
                    │          ▼
                    │   ┌─────────────┐
                    │   │  huffman    │ ←── GPU parallel (dimension[T])
                    │   │  decode     │
                    │   └──────┬──────┘
                    │          │
                    ▼          ▼
              ┌─────────────────────────┐
              │  dct_coefficients       │
              │  + quantization_tables  │
              └────────────┬────────────┘
                           │ dequant + IDCT (fused)
                           ▼                         ←── GPU parallel
                    ┌─────────────┐
                    │ pixel_blocks│
                    │   (YCbCr)   │
                    └──────┬──────┘
                           │ color_convert
                           ▼                         ←── GPU parallel
                    ┌─────────────┐
                    │  rgb_image  │
                    └─────────────┘
```

Links show data dependencies. The DAG structure reveals:
- Tables must be parsed before Huffman decode
- Stages are sequential (can't IDCT before dequant)
- Within each stage, blocks are independent (parallel dimension)

---

## Dimension Descriptors Enable Optimization

```
dct_coefficients: dimension[B] × dimension[64]
    descriptors:
        bounds: fixed(B), fixed(64)
        contiguous: true
        aligned: 4 bytes
        homogeneous: true (all i16)
        ordered: true (block order matters for output)

    GPU optimization enabled by:
        - fixed(64): compile-time loop unrolling
        - contiguous + aligned: coalesced memory access
        - homogeneous: SIMD operations
        - bounds known: no runtime checks
```

The descriptors aren't just documentation - they're **optimization permissions**. The GPU can do things because the structure guarantees properties.

---

## What This Drawing Reveals

1. **Complexity is visible**: O(N + W×H) falls out from counting dimension elements

2. **Parallelism is a dimension**: GPU threads are just another axis of repetition

3. **The self-sync property is a boundary**: The insight that makes parallel Huffman work is literally a boundary in value space (synced vs unsynced)

4. **DAG structure shows dependencies**: What can parallelize, what must be sequential

5. **Descriptors enable optimization**: The structural properties (contiguous, aligned, fixed bounds) are what let the GPU go fast

---

## Observations

### Process = Dimension of Structures

The whole decode is one dimension[6] where each element is a complete data structure. The "algorithm" is just traversing this dimension.

### Parallelism = Orthogonal Dimension

Adding GPU parallelism doesn't change the algorithm - it adds a dimension[T] that the work is spread across. Wall-clock time divides by T.

### Boundaries Enable Everything

- Huffman code boundaries enable parsing
- Sync boundaries enable parallelism
- Block boundaries enable independent processing

### Links Reveal the DAG

The dependency structure isn't hidden in code - it's explicit in the links between intermediate structures.

---

## See Also

- [Glossary](../glossary.md) — Central definitions
- [Structural Language](../theory/structural-language.md) — B/L/D specification
- [ZIP Structure](./zip.md) — Another worked example
