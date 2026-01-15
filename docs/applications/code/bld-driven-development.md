---
status: VALIDATED
layer: application
depends_on:
  - ../../mathematics/foundations/factorization-calculus.md
  - ../../meta/discovery-method.md
  - refactoring.md
used_by:
  - code-generation-cli.md
  - README.md
  - code-generation.md
  - ../../paths/practitioner.md
  - ../../README.md
---

# BLD-Driven Development

> **Status**: Foundational

## Quick Summary (D≈7 Human Traversal)

**BLD-driven development in 7 steps:**

1. **Find structure first** — Before writing code, answer: What partitions behavior? What depends on what? What repeats?
2. **Boundaries should be explicit** — Use enums and dispatch tables, never scatter the same condition across multiple locations
3. **Dependencies should form a DAG** — If you can't draw it as a directed acyclic graph, there's hidden state
4. **Dimensions should be homogeneous** — If elements need different handling, that's a hidden boundary—make it explicit
5. **FACTOR operation decomposes** — `S → S₁ × S₂ × ... × Sₙ` terminates at irreducible B × L × D primitives
6. **D×L scaling reveals hidden B** — If adding more items makes code significantly more complex, you've hidden a boundary
7. **BLD code is naturally concurrent** — Explicit B (no races), DAG L (no deadlocks), homogeneous D (parallel-safe)

| Component | BLD Mapping |
|-----------|-------------|
| Modes/states | B: explicit enum or dispatch table |
| Data flow | L: explicit in function signatures, DAG structure |
| Collections | D: homogeneous elements, uniform handling |
| Hidden state | Scattered B, cyclic L, or heterogeneous D |
| Concurrency safety | Explicit B + DAG L + homogeneous D |

---

A methodology for writing better code by designing with structure from the start.

---

## The Core Idea

**Before writing code, find the structure.**

BLD-driven development means applying the three questions *before* implementation, not after. Instead of writing code and then refactoring to make state explicit, design with explicit structure from the beginning.

```
Traditional:     Write code → Find bugs → Refactor → Repeat
BLD-Driven:      Find structure → Write aligned code → Less friction
```

---

## Formal Operation: FACTOR

The mathematical foundation of BLD-driven development is the **FACTOR** operation:

```
FACTOR : S → S₁ × S₂ × ... × Sₙ

Properties:
  1. |Sᵢ| < |S|      (decomposition into smaller pieces)
  2. Π Sᵢ ≅ S        (behavior preserved)
  3. Terminates      (reaches irreducible B × L × D)
```

**The three factorization rules**:

| Rule | Input | Output | What It Reveals |
|------|-------|--------|-----------------|
| **B-Factor** | Scattered if/elif | Sum type + dispatch | Boundary |
| **L-Factor** | Cycle A→B→C→A | Shared state + DAG | Links |
| **D-Factor** | Mixed collection | Homogeneous products | Dimension |

BLD-driven development applies these rules **proactively** — identify structure before writing code, rather than discovering it through refactoring afterward.

See [Factorization Calculus](../../mathematics/foundations/factorization-calculus.md) for formal definitions.

---

## The Pre-Implementation Checklist

Before writing any significant code, answer these questions:

### 1. What are the Boundaries?

**Ask**: "What values will partition behavior in this system?"

- What modes or states exist?
- What error conditions branch differently?
- What configuration options change behavior?
- Where are the type boundaries?

**Output**: A list of boundaries and what they partition.

**Design decision**: Each boundary should be explicit in the code—an enum, a discriminated union, a dispatch table. Never scatter the same boundary check across multiple locations.

### 2. What are the Links?

**Ask**: "What will depend on what?"

- What data flows where?
- What functions call what functions?
- What modules import what modules?
- What external systems are referenced?

**Output**: A dependency graph (should be a DAG).

**Design decision**: Dependencies should be explicit in function signatures. If you can't draw the dependency graph as a clean DAG, redesign before implementing.

### 3. What are the Dimensions?

**Ask**: "What repeats?"

- What collections exist?
- What loops will iterate over what?
- What parallel instances exist?
- What layers or stages process the same structure?

**Output**: A list of dimensions with their extent and element type.

**Design decision**: Each dimension should be homogeneous. If elements in a collection need different handling, that's a hidden boundary—make it explicit.

---

## Design Principles

### Principle 1: Boundaries First

Design the partitions before the logic. Know your modes, your error cases, your configuration space *before* writing the code that handles them.

**Bad**: Start writing code, add `if` statements as edge cases appear.
```python
def process(data):
    result = transform(data)
    if data.special_case:      # Added later
        result = special_transform(data)
    if data.another_case:       # Added even later
        result = another_transform(data)
    return result
```

**Good**: Enumerate all cases first, then implement.
```python
class DataKind(Enum):
    NORMAL = auto()
    SPECIAL = auto()
    ANOTHER = auto()

TRANSFORMS = {
    DataKind.NORMAL: transform,
    DataKind.SPECIAL: special_transform,
    DataKind.ANOTHER: another_transform,
}

def process(data):
    return TRANSFORMS[data.kind](data)
```

### Principle 2: Dependencies as DAG

If you can't draw the dependency graph before implementing, you don't understand the problem yet.

**Bad**: Circular dependencies emerge during implementation.
```python
# module_a.py
from module_b import helper_b
def func_a(): ...

# module_b.py
from module_a import func_a  # Circular!
def helper_b(): ...
```

**Good**: Design the DAG first, implement to match.
```
module_shared (no dependencies)
    ↑
module_a (depends on shared)
    ↑
module_b (depends on a, shared)
    ↑
module_main (depends on b)
```

### Principle 3: Uniform Dimensions

Collections should contain homogeneous elements. If you find yourself checking types inside a loop, you have a hidden boundary.

**Bad**: Heterogeneous collection.
```python
def process_items(items):
    for item in items:
        if isinstance(item, TypeA):
            process_a(item)
        elif isinstance(item, TypeB):
            process_b(item)
```

**Good**: Separate dimensions by type.
```python
def process_items(items_a: list[TypeA], items_b: list[TypeB]):
    for item in items_a:
        process_a(item)
    for item in items_b:
        process_b(item)
```

Or use a common interface (boundary at the type level, not in the loop):
```python
def process_items(items: list[Processable]):
    for item in items:
        item.process()  # Dispatch happens in the type system
```

---

## The BLD Design Template

For any new feature or system, fill out this template before coding:

```
Feature: [name]

BOUNDARIES (what partitions behavior):
- B1: [description] → partitions into {case1, case2, ...}
- B2: [description] → partitions into {...}

LINKS (what depends on what):
- L1: [source] → [target]
- L2: [source] → [target]
Verify: Is this a DAG? [yes/no]

DIMENSIONS (what repeats):
- D1: [name] with extent [N] of type [T]
- D2: [name] with extent [M] of type [U]
Verify: Are elements homogeneous? [yes/no for each]

ALIGNMENT CHECK:
- Does code structure match domain structure? [yes/no]
- Are all boundaries explicit (enums, dispatch tables)? [yes/no]
- Are all dependencies in function signatures? [yes/no]
```

---

## Example: Designing a Notification System

**Feature**: Send notifications to users via email, SMS, or push.

### Step 1: Find Boundaries

What partitions behavior?
- **Channel type**: email vs SMS vs push (different delivery logic)
- **User preference**: opted-in vs opted-out (don't send to opted-out)
- **Message priority**: urgent vs normal (affects retry behavior)

```python
class Channel(Enum):
    EMAIL = auto()
    SMS = auto()
    PUSH = auto()

class Priority(Enum):
    URGENT = auto()
    NORMAL = auto()
```

### Step 2: Find Links

What depends on what?
- `send_notification` → `validate_user_preference`
- `send_notification` → `channel_dispatcher`
- `channel_dispatcher` → `email_sender`, `sms_sender`, `push_sender`
- `*_sender` → external services

```
validate_user_preference
         │
send_notification ──→ channel_dispatcher
                            │
                   ┌────────┼────────┐
                   ▼        ▼        ▼
              email_sender sms_sender push_sender
                   │        │        │
                   ▼        ▼        ▼
              SMTP API   Twilio   Firebase
```

DAG? Yes.

### Step 3: Find Dimensions

What repeats?
- **D1**: `users` - list of recipients (extent: variable, type: User)
- **D2**: `channels` - channels per user preference (extent: 1-3, type: Channel)
- **D3**: `retry_attempts` - for failed sends (extent: 3, type: int)

Are elements homogeneous?
- D1: All Users have same structure ✓
- D2: All Channels handled by same dispatcher interface ✓
- D3: All retries follow same logic ✓

### Step 4: Write Aligned Code

```python
@dataclass
class Notification:
    user: User
    message: str
    channel: Channel
    priority: Priority

# Boundary: explicit dispatch table
SENDERS: dict[Channel, Callable[[Notification], bool]] = {
    Channel.EMAIL: send_email,
    Channel.SMS: send_sms,
    Channel.PUSH: send_push,
}

# Link: dependencies in signature
def send_notification(
    notification: Notification,
    check_preference: Callable[[User, Channel], bool],
    sender_dispatch: dict[Channel, Callable],
) -> bool:
    # Boundary: user preference
    if not check_preference(notification.user, notification.channel):
        return False  # Opted out

    sender = sender_dispatch[notification.channel]
    return sender(notification)

# Dimension: batch sending with uniform elements
def send_batch(notifications: list[Notification]) -> list[bool]:
    return [send_notification(n, check_pref, SENDERS) for n in notifications]
```

---

## Anti-Patterns to Avoid

### Anti-Pattern 1: Scattered Boundaries

**Symptom**: Same condition checked in multiple places.

```python
# BAD: Boundary scattered
if user.is_premium:
    rate_limit = 1000
# ... 50 lines later ...
if user.is_premium:
    feature_x_enabled = True
# ... 100 lines later ...
if user.is_premium:
    support_priority = "high"
```

**Fix**: Consolidate boundary into one place.

```python
# GOOD: Boundary explicit
@dataclass
class UserTier:
    rate_limit: int
    feature_x: bool
    support_priority: str

TIERS = {
    "premium": UserTier(1000, True, "high"),
    "free": UserTier(100, False, "normal"),
}

tier = TIERS[user.tier]
```

### Anti-Pattern 2: Hidden Dependencies

**Symptom**: Functions access global state or have non-obvious side effects.

```python
# BAD: Hidden link to global state
config = None  # Set somewhere else

def process():
    if config.debug:  # Where does config come from?
        log_debug()
```

**Fix**: Make all dependencies explicit in signatures.

```python
# GOOD: Explicit link
def process(config: Config):
    if config.debug:
        log_debug()
```

### Anti-Pattern 3: Heterogeneous Dimensions

**Symptom**: Type checking inside loops.

```python
# BAD: Hidden boundary inside dimension
for item in items:
    if item.type == "A":
        handle_a(item)
    else:
        handle_b(item)
```

**Fix**: Either separate dimensions or use polymorphism.

```python
# GOOD: Boundary at type level
for item in items:
    item.handle()  # Polymorphic dispatch

# OR: Separate dimensions
for item in items_a:
    handle_a(item)
for item in items_b:
    handle_b(item)
```

### Anti-Pattern 4: Premature Abstraction

**Symptom**: Creating structure that doesn't exist in the domain.

```python
# BAD: Abstraction without real dimension
class AbstractHandlerFactoryBuilder:
    def build_factory(self): ...

# When there's only ever one handler
```

**Fix**: Only create dimensions that exist. Don't add structure for hypothetical future requirements.

```python
# GOOD: Match actual structure
def handle(request):
    # Just do the thing
```

---

## D×L Scaling: A Design Heuristic

The BLD principle that "D multiplies L, not B" gives a useful design heuristic:

**If adding more items (D) makes the code significantly more complex, you've hidden a boundary.**

Good D×L scaling:
```python
# Adding more users doesn't add complexity
for user in users:  # D
    send_notification(user, channel)  # L
```

Bad scaling (hidden B):
```python
# Adding users reveals hidden complexity
for user in users:
    if user.region == "EU":
        send_gdpr_compliant(user)
    elif user.region == "US":
        send_standard(user)
    # ... complexity grows with user diversity
```

**Fix**: Extract the hidden boundary (region).

```python
# Region is a boundary, handle it explicitly
REGION_SENDERS = {
    "EU": send_gdpr_compliant,
    "US": send_standard,
}

for user in users:
    REGION_SENDERS[user.region](user)
```

---

## Why BLD Code is Naturally Concurrent

Code written with BLD principles is inherently parallelizable. This isn't a side effect—it's structural.

### The Three Sources of Concurrency Bugs

Most concurrency bugs come from hidden structure:

| Bug Type | Root Cause | BLD Violation |
|----------|------------|---------------|
| **Race condition** | Hidden shared state | Scattered B (boundary not explicit) |
| **Deadlock** | Circular wait | Cyclic L (dependencies not a DAG) |
| **Data race** | Hidden mutation | Implicit L (dependency not in signature) |

BLD-driven code avoids all three by making structure explicit.

### Dimensions Are Embarrassingly Parallel

When dimensions are homogeneous, every element can be processed independently:

```python
# Sequential (but parallelizable)
results = [process(item) for item in items]

# Parallel (trivial transformation)
results = parallel_map(process, items)

# Why it works: D is homogeneous, no hidden B inside the loop
```

If you find yourself unable to parallelize a loop, you have a hidden boundary or link:

```python
# NOT parallelizable - hidden link (accumulator)
total = 0
for item in items:
    total += item.value  # Each iteration depends on previous

# Fix: Make the link explicit, use reduction
totals = parallel_map(lambda x: x.value, items)
total = reduce(add, totals)  # Explicit tree reduction
```

### DAG Links Define the Parallelism Frontier

When dependencies form a DAG, you can read parallelism directly from the graph:

```
    A
   / \
  B   C     ← B and C can run in parallel (no link between them)
   \ /
    D       ← D waits for both B and C
```

```python
# The DAG tells you exactly what's parallel
async def process():
    a = await step_a()
    b, c = await asyncio.gather(
        step_b(a),  # These run in parallel
        step_c(a),  # because no L connects them
    )
    d = await step_d(b, c)
    return d
```

If your code can't be parallelized this way, you have hidden dependencies:

```python
# Hidden link prevents parallelism
shared_cache = {}

def step_b(a):
    shared_cache["b"] = compute(a)  # Hidden write

def step_c(a):
    if "b" in shared_cache:  # Hidden read - race condition!
        ...
```

**Fix**: Make the link explicit.

```python
# Explicit links - parallelism is safe
def step_b(a) -> BResult:
    return compute(a)  # Pure function, no hidden state

def step_c(a) -> CResult:
    return compute(a)  # Pure function, no hidden state

def step_d(b: BResult, c: CResult) -> DResult:
    # Link to b is explicit in signature
    ...
```

### Boundaries Isolate State

Explicit boundaries create natural isolation zones:

```python
# Each partition is isolated - can process in parallel
HANDLERS = {
    "type_a": handle_a,  # Isolated handler
    "type_b": handle_b,  # Isolated handler
    "type_c": handle_c,  # Isolated handler
}

# Parallel by type (each boundary partition is independent)
async def process_all(items):
    by_type = group_by(items, key=lambda x: x.type)
    return await asyncio.gather(*[
        process_partition(t, items)
        for t, items in by_type.items()
    ])
```

Hidden boundaries create hidden sharing:

```python
# Hidden boundary = hidden sharing = race condition
def process(item):
    if item.type == "type_a":
        global_counter_a += 1  # Hidden shared state
    elif item.type == "type_b":
        global_counter_b += 1  # Hidden shared state
```

### The Concurrency Theorem

**BLD-aligned code is maximally parallelizable.**

| BLD Property | Concurrency Implication |
|--------------|------------------------|
| Explicit B (boundaries) | No hidden shared state → no race conditions |
| DAG L (links) | No circular dependencies → no deadlocks |
| Explicit L (in signatures) | No hidden mutation → no data races |
| Homogeneous D (dimensions) | Independent elements → embarrassingly parallel |

This is why functional programming enables parallelism—it enforces explicit structure. BLD gives you the same benefits in any paradigm by making structure visible.

### Practical Concurrency Checklist

Before parallelizing, verify:

- [ ] **All boundaries explicit?** No scattered if/else on the same condition
- [ ] **Dependencies are DAG?** Can draw the graph with no cycles
- [ ] **All links in signatures?** No global state, no hidden side effects
- [ ] **Dimensions homogeneous?** No type-checking inside loops

If all four are true, parallelization is mechanical:
1. Find independent nodes in the DAG → run in parallel
2. Find homogeneous dimensions → map in parallel
3. Find isolated boundary partitions → process in parallel

---

## Testing with BLD

### Boundary Testing

For each boundary, test:
- All partitions are covered
- Boundary transitions work correctly
- Invalid inputs are handled

```python
@pytest.mark.parametrize("channel", list(Channel))
def test_all_channels_handled(channel):
    """Every boundary partition has a handler."""
    assert channel in SENDERS
```

### Link Testing

For each link, test:
- Dependency is mockable
- Direction is correct (A depends on B, not reverse)
- DAG property holds (no cycles)

```python
def test_send_notification_uses_injected_sender():
    """Link to sender is explicit and mockable."""
    mock_sender = Mock(return_value=True)
    result = send_notification(notif, check_pref, {Channel.EMAIL: mock_sender})
    mock_sender.assert_called_once()
```

### Dimension Testing

For each dimension, test:
- Empty case works
- Single element works
- Multiple elements work (verify D×L scaling)

```python
def test_batch_send_scales_linearly():
    """D×L: Cost should scale with count."""
    results_10 = send_batch(notifications[:10])
    results_100 = send_batch(notifications[:100])
    # Both should complete, complexity is O(n) not O(n²)
```

---

## Summary

BLD-driven development is about finding structure before writing code:

| Phase | Action | Output |
|-------|--------|--------|
| **Design** | Ask the three questions | B/L/D lists |
| **Verify** | Check alignment | DAG diagram, homogeneity check |
| **Implement** | Write code that matches structure | Aligned code |
| **Test** | Verify B partitions, L dependencies, D scaling | Passing tests |

The goal: Code structure should mirror domain structure. When they align, the code is readable, testable, and performant. When they misalign, you get hidden state, scattered conditions, and accidental complexity.

**Design with structure. Write aligned code. Avoid refactoring later.**

---

## See Also

- [Code Generation](./code-generation.md) — Generate code from BLD structures
- [Cross-Language Compilation](./cross-language-compilation.md) — Haskell → Python/C via BLD
- [Glossary](../../glossary.md) — Central definitions
- [Discovery Method](../../meta/discovery-method.md) — The three questions
- [Refactoring](./refactoring.md) — Fixing existing code with BLD
- [Lie Correspondence](../../mathematics/lie-theory/lie-correspondence.md) — Why BLD works
