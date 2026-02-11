# Test Fixture: All Link Types

## Valid Links

### Inline Links
- [Valid inline](./other.md)
- [With anchor](./other.md#section-one)
- [Self anchor](#valid-links)

### Reference-Style Links
- [Valid reference][ref1]
- [Another reference][ref2]

[ref1]: ./other.md
[ref2]: ./other.md#section-one

### Autolinks
- <https://example.com>

## Invalid Links (Expected Errors)

### Broken Inline
- [Missing file](./nonexistent.md)
- [Bad anchor](./other.md#no-such-anchor)

### Broken Reference
- [Undefined ref][undefined]
- [Bad ref target][bad-ref]

[bad-ref]: ./nonexistent.md

### External URLs
- [Valid org](https://github.com/Experiential-Reality/theory)
- [Bad org](https://github.com/experiential-reality-org/bld)
- [Non-GitHub](https://example.com/some/path)

### Edge Cases
- [Text only no url]
- Links in `[inline code](ignored.md)`

```python
# Code fence - links here ignored
[ignored](./ignored.md)
```

## Section One

Target for anchor tests.
