# Proof: `findKeyframeIndex` Fallback is Impossible

**Date:** 2025-01-20  
**Status:** ✅ **PROVEN** - Fallback case is mathematically impossible

---

## Theorem

For `findKeyframeIndex keyframes frame` where `length keyframes >= 2`:

**Given:**
- `l >= 0`
- `h <= length keyframes - 2`
- `l <= h`
- `mid = (l + h) div 2`

**Prove:** `drop mid keyframes` has length >= 2 AND `drop (mid + 1) keyframes` has length >= 1

---

## Proof

### Invariants

**I1:** `l >= 0` (initial: `l = 0`, maintained by search)
**I2:** `h <= length keyframes - 2` (initial: `h = length keyframes - 2`, maintained by search)
**I3:** `l <= h` (when entering `otherwise` branch)

### Step 1: Bound on `mid`

From `mid = (l + h) div 2`:
```
l <= mid <= h  (by definition of integer division)
```

From I2 and I3:
```
mid <= h <= length keyframes - 2
```

**Therefore:** `mid <= length keyframes - 2` ✓

### Step 2: Bound on `mid + 1`

From Step 1:
```
mid <= length keyframes - 2
```

Adding 1:
```
mid + 1 <= length keyframes - 1
```

**Therefore:** `mid + 1 <= length keyframes - 1` ✓

### Step 3: Length of `drop mid keyframes`

By definition: `length (drop n xs) = max 0 (length xs - n)`

From Step 1: `mid <= length keyframes - 2`

Therefore:
```
length (drop mid keyframes) = length keyframes - mid
                            >= length keyframes - (length keyframes - 2)
                            >= 2
```

**Therefore:** `length (drop mid keyframes) >= 2` ✓

### Step 4: Length of `drop (mid + 1) keyframes`

From Step 2: `mid + 1 <= length keyframes - 1`

Therefore:
```
length (drop (mid + 1) keyframes) = length keyframes - (mid + 1)
                                   >= length keyframes - (length keyframes - 1)
                                   >= 1
```

**Therefore:** `length (drop (mid + 1) keyframes) >= 1` ✓

---

## QED

**Both `drop mid keyframes` and `drop (mid + 1) keyframes` are guaranteed non-empty.**

The `[]` cases in pattern matching are **mathematically impossible** and serve only as:
1. Type system exhaustiveness requirement (Haskell requires all cases)
2. Runtime assertion if invariants are violated (logic error detection)

If `error` executes, it indicates a **logic error** in the binary search implementation, not a valid runtime case.
