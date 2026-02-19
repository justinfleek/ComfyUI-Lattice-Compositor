# Lazy Concat Ban

**Date:** 2025-01-20  
**Status:** ✅ **ENFORCED**

---

## Banned Pattern

```haskell
-- ❌ BANNED: Lazy concat
object $ concat
  [ ["field1" .= val1]
  , if condition then ["field2" .= val2] else []
  , ["field3" .= val3]
  ]
```

---

## Required Pattern

```haskell
-- ✅ REQUIRED: Explicit list construction
instance ToJSON MyType where
  toJSON (MyType field1 field2 field3 condition) =
    let
      -- Build list explicitly - no lazy concat
      baseFields = ["field1" .= field1, "field3" .= field3]
      withConditional = if condition then ("field2" .= field2) : baseFields else baseFields
    in object withConditional
```

---

## Rationale

- `concat` uses lazy evaluation
- Explicit list construction with `:` is deterministic
- All values must be computed explicitly
- No lazy evaluation patterns allowed

---

## Files Fixed

- ✅ `src/lattice/State/Animation/Types.hs`
- ✅ `src/lattice/State/Audio.hs`
- ✅ `src/lattice/State/Playback.hs`
- ✅ `src/lattice/State/Expression.hs`

---

## CI/CD Enforcement

Add check for `concat` patterns in JSON instances:

```bash
grep -n "object \$ concat" src/**/*.hs
```

Should return zero matches.
