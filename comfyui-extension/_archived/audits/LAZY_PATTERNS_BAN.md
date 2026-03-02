# Lazy Patterns Ban

**Date:** 2025-01-20  
**Status:** ✅ **ENFORCED**

---

## Banned Patterns

### ❌ BANNED: Lazy List Concatenation

```haskell
-- BANNED: concat in JSON instances
object $ concat
  [ ["field1" .= val1]
  , if condition then ["field2" .= val2] else []
  ]

-- BANNED: maybe [] pattern
maybe [] (\x -> ["field" .= x]) mValue

-- BANNED: ++ operator (lazy list concatenation)
list1 ++ list2
```

### ❌ BANNED: Lazy Text Concatenation

```haskell
-- BANNED: T.concat
T.concat [text1, text2, text3]

-- BANNED: T.cons + T.concat
T.cons '#' (T.concat [hex1, hex2, hex3])
```

---

## Required Patterns

### ✅ REQUIRED: Explicit List Construction

```haskell
-- REQUIRED: Explicit list construction with :
instance ToJSON MyType where
  toJSON (MyType val1 val2 condition) =
    let
      -- Build list explicitly - no lazy concat
      baseFields = ["field1" .= val1]
      withConditional = if condition then ("field2" .= val2) : baseFields else baseFields
    in object withConditional
```

### ✅ REQUIRED: Explicit Text Construction

```haskell
-- REQUIRED: Explicit Text concatenation with <>
let
  text1 = "hello"
  text2 = "world"
  combined = text1 <> text2
in combined
```

---

## Rationale

- `concat` uses lazy evaluation
- `++` operator is lazy list concatenation
- `T.concat` uses lazy evaluation for Text
- Explicit construction with `:` and `<>` is deterministic
- All values must be computed explicitly
- No lazy evaluation patterns allowed

---

## Files Fixed

### JSON Instances (Fixed)
- ✅ `src/lattice/State/Animation/Types.hs`
- ✅ `src/lattice/State/Audio.hs`
- ✅ `src/lattice/State/Playback.hs`
- ✅ `src/lattice/State/Expression.hs`
- ✅ `src/lattice/State/Selection.hs`
- ✅ `src/lattice/State/Asset.hs` (3 instances)
- ✅ `src/lattice/State/Layer/Types.hs`
- ✅ `src/lattice/State/Preset.hs`

### Text Operations (Fixed)
- ✅ `src/lattice/State/TextAnimator.hs` (2 instances)
- ✅ `src/lattice/State/Cache.hs`

---

## Remaining Patterns

### List Operations (`++`)
Some `++` patterns remain in list manipulation code (e.g., `before ++ [item] ++ after`). These are harder to replace without making code very verbose. Consider on a case-by-case basis.

### Helper Functions (`concatMap`)
`concatMap` in helper functions (e.g., `Project.hs`) is acceptable if not in JSON serialization paths.

---

## CI/CD Enforcement

Add check for lazy patterns:

```bash
# Check for concat in JSON instances
grep -n "object \$ concat" src/**/*.hs

# Check for T.concat
grep -n "T\.concat" src/**/*.hs

# Should return zero matches
```
