# Maybe/Nothing Elimination Protocol

**Date:** 2025-01-20  
**Status:** 🔄 **IN PROGRESS**

---

## Core Principle

```
EVERY VALUE HAS EXPLICIT DEFAULTS
NO Maybe/Nothing
ALL VALUES ARE DETERMINISTIC
```

---

## Banned Patterns

### ❌ BANNED

```haskell
-- BANNED: Maybe types
data AudioState = AudioState
  { audioBuffer :: Maybe AudioBuffer
  , audioAnalysis :: Maybe AudioAnalysis
  }

-- BANNED: Nothing values
defaultState = AudioState
  { audioBuffer = Nothing
  , audioAnalysis = Nothing
  }

-- BANNED: Just pattern matching
case mValue of
  Nothing -> defaultValue
  Just value -> value

-- BANNED: Lazy concat in JSON instances
object $ concat
  [ ["field1" .= val1]
  , if condition then ["field2" .= val2] else []
  ]
```

---

## Required Patterns

### ✅ REQUIRED

```haskell
-- REQUIRED: Explicit defaults + Bool flags
data AudioState = AudioState
  { audioBuffer :: AudioBuffer  -- Default: duration = 0.0
  , audioBufferLoaded :: Bool  -- Explicit flag: loaded (default: False)
  , audioAnalysis :: AudioAnalysis  -- Default: all fields = 0/empty
  , audioAnalysisLoaded :: Bool  -- Explicit flag: loaded (default: False)
  }

-- REQUIRED: Explicit defaults
defaultState = AudioState
  { audioBuffer = AudioBuffer {audioBufferDuration = 0.0}
  , audioBufferLoaded = False
  , audioAnalysis = defaultAudioAnalysis
  , audioAnalysisLoaded = False
  }

-- REQUIRED: Explicit flag checks
getDuration state =
  if audioBufferLoaded state
  then audioBufferDuration (audioBuffer state)
  else 0.0  -- Explicit default
```

---

## Migration Pattern

### Step 1: Replace Maybe with explicit value + flag

**Before:**
```haskell
data State = State
  { value :: Maybe ValueType
  }
```

**After:**
```haskell
data State = State
  { value :: ValueType  -- Default: defaultValueType
  , valueSet :: Bool  -- Explicit flag: set (default: False)
  }
```

### Step 2: Update default values

**Before:**
```haskell
defaultState = State
  { value = Nothing
  }
```

**After:**
```haskell
defaultState = State
  { value = defaultValueType
  , valueSet = False
  }
```

### Step 3: Update query functions

**Before:**
```haskell
getValue :: State -> Maybe ValueType
getValue state = value state
```

**After:**
```haskell
getValue :: State -> ValueType
getValue state = value state  -- Always returns value (with defaults)

isValueSet :: State -> Bool
isValueSet state = valueSet state  -- Check if actually set
```

### Step 4: Update pattern matching

**Before:**
```haskell
case value state of
  Nothing -> defaultValue
  Just v -> v
```

**After:**
```haskell
if valueSet state
then value state
else defaultValue  -- Explicit default
```

### Step 5: Update JSON instances (NO LAZY CONCAT)

**Before:**
```haskell
instance ToJSON MyType where
  toJSON (MyType val1 val2 condition) =
    object $ concat
      [ ["field1" .= val1]
      , if condition then ["field2" .= val2] else []
      ]
```

**After:**
```haskell
instance ToJSON MyType where
  toJSON (MyType val1 val2 condition) =
    let
      -- Build list explicitly - no lazy concat
      baseFields = ["field1" .= val1]
      withConditional = if condition then ("field2" .= val2) : baseFields else baseFields
    in object withConditional
```

---

## Common Default Patterns

Use `Lattice.Utils.Defaults` for common defaults:

```haskell
import Lattice.Utils.Defaults

-- Text defaults
defaultText :: Text  -- ""
defaultTextNonEmpty :: Text  -- "default"

-- Numeric defaults
defaultDouble :: Double  -- 0.0
defaultInt :: Int  -- 0

-- Collection defaults
defaultList :: [a]  -- []
defaultHashMap :: HashMap k v  -- HM.empty

-- Boolean defaults
defaultBool :: Bool  -- False
```

---

## CI/CD Enforcement

The CI/CD pipeline now checks for banned patterns:

- **Check:** `nix build .#checks.haskell-no-maybe-check`
- **Location:** `.github/workflows/ci.yml`
- **Scope:** All `src/lattice/State/**/*.hs` files

**Violations will fail CI.**

---

## Migration Status

### ✅ COMPLETE
- `Lattice.State.Audio` - All Maybe/Nothing removed
- `Lattice.State.Animation.Types` - WorkArea Maybe removed
- `Lattice.State.Animation.WorkArea` - All functions updated

### 🔄 IN PROGRESS
- `Lattice.State.Expression` - PropertyDriver has Maybe fields
- `Lattice.State.Layer.*` - Multiple Maybe fields
- `Lattice.State.Keyframe.*` - Multiple Maybe fields

### ⏳ PENDING
- All other State modules (50+ files)
- Services modules (20+ files)
- Types modules (37+ files)

---

## Examples

### Example 1: AudioBuffer

**Before:**
```haskell
data AudioState = AudioState
  { audioBuffer :: Maybe AudioBuffer
  }

duration state = case audioBuffer state of
  Nothing -> 0.0
  Just buf -> audioBufferDuration buf
```

**After:**
```haskell
data AudioState = AudioState
  { audioBuffer :: AudioBuffer
  , audioBufferLoaded :: Bool
  }

duration state =
  if audioBufferLoaded state
  then audioBufferDuration (audioBuffer state)
  else 0.0
```

### Example 2: Work Area

**Before:**
```haskell
data AnimationState = AnimationState
  { workAreaStart :: Maybe Double
  , workAreaEnd :: Maybe Double
  }

effectiveStart state = case workAreaStart state of
  Nothing -> 0.0
  Just start -> start
```

**After:**
```haskell
data AnimationState = AnimationState
  { workAreaStart :: Double
  , workAreaStartSet :: Bool
  , workAreaEnd :: Double
  , workAreaEndSet :: Bool
  }

effectiveStart state =
  if workAreaStartSet state
  then workAreaStart state
  else 0.0
```

---

## Verification

After migration:

1. ✅ No `Maybe` in type signatures (except imports)
2. ✅ No `Nothing` in values
3. ✅ No `Just` in pattern matches
4. ✅ All values have explicit defaults
5. ✅ All functions are deterministic
6. ✅ No `concat` in JSON instances (use explicit list construction)
7. ✅ CI/CD check passes

---

## Next Steps

1. Continue migrating State modules systematically
2. Migrate Services modules
3. Migrate Types modules
4. Update all tests
5. Verify CI/CD check catches violations
