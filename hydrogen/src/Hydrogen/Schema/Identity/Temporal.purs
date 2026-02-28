-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // identity // temporal
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Identified — UUID5-based wrapper with temporal identity for cache invalidation.
-- |
-- | ## Purpose
-- |
-- | At billion-agent scale, entities need:
-- | 1. **Content-addressed identity** — Same content → same UUID5
-- | 2. **Temporal versioning** — Track when content changed (generation counter)
-- | 3. **Cache invalidation** — Know when cached representations are stale
-- |
-- | The `Identified` wrapper combines these into a single type.
-- |
-- | ## Design
-- |
-- | ```purescript
-- | Identified a = 
-- |   { uuid :: UUID5         -- Deterministic ID from content hash
-- |   , generation :: Int     -- Monotonically increasing version
-- |   , value :: a            -- The wrapped value
-- |   }
-- | ```
-- |
-- | ## Invariants
-- |
-- | 1. **Determinism**: Same value produces same UUID5 (for hashable types)
-- | 2. **Monotonicity**: Generation only increases, never decreases
-- | 3. **Cache validity**: If UUID changed, cached data is invalid
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Wrap a value with identity
-- | let point = Point2D { x: 100.0, y: 200.0 }
-- | let identified = identify "my-point" point
-- | 
-- | -- Access the value
-- | let value = unwrapIdentified identified
-- | 
-- | -- Update preserves identity but bumps generation
-- | let updated = updateIdentified (\p -> p { x = p.x + 10.0 }) identified
-- | -- updated.generation == identified.generation + 1
-- | ```
-- |
-- | ## Lean4 Proof
-- |
-- | ```lean
-- | theorem determinism : ∀ x y, x = y → uuid(x) = uuid(y)
-- | ```

module Hydrogen.Schema.Identity.Temporal
  ( -- * Identified Wrapper
    Identified
  , identify
  , identifyWithNamespace
  , identifyUnsafe
  
  -- * Accessors
  , unwrapIdentified
  , getUUID
  , getGeneration
  
  -- * Modification
  , updateIdentified
  , bumpGeneration
  , setGeneration
  
  -- * Comparison
  , sameIdentity
  , sameContent
  , isNewerThan
  
  -- * Cache Helpers
  , CacheKey
  , toCacheKey
  , cacheKeyString
  
  -- * Generation Counter
  , Generation
  , generation
  , initialGeneration
  , nextGeneration
  , unwrapGeneration
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , ($)
  , (+)
  , (<)
  , (>)
  , (>=)
  , (==)
  , (<>)
  , (&&)
  , compare
  , Ordering
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Attestation.UUID5 as UUID5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // generation counter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Monotonically increasing generation counter.
-- |
-- | Used for cache invalidation. When an entity is modified, its generation
-- | increases. Cached representations with lower generations are stale.
newtype Generation = Generation Int

derive instance eqGeneration :: Eq Generation
derive instance ordGeneration :: Ord Generation

instance showGeneration :: Show Generation where
  show (Generation n) = "Gen(" <> show n <> ")"

-- | Create a generation counter
generation :: Int -> Generation
generation n = Generation (if n < 0 then 0 else n)

-- | Initial generation (0)
initialGeneration :: Generation
initialGeneration = Generation 0

-- | Next generation (increment by 1)
nextGeneration :: Generation -> Generation
nextGeneration (Generation n) = Generation (n + 1)

-- | Unwrap generation to Int
unwrapGeneration :: Generation -> Int
unwrapGeneration (Generation n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // identified wrapper
-- ═════════════════════════════════════════════════════════════════════════════

-- | A value wrapped with deterministic UUID5 identity and generation counter.
-- |
-- | ## Properties
-- |
-- | - `uuid`: Content-addressed identifier (deterministic from content)
-- | - `generation`: Monotonically increasing version number
-- | - `value`: The wrapped value
-- |
-- | Two `Identified` values with the same UUID have semantically identical
-- | content. The generation indicates which version is newer.
type Identified a =
  { uuid :: UUID5.UUID5
  , generation :: Generation
  , value :: a
  }

-- | Create an Identified value from a name.
-- |
-- | The UUID is deterministically generated from the name using the
-- | Element namespace.
-- |
-- | ```purescript
-- | let point = { x: 100.0, y: 200.0 }
-- | let identified = identify "my-point" point
-- | ```
identify :: forall a. String -> a -> Identified a
identify name value =
  { uuid: UUID5.uuid5 UUID5.nsElement name
  , generation: initialGeneration
  , value: value
  }

-- | Create an Identified value with a specific namespace.
-- |
-- | Useful when you need to avoid collisions between different domains.
identifyWithNamespace :: forall a. UUID5.UUID5 -> String -> a -> Identified a
identifyWithNamespace namespace name value =
  { uuid: UUID5.uuid5 namespace name
  , generation: initialGeneration
  , value: value
  }

-- | Create an Identified value with explicit UUID (for deserialization).
-- |
-- | Use with caution — this bypasses deterministic generation.
identifyUnsafe :: forall a. String -> Generation -> a -> Identified a
identifyUnsafe uuidString gen value =
  { uuid: UUID5.fromString uuidString
  , generation: gen
  , value: value
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the wrapped value
unwrapIdentified :: forall a. Identified a -> a
unwrapIdentified identified = identified.value

-- | Get the UUID
getUUID :: forall a. Identified a -> UUID5.UUID5
getUUID identified = identified.uuid

-- | Get the generation counter
getGeneration :: forall a. Identified a -> Generation
getGeneration identified = identified.generation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // modification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update the value, bumping the generation counter.
-- |
-- | The UUID stays the same (identity preserved), but generation increases
-- | to indicate the content has changed.
-- |
-- | ```purescript
-- | let updated = updateIdentified (\p -> p { x = p.x + 10.0 }) point
-- | -- updated.generation > point.generation
-- | ```
updateIdentified :: forall a. (a -> a) -> Identified a -> Identified a
updateIdentified f identified =
  { uuid: identified.uuid
  , generation: nextGeneration identified.generation
  , value: f identified.value
  }

-- | Bump the generation without changing the value.
-- |
-- | Useful for forcing cache invalidation.
bumpGeneration :: forall a. Identified a -> Identified a
bumpGeneration identified =
  { uuid: identified.uuid
  , generation: nextGeneration identified.generation
  , value: identified.value
  }

-- | Set a specific generation (for deserialization).
setGeneration :: forall a. Generation -> Identified a -> Identified a
setGeneration gen identified =
  { uuid: identified.uuid
  , generation: gen
  , value: identified.value
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two Identified values have the same UUID.
-- |
-- | Same UUID means same logical entity, though content may have changed.
sameIdentity :: forall a b. Identified a -> Identified b -> Boolean
sameIdentity a b = UUID5.toString (getUUID a) == UUID5.toString (getUUID b)

-- | Check if two Identified values have same UUID AND same generation.
-- |
-- | If true, the values are semantically identical (can use cached version).
sameContent :: forall a. Identified a -> Identified a -> Boolean
sameContent a b = 
  sameIdentity a b && getGeneration a == getGeneration b

-- | Check if first value is newer than second.
-- |
-- | Assumes both have same identity. Used for cache invalidation.
isNewerThan :: forall a. Identified a -> Identified a -> Boolean
isNewerThan a b = 
  sameIdentity a b && getGeneration a > getGeneration b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // cache helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | A cache key combining UUID and generation.
-- |
-- | Two cache keys are equal IFF the content is identical.
-- | Use this as key in caches/maps.
newtype CacheKey = CacheKey String

derive instance eqCacheKey :: Eq CacheKey
derive instance ordCacheKey :: Ord CacheKey

instance showCacheKey :: Show CacheKey where
  show (CacheKey k) = k

-- | Create a cache key from an Identified value.
-- |
-- | Format: "uuid:generation"
toCacheKey :: forall a. Identified a -> CacheKey
toCacheKey identified =
  CacheKey $ UUID5.toString identified.uuid <> ":" <> show (unwrapGeneration identified.generation)

-- | Convert cache key to string
cacheKeyString :: CacheKey -> String
cacheKeyString (CacheKey k) = k
