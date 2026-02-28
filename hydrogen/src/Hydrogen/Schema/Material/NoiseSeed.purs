-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // material // noiseseed
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | NoiseSeed - random seed for deterministic procedural noise generation.
-- |
-- | Range: Any finite Int
-- | - Different seeds produce completely different noise patterns
-- | - Same seed always produces identical noise (deterministic)
-- | - Critical for reproducible generative work
-- |
-- | Used to initialize pseudorandom number generators in noise algorithms.
-- | Enables deterministic art - same seed = same visual output.

module Hydrogen.Schema.Material.NoiseSeed
  ( NoiseSeed
  , noiseSeed
  , unwrap
  , toInt
  , bounds
  , zero
  , fromTime
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , negate
  , show
  , (<>)
  )

import Data.Int (floor)
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // noiseseed
-- ═════════════════════════════════════════════════════════════════════════════

-- | Noise seed (any finite Int)
-- |
-- | Random seed for procedural noise. Different seeds produce different patterns.
newtype NoiseSeed = NoiseSeed Int

derive instance eqNoiseSeed :: Eq NoiseSeed
derive instance ordNoiseSeed :: Ord NoiseSeed

instance showNoiseSeed :: Show NoiseSeed where
  show (NoiseSeed s) = "seed=" <> show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a noise seed (accepts any Int)
noiseSeed :: Int -> NoiseSeed
noiseSeed n = NoiseSeed n

-- | Create seed from timestamp or other Number
fromTime :: Number -> NoiseSeed
fromTime t = NoiseSeed (floor t)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default seed (0)
zero :: NoiseSeed
zero = NoiseSeed 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: NoiseSeed -> Int
unwrap (NoiseSeed s) = s

-- | Convert to Int (passthrough for this type)
toInt :: NoiseSeed -> Int
toInt (NoiseSeed s) = s

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds (-2147483648) 2147483647 "noiseSeed" "Random seed for deterministic noise"
