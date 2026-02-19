-- | Lattice.Services.Particles.SeededRandom - Seeded Random Number Generator
-- |
-- | Uses mulberry32 algorithm for deterministic, reproducible randomness.
-- | This is CRITICAL for particle system determinism - same seed always
-- | produces the same sequence of numbers.
-- |
-- | Core bitwise operations delegated to JS FFI for correctness.
-- |
-- | Source: ui/src/services/particles/SeededRandom.ts

module Lattice.Services.Particles.SeededRandom
  ( -- * Types
    RngState(..)
  , Point2D(..)
  , Point3D(..)
    -- * Core Operations
  , create, reset, setSeed
  , getState, setState, getSeed
    -- * Random Generation
  , next, nextN
    -- * Range Operations
  , range, int, variance, bool
    -- * Angular Operations
  , angle
    -- * Geometric Distributions
  , inCircle, onSphere
    -- * Statistical Distributions
  , gaussian
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Tuple (Tuple(..))
import Data.List (List, reverse)
import Data.List as List
import Data.Int (floor, toNumber) as Int
import Math (pi, sqrt, cos, sin, log, acos) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Random generator state
-- | Note: Using Number for state since PureScript doesn't have native UInt32
newtype RngState = RngState { state :: Number, initialSeed :: Number }

derive instance Generic RngState _
derive newtype instance Eq RngState
instance Show RngState where show = genericShow

-- | 2D point
newtype Point2D = Point2D { x :: Number, y :: Number }

derive instance Generic Point2D _
derive newtype instance Eq Point2D
instance Show Point2D where show = genericShow

-- | 3D point
newtype Point3D = Point3D { x :: Number, y :: Number, z :: Number }

derive instance Generic Point3D _
derive newtype instance Eq Point3D
instance Show Point3D where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Max 32-bit unsigned value
maxUint32 :: Number
maxUint32 = 4294967296.0

-- ────────────────────────────────────────────────────────────────────────────
-- Foreign imports for correct bitwise operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Foreign import for bitwise XOR (unused now but kept for API compat)
foreign import xorBitwise :: Int -> Int -> Int

-- | Foreign import for bitwise OR (unused now but kept for API compat)
foreign import orBitwise :: Int -> Int -> Int

-- | Core mulberry32 step - implemented in JS for correct bitwise behavior
foreign import mulberry32NextImpl :: Number -> { value :: Number, newState :: Number }

-- | Wrap to uint32 using JS >>> 0
foreign import wrap32Impl :: Number -> Number

-- ────────────────────────────────────────────────────────────────────────────
-- Core Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Create new RNG with seed
create :: Number -> RngState
create seed = RngState { state: wrap32Impl seed, initialSeed: wrap32Impl seed }

-- | Reset to initial seed
reset :: RngState -> RngState
reset (RngState rng) = RngState { state: rng.initialSeed, initialSeed: rng.initialSeed }

-- | Set new seed
setSeed :: Number -> RngState -> RngState
setSeed seed _ = create seed

-- | Get current state for checkpointing
getState :: RngState -> Number
getState (RngState rng) = rng.state

-- | Restore state from checkpoint
setState :: Number -> RngState -> RngState
setState s (RngState rng) = RngState { state: wrap32Impl s, initialSeed: rng.initialSeed }

-- | Get initial seed
getSeed :: RngState -> Number
getSeed (RngState rng) = rng.initialSeed

-- ────────────────────────────────────────────────────────────────────────────
-- Mulberry32 Algorithm
-- ────────────────────────────────────────────────────────────────────────────

-- | Get next random number in [0, 1)
-- | Returns (value, newState)
next :: RngState -> Tuple Number RngState
next (RngState rng) =
  let result = mulberry32NextImpl rng.state
  in Tuple result.value (RngState { state: result.newState, initialSeed: rng.initialSeed })

-- | Generate n random numbers in [0, 1)
nextN :: Int -> RngState -> Tuple (List Number) RngState
nextN n rng = go n List.Nil rng
  where
    go :: Int -> List Number -> RngState -> Tuple (List Number) RngState
    go 0 acc r = Tuple (reverse acc) r
    go k acc r =
      let Tuple v r' = next r
      in go (k - 1) (List.Cons v acc) r'

-- ────────────────────────────────────────────────────────────────────────────
-- Range Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Get random in range [min, max]
range :: Number -> Number -> RngState -> Tuple Number RngState
range minV maxV rng =
  let Tuple r rng' = next rng
  in Tuple (minV + r * (maxV - minV)) rng'

-- | Get random integer in range [min, max] inclusive
int :: Int -> Int -> RngState -> Tuple Int RngState
int minV maxV rng =
  let Tuple r rng' = range (Int.toNumber minV) (Int.toNumber maxV + 1.0) rng
  in Tuple (Int.floor r) rng'

-- | Get random value with variance: base + random(-variance, +variance)
variance :: Number -> Number -> RngState -> Tuple Number RngState
variance base var rng =
  let Tuple r rng' = next rng
  in Tuple (base + (r - 0.5) * 2.0 * var) rng'

-- | Get random boolean with given probability of true
bool :: Number -> RngState -> Tuple Boolean RngState
bool probability rng =
  let Tuple r rng' = next rng
  in Tuple (r < probability) rng'

-- ────────────────────────────────────────────────────────────────────────────
-- Angular Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Get random angle in radians [0, 2*PI)
angle :: RngState -> Tuple Number RngState
angle rng =
  let Tuple r rng' = next rng
  in Tuple (r * Math.pi * 2.0) rng'

-- ────────────────────────────────────────────────────────────────────────────
-- Geometric Distributions
-- ────────────────────────────────────────────────────────────────────────────

-- | Get random point in unit circle
inCircle :: RngState -> Tuple Point2D RngState
inCircle rng =
  let Tuple a rng1 = angle rng
      Tuple r rng2 = next rng1
      radius = Math.sqrt r
  in Tuple (Point2D { x: radius * Math.cos a, y: radius * Math.sin a }) rng2

-- | Get random point on unit sphere
onSphere :: RngState -> Tuple Point3D RngState
onSphere rng =
  let Tuple theta rng1 = angle rng
      Tuple u rng2 = next rng1
      phi = Math.acos (2.0 * u - 1.0)
      sinPhi = Math.sin phi
  in Tuple (Point3D { x: sinPhi * Math.cos theta
                    , y: sinPhi * Math.sin theta
                    , z: Math.cos phi }) rng2

-- ────────────────────────────────────────────────────────────────────────────
-- Statistical Distributions
-- ────────────────────────────────────────────────────────────────────────────

-- | Get random number from Gaussian/normal distribution
-- | Uses Box-Muller transform
gaussian :: Number -> Number -> RngState -> Tuple Number RngState
gaussian mean stdDev rng =
  let stdDev' = if stdDev == 0.0 then 1.0 else stdDev
      Tuple u1 rng1 = next rng
      Tuple u2 rng2 = next rng1
      -- Prevent log(0)
      u1' = if u1 == 0.0 then 1e-10 else u1
      -- Box-Muller transform
      z = Math.sqrt (-2.0 * Math.log u1') * Math.cos (2.0 * Math.pi * u2)
  in Tuple (mean + z * stdDev') rng2
