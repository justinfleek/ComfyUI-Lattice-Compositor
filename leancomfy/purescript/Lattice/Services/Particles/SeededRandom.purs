-- | Lattice.Services.Particles.SeededRandom - Seeded Random Number Generator
-- |
-- | Uses mulberry32 algorithm for deterministic, reproducible randomness.
-- | This is CRITICAL for particle system determinism - same seed always
-- | produces the same sequence of numbers.
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

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Mulberry32 magic constant
mulberry32Magic :: Number
mulberry32Magic = 1831565813.0  -- 0x6D2B79F5

-- | Max 32-bit unsigned value
maxUint32 :: Number
maxUint32 = 4294967296.0

--------------------------------------------------------------------------------
-- Bit Operations (simulated for Numbers representing UInt32)
--------------------------------------------------------------------------------

-- | Simulate unsigned right shift
shr :: Number -> Int -> Number
shr n bits =
  let intN = Int.floor n
      shifted = intN / (2 `pow` bits)
  in Int.toNumber (Int.floor shifted)
  where
    pow :: Int -> Int -> Int
    pow _ 0 = 1
    pow b e = b * pow b (e - 1)

-- | Simulate XOR
xor' :: Number -> Number -> Number
xor' a b =
  let intA = Int.floor a
      intB = Int.floor b
  in Int.toNumber (intA `xorInt` intB)
  where
    xorInt :: Int -> Int -> Int
    xorInt = xorBitwise

-- | Foreign import for bitwise XOR
foreign import xorBitwise :: Int -> Int -> Int

-- | Simulate bitwise OR
bor :: Number -> Number -> Number
bor a b =
  let intA = Int.floor a
      intB = Int.floor b
  in Int.toNumber (intA `orInt` intB)
  where
    orInt :: Int -> Int -> Int
    orInt = orBitwise

-- | Foreign import for bitwise OR
foreign import orBitwise :: Int -> Int -> Int

-- | Wrap to 32-bit unsigned range
wrap32 :: Number -> Number
wrap32 n =
  let m = n `mod` maxUint32
  in if m < 0.0 then m + maxUint32 else m

-- | Simulate 32-bit integer multiply
imul :: Number -> Number -> Number
imul a b = wrap32 (Int.toNumber (Int.floor a) * Int.toNumber (Int.floor b))

--------------------------------------------------------------------------------
-- Core Operations
--------------------------------------------------------------------------------

-- | Create new RNG with seed
create :: Number -> RngState
create seed = RngState { state: wrap32 seed, initialSeed: wrap32 seed }

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
setState s (RngState rng) = RngState { state: wrap32 s, initialSeed: rng.initialSeed }

-- | Get initial seed
getSeed :: RngState -> Number
getSeed (RngState rng) = rng.initialSeed

--------------------------------------------------------------------------------
-- Mulberry32 Algorithm
--------------------------------------------------------------------------------

-- | Get next random number in [0, 1)
-- | Returns (value, newState)
next :: RngState -> Tuple Number RngState
next (RngState rng) =
  let newState = wrap32 (rng.state + mulberry32Magic)
      t1 = xor' newState (shr newState 15)
      t2 = imul t1 (bor t1 1.0)
      t3 = xor' t2 (wrap32 (t2 + imul (xor' t2 (shr t2 7)) (bor t2 61.0)))
      t4 = xor' t3 (shr t3 14)
      value = t4 / maxUint32
  in Tuple value (RngState { state: newState, initialSeed: rng.initialSeed })

-- | Generate n random numbers in [0, 1)
nextN :: Int -> RngState -> Tuple (List Number) RngState
nextN n rng = go n List.Nil rng
  where
    go :: Int -> List Number -> RngState -> Tuple (List Number) RngState
    go 0 acc r = Tuple (reverse acc) r
    go k acc r =
      let Tuple v r' = next r
      in go (k - 1) (List.Cons v acc) r'

--------------------------------------------------------------------------------
-- Range Operations
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Angular Operations
--------------------------------------------------------------------------------

-- | Get random angle in radians [0, 2*PI)
angle :: RngState -> Tuple Number RngState
angle rng =
  let Tuple r rng' = next rng
  in Tuple (r * Math.pi * 2.0) rng'

--------------------------------------------------------------------------------
-- Geometric Distributions
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Statistical Distributions
--------------------------------------------------------------------------------

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
