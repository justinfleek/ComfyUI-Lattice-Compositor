-- | Lattice.Services.Export.FlowGenerators.SeededRandom - Seeded RNG
-- |
-- | Deterministic pseudo-random number generator using a simple hash function.
-- | Produces consistent results across platforms given the same seed.
-- |
-- | Algorithm: Mulberry32-style PRNG with improved bit mixing.
-- |
-- | Source: ui/src/services/export/wanMoveFlowGenerators.ts (SeededRandom class)

module Lattice.Services.Export.FlowGenerators.SeededRandom
  ( -- * Seeded Random State
    SeededRandomState
  , initialState
    -- * Random Operations
  , next
  , nextWithState
  , range
  , rangeWithState
  , gaussian
  , gaussianWithState
    -- * Pure Random Generation
  , randomSequence
  , randomRangeSequence
  ) where

import Prelude
import Data.Int (floor, toNumber)
import Data.Int.Bits (xor, (.&.), (.|.), shl, zshr) as Bits
import Data.Number (sqrt, log, cos, pi)
import Data.Array (snoc, (..))
import Data.Foldable (foldl)

-- ────────────────────────────────────────────────────────────────────────────
-- Seeded Random State
-- ────────────────────────────────────────────────────────────────────────────

-- | Seeded random state (immutable)
type SeededRandomState =
  { state :: Int
  }

-- | Create initial state from seed
initialState :: Int -> SeededRandomState
initialState seed = { state: seed }

-- ────────────────────────────────────────────────────────────────────────────
-- Core Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Integer multiplication with overflow behavior (JavaScript imul equivalent)
-- | This simulates 32-bit integer multiplication
imul :: Int -> Int -> Int
imul a b =
  let
    ah = (a `Bits.zshr` 16) Bits..&. 0xFFFF
    al = a Bits..&. 0xFFFF
    bh = (b `Bits.zshr` 16) Bits..&. 0xFFFF
    bl = b Bits..&. 0xFFFF
  in
    ((al * bl) + (((ah * bl + al * bh) `Bits.shl` 16) Bits..|. 0)) Bits..|. 0

-- | Bitwise zero-fill right shift
zshr :: Int -> Int -> Int
zshr = Bits.zshr

-- | Bitwise XOR
xor :: Int -> Int -> Int
xor = Bits.xor

-- | Generate next random value (0 to 1)
-- | Returns new state and random value
nextWithState :: SeededRandomState -> { state :: SeededRandomState, value :: Number }
nextWithState { state } =
  let
    -- Mulberry32-style PRNG
    t0 = state + 0x6D2B79F5
    t1 = imul (t0 `xor` (t0 `zshr` 15)) (t0 `or` 1)
    t2 = t1 `xor` (t1 + imul (t1 `xor` (t1 `zshr` 7)) (t1 `or` 61))
    t3 = t2 `xor` (t2 `zshr` 14)
    -- Convert to unsigned and normalize to 0-1
    unsigned = t3 `and` 0x7FFFFFFF
    normalized = toNumber unsigned / 2147483647.0
  in
    { state: { state: t0 }
    , value: normalized
    }

-- | Generate next random value (modifies state implicitly through return)
next :: SeededRandomState -> Number
next s = (nextWithState s).value

-- | Generate random value in range [min, max]
rangeWithState :: Number -> Number -> SeededRandomState -> { state :: SeededRandomState, value :: Number }
rangeWithState minVal maxVal s =
  let
    result = nextWithState s
    value = minVal + result.value * (maxVal - minVal)
  in
    { state: result.state, value }

-- | Generate random value in range [min, max]
range :: Number -> Number -> SeededRandomState -> Number
range minVal maxVal s = (rangeWithState minVal maxVal s).value

-- | Generate Gaussian-distributed random value (Box-Muller transform)
gaussianWithState :: Number -> Number -> SeededRandomState -> { state :: SeededRandomState, value :: Number }
gaussianWithState mean stdDev s =
  let
    r1 = nextWithState s
    r2 = nextWithState r1.state
    -- Guard against log(0) - clamp to minimum positive value
    u1 = max 0.0000001 r1.value
    u2 = r2.value
    -- Box-Muller transform
    z = sqrt (-2.0 * log u1) * cos (2.0 * pi * u2)
    value = mean + z * stdDev
  in
    { state: r2.state, value }

-- | Generate Gaussian-distributed random value
gaussian :: Number -> Number -> SeededRandomState -> Number
gaussian mean stdDev s = (gaussianWithState mean stdDev s).value

-- ────────────────────────────────────────────────────────────────────────────
-- Sequence Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate a sequence of random values
randomSequence :: Int -> SeededRandomState -> Array Number
randomSequence count seed =
  let
    go acc currentState n
      | n <= 0 = acc
      | otherwise =
          let
            result = nextWithState currentState
          in
            go (snoc acc result.value) result.state (n - 1)
  in
    go [] seed count

-- | Generate a sequence of random values in a range
randomRangeSequence :: Number -> Number -> Int -> SeededRandomState -> Array Number
randomRangeSequence minVal maxVal count seed =
  let
    go acc currentState n
      | n <= 0 = acc
      | otherwise =
          let
            result = rangeWithState minVal maxVal currentState
          in
            go (snoc acc result.value) result.state (n - 1)
  in
    go [] seed count
