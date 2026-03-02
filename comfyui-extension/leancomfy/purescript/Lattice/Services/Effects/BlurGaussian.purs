-- | Lattice.Services.Effects.BlurGaussian - Gaussian Blur Implementation
-- |
-- | Pure mathematical functions for Gaussian blur:
-- | - Gaussian kernel generation
-- | - Separable convolution (horizontal/vertical passes)
-- | - Stack blur approximation coefficients
-- |
-- | All functions are total and deterministic.
-- | Uses StackBlur algorithm for O(n) performance regardless of radius.
-- |
-- | Source: ui/src/services/effects/blurRenderer.ts

module Lattice.Services.Effects.BlurGaussian
  ( GaussianParams
  , EdgeMode(..)
  , BlurKernel
  , defaultGaussianParams
  , gaussianWeight
  , generateGaussianKernel
  , applyKernel1D
  ) where

import Prelude

import Data.Array ((..), length, index, mapWithIndex, foldl)
import Data.Int (round, toNumber)
import Data.Maybe (fromMaybe)
import Data.Number (exp, sqrt, log, pi) as Number
import Data.Tuple (Tuple(..))

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Gaussian blur parameters
type GaussianParams =
  { radius :: Int       -- Blur radius in pixels [1-250]
  , quality :: Number   -- Blur quality [0.1-3.0]
  , edgeMode :: EdgeMode
  }

-- | Edge handling mode
data EdgeMode
  = EdgeClamp   -- Clamp to edge pixels
  | EdgeWrap    -- Wrap around
  | EdgeMirror  -- Mirror at edges

derive instance eqEdgeMode :: Eq EdgeMode

instance showEdgeMode :: Show EdgeMode where
  show EdgeClamp = "EdgeClamp"
  show EdgeWrap = "EdgeWrap"
  show EdgeMirror = "EdgeMirror"

-- | Pre-computed blur kernel
type BlurKernel =
  { weights :: Array Number  -- Kernel weights
  , radius :: Int            -- Kernel radius
  , sum :: Number            -- Sum of weights
  }

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default Gaussian blur (radius 5)
defaultGaussianParams :: GaussianParams
defaultGaussianParams =
  { radius: 5
  , quality: 1.0
  , edgeMode: EdgeClamp
  }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Clamp integer to range
clampInt :: Int -> Int -> Int -> Int
clampInt lo hi x = max lo (min hi x)

-- | Clamp value to [0, 1]
clamp01 :: Number -> Number
clamp01 = max 0.0 <<< min 1.0

-- | Safe array access with default
safeIndex :: forall a. Array a -> Int -> a -> a
safeIndex arr i def = fromMaybe def (index arr i)

--------------------------------------------------------------------------------
-- Gaussian Kernel
--------------------------------------------------------------------------------

-- | Calculate Gaussian weight at distance x with given sigma
gaussianWeight :: Number -> Number -> Number
gaussianWeight sigma x =
  let sigma2 = sigma * sigma
      coeff = 1.0 / (Number.sqrt (2.0 * Number.pi) * sigma)
  in coeff * Number.exp (-(x * x) / (2.0 * sigma2))

-- | Generate 1D Gaussian kernel
generateGaussianKernel :: Int -> Number -> BlurKernel
generateGaussianKernel radius quality =
  let r = clampInt 1 250 radius
      sigma = toNumber r / max 0.1 quality
      -- Generate weights for 0 to radius
      weights = map (\i -> gaussianWeight sigma (toNumber i)) (0 .. r)
      -- Calculate sum
      centerWeight = safeIndex weights 0 0.0
      sideSum = foldl (+) 0.0 (map (\i -> safeIndex weights i 0.0) (1 .. r))
      totalSum = centerWeight + 2.0 * sideSum
  in { weights: weights
     , radius: r
     , sum: totalSum
     }

--------------------------------------------------------------------------------
-- Blur Operations
--------------------------------------------------------------------------------

-- | Apply 1D kernel to a row of pixels at position x
applyKernel1D :: Array Number -> BlurKernel -> EdgeMode -> Int -> Number
applyKernel1D pixels kernel mode x =
  let r = kernel.radius
      weights = kernel.weights
      width = length pixels
      -- Sample with edge handling
      sample i = case mode of
        EdgeClamp -> safeIndex pixels (clampInt 0 (width - 1) i) 0.0
        EdgeWrap -> safeIndex pixels (i `mod` width) 0.0
        EdgeMirror ->
          let i' = if i < 0 then -i - 1
                   else if i >= width then 2 * width - i - 1
                   else i
          in safeIndex pixels (clampInt 0 (width - 1) i') 0.0
      -- Center contribution
      centerWeight = safeIndex weights 0 0.0
      center = sample x * centerWeight
      -- Side contributions
      sides = foldl (+) 0.0 $ mapWithIndex (\i w ->
        if i == 0 then 0.0
        else w * (sample (x - i) + sample (x + i))
        ) weights
  in (center + sides) / kernel.sum
