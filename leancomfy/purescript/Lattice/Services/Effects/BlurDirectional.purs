-- | Lattice.Services.Effects.BlurDirectional - Directional and Radial Blur
-- |
-- | Pure mathematical functions for motion-style blurs:
-- | - Directional blur (motion blur in a direction)
-- | - Radial blur (zoom blur from center)
-- | - Box blur (fast average blur)
-- | - Sharpen filter
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/blurRenderer.ts

module Lattice.Services.Effects.BlurDirectional
  ( DirectionalParams
  , RadialParams
  , RadialType(..)
  , BoxParams
  , SharpenParams
  , defaultDirectionalParams
  , defaultRadialParams
  , defaultBoxParams
  , defaultSharpenParams
  , directionalOffset
  , radialOffset
  , boxBlurKernel
  , sharpenKernel
  , normalizeAngle
  , distance2D
  , sharpenWithThreshold
  ) where

import Prelude

import Data.Array (range, replicate)
import Data.Int (floor, toNumber)
import Data.Number (abs, atan2, cos, pi, sin, sqrt) as Number
import Data.Tuple (Tuple(..))
import Math (max, min) as Math

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Directional (motion) blur parameters
type DirectionalParams =
  { angle :: Number      -- Blur angle in radians [0, 2*pi]
  , distance :: Number   -- Blur distance in pixels [0-500]
  , samples :: Int       -- Number of samples [1-64]
  }

-- | Radial blur type
data RadialType
  = RadialSpin  -- Rotational blur around center
  | RadialZoom  -- Zoom blur toward/from center

derive instance eqRadialType :: Eq RadialType

instance showRadialType :: Show RadialType where
  show RadialSpin = "RadialSpin"
  show RadialZoom = "RadialZoom"

-- | Radial (zoom) blur parameters
type RadialParams =
  { centerX :: Number   -- Center X [0-1] normalized
  , centerY :: Number   -- Center Y [0-1] normalized
  , amount :: Number    -- Blur amount [0-100]
  , samples :: Int      -- Number of samples [1-64]
  , radialType :: RadialType
  }

-- | Box blur parameters
type BoxParams =
  { radiusX :: Int  -- Horizontal radius [1-250]
  , radiusY :: Int  -- Vertical radius [1-250]
  }

-- | Sharpen parameters
type SharpenParams =
  { amount :: Number     -- Sharpen amount [0-500%]
  , radius :: Int        -- Radius [1-10]
  , threshold :: Int     -- Threshold [0-255]
  }

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default directional blur
defaultDirectionalParams :: DirectionalParams
defaultDirectionalParams =
  { angle: 0.0
  , distance: 10.0
  , samples: 16
  }

-- | Default radial blur
defaultRadialParams :: RadialParams
defaultRadialParams =
  { centerX: 0.5
  , centerY: 0.5
  , amount: 10.0
  , samples: 16
  , radialType: RadialZoom
  }

-- | Default box blur
defaultBoxParams :: BoxParams
defaultBoxParams =
  { radiusX: 5
  , radiusY: 5
  }

-- | Default sharpen
defaultSharpenParams :: SharpenParams
defaultSharpenParams =
  { amount: 100.0
  , radius: 1
  , threshold: 0
  }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Clamp integer to range
clampInt :: Int -> Int -> Int -> Int
clampInt lo hi x = max lo (min hi x)

-- | Normalize angle to [0, 2*pi]
normalizeAngle :: Number -> Number
normalizeAngle angle =
  let twoPi = 2.0 * Number.pi
      a = angle - twoPi * toNumber (floor (angle / twoPi))
  in if a < 0.0 then a + twoPi else a

-- | 2D Euclidean distance
distance2D :: Number -> Number -> Number -> Number -> Number
distance2D x1 y1 x2 y2 =
  let dx = x2 - x1
      dy = y2 - y1
  in Number.sqrt (dx * dx + dy * dy)

--------------------------------------------------------------------------------
-- Directional Blur
--------------------------------------------------------------------------------

-- | Calculate sample offset for directional blur
directionalOffset :: DirectionalParams -> Int -> { dx :: Number, dy :: Number, weight :: Number }
directionalOffset params sampleIdx =
  let angle = params.angle
      dist = params.distance
      samples = max 1 params.samples
      t = toNumber sampleIdx / toNumber (samples - 1) - 0.5
      dx = Number.cos angle * dist * t
      dy = Number.sin angle * dist * t
      weight = 1.0 / toNumber samples
  in { dx, dy, weight }

--------------------------------------------------------------------------------
-- Radial Blur
--------------------------------------------------------------------------------

-- | Calculate sample offset for radial blur at a pixel position
radialOffset :: RadialParams -> Number -> Number -> Int -> { dx :: Number, dy :: Number, weight :: Number }
radialOffset params x y sampleIdx =
  let cx = params.centerX
      cy = params.centerY
      amount = params.amount / 100.0
      samples = max 1 params.samples
      dx' = x - cx
      dy' = y - cy
      dist = Number.sqrt (dx' * dx' + dy' * dy')
      t = toNumber sampleIdx / toNumber (samples - 1) - 0.5
      { offsetX, offsetY } = case params.radialType of
        RadialZoom ->
          { offsetX: dx' * amount * t, offsetY: dy' * amount * t }
        RadialSpin ->
          let angle = Number.atan2 dy' dx'
              spinAngle = angle + amount * t
          in { offsetX: Number.cos spinAngle * dist - dx'
             , offsetY: Number.sin spinAngle * dist - dy' }
      weight = 1.0 / toNumber samples
  in { dx: offsetX, dy: offsetY, weight }

--------------------------------------------------------------------------------
-- Box Blur
--------------------------------------------------------------------------------

-- | Generate box blur kernel (uniform weights)
boxBlurKernel :: BoxParams -> Array (Array Number)
boxBlurKernel params =
  let rx = clampInt 1 250 params.radiusX
      ry = clampInt 1 250 params.radiusY
      width = rx * 2 + 1
      height = ry * 2 + 1
      total = toNumber (width * height)
      weight = 1.0 / total
  in replicate height (replicate width weight)

--------------------------------------------------------------------------------
-- Sharpen
--------------------------------------------------------------------------------

-- | Generate sharpen kernel
sharpenKernel :: SharpenParams -> Array (Array Number)
sharpenKernel params =
  let amount = params.amount / 100.0
      r = clampInt 1 10 params.radius
      size = r * 2 + 1
      center = r
      blurWeight = 1.0 / toNumber (size * size)
      neighborWeight = -amount * blurWeight
      centerWeight = 1.0 + amount * (1.0 - blurWeight)
      mkRow i = map (\j ->
        if i == center && j == center then centerWeight else neighborWeight
        ) (range 0 (size - 1))
  in map mkRow (range 0 (size - 1))

-- | Apply sharpen threshold
sharpenWithThreshold :: SharpenParams -> Number -> Number -> Number
sharpenWithThreshold params original sharpened =
  let threshold = toNumber params.threshold / 255.0
      diff = Number.abs (sharpened - original)
  in if diff < threshold then original else sharpened
