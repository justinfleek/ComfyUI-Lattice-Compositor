{-
  Lattice.Services.Time.Echo - Echo Effect Logic

  Pure functions for echo/motion trail effect:
  - Echo operator blending modes
  - Intensity calculations with decay
  - Echo frame compositing order

  Source: ui/src/services/effects/timeRenderer.ts (lines 207-388)
-}

module Lattice.Services.Time.Echo
  ( EchoOperator(..)
  , parseEchoOperator
  , echoOperatorToComposite
  -- * Parameter Validation
  , validateNumEchoes
  , validateStartingIntensity
  , validateDecay
  , validateEchoTime
  -- * Intensity Calculation
  , calculateEchoIntensities
  , intensityThreshold
  -- * Echo Ordering
  , shouldDrawEchosBehind
  , echoRequiresCurrentOnTop
  ) where

import Prelude

import Data.Array ((..), mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Math (pow)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Echo operator - how echoes are composited.
data EchoOperator
  = EchoAdd
  | EchoScreen
  | EchoMaximum
  | EchoMinimum
  | EchoCompositeBack
  | EchoCompositeFront
  | EchoBlend

derive instance eqEchoOperator :: Eq EchoOperator

instance showEchoOperator :: Show EchoOperator where
  show EchoAdd = "add"
  show EchoScreen = "screen"
  show EchoMaximum = "maximum"
  show EchoMinimum = "minimum"
  show EchoCompositeBack = "composite_back"
  show EchoCompositeFront = "composite_front"
  show EchoBlend = "blend"

-- | Parse echo operator from string.
parseEchoOperator :: String -> EchoOperator
parseEchoOperator s = case s of
  "add" -> EchoAdd
  "screen" -> EchoScreen
  "maximum" -> EchoMaximum
  "minimum" -> EchoMinimum
  "composite_back" -> EchoCompositeBack
  "composite_front" -> EchoCompositeFront
  "blend" -> EchoBlend
  _ -> EchoAdd  -- Default

-- | Convert echo operator to canvas composite operation name.
echoOperatorToComposite :: EchoOperator -> String
echoOperatorToComposite op = case op of
  EchoAdd -> "lighter"
  EchoScreen -> "screen"
  EchoMaximum -> "lighten"
  EchoMinimum -> "darken"
  EchoCompositeBack -> "destination-over"
  EchoCompositeFront -> "source-over"
  EchoBlend -> "source-over"

--------------------------------------------------------------------------------
-- Parameter Validation
--------------------------------------------------------------------------------

-- | Validate and clamp number of echoes to [1, 50].
validateNumEchoes :: Int -> Int
validateNumEchoes n = max 1 (min 50 n)

-- | Validate and clamp starting intensity to [0, 1].
validateStartingIntensity :: Number -> Number
validateStartingIntensity i = max 0.0 (min 1.0 i)

-- | Validate and clamp decay to [0, 1].
validateDecay :: Number -> Number
validateDecay d = max 0.0 (min 1.0 d)

-- | Validate echo time (no clamping, can be negative for trailing).
validateEchoTime :: Number -> Number -> Number
validateEchoTime echoTime fps =
  if echoTime == 0.0 then -1.0 / fps else echoTime

--------------------------------------------------------------------------------
-- Intensity Calculation
--------------------------------------------------------------------------------

-- | Minimum intensity threshold for rendering echo.
intensityThreshold :: Number
intensityThreshold = 0.001

-- | Calculate intensities for all echoes.
--   Returns array of intensities using exponential decay.
--   intensity[i] = startingIntensity * (1 - decay)^i
calculateEchoIntensities :: Number -> Number -> Int -> Array Number
calculateEchoIntensities startingIntensity decay numEchoes =
  let base = 1.0 - decay
      calcIntensity i = startingIntensity * pow base (toNumber i)
  in map calcIntensity (0 .. (numEchoes - 1))

--------------------------------------------------------------------------------
-- Echo Ordering
--------------------------------------------------------------------------------

-- | Check if echoes should be drawn behind current frame.
shouldDrawEchosBehind :: EchoOperator -> Boolean
shouldDrawEchosBehind EchoCompositeBack = true
shouldDrawEchosBehind _ = false

-- | Check if current frame needs to be drawn on top after echoes.
echoRequiresCurrentOnTop :: EchoOperator -> Boolean
echoRequiresCurrentOnTop EchoCompositeBack = true
echoRequiresCurrentOnTop _ = false
