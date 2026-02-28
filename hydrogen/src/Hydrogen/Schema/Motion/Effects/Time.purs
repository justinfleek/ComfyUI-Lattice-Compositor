-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // effects // time
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Time-based effect enums for motion graphics.
-- |
-- | Defines echo operators and time resolution options.

module Hydrogen.Schema.Motion.Effects.Time
  ( -- * Echo Operator
    EchoOperator(..)
  , allEchoOperators
  , echoOperatorToString
  , echoOperatorFromString
  
    -- * Time Resolution
  , TimeResolution(..)
  , allTimeResolutions
  , timeResolutionToString
  , timeResolutionFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // echo // operator
-- ═════════════════════════════════════════════════════════════════════════════

-- | Operator for combining echo frames.
data EchoOperator
  = EOAdd            -- ^ Add frames together
  | EOScreen         -- ^ Screen blend
  | EOMaximum        -- ^ Take maximum values
  | EOMinimum        -- ^ Take minimum values
  | EOCompositeBack  -- ^ Composite echoes behind
  | EOCompositeFront -- ^ Composite echoes in front
  | EOBlend          -- ^ Linear blend

derive instance eqEchoOperator :: Eq EchoOperator
derive instance ordEchoOperator :: Ord EchoOperator

instance showEchoOperator :: Show EchoOperator where
  show EOAdd = "EOAdd"
  show EOScreen = "EOScreen"
  show EOMaximum = "EOMaximum"
  show EOMinimum = "EOMinimum"
  show EOCompositeBack = "EOCompositeBack"
  show EOCompositeFront = "EOCompositeFront"
  show EOBlend = "EOBlend"

-- | All echo operators for enumeration
allEchoOperators :: Array EchoOperator
allEchoOperators =
  [ EOAdd
  , EOScreen
  , EOMaximum
  , EOMinimum
  , EOCompositeBack
  , EOCompositeFront
  , EOBlend
  ]

echoOperatorToString :: EchoOperator -> String
echoOperatorToString EOAdd = "add"
echoOperatorToString EOScreen = "screen"
echoOperatorToString EOMaximum = "maximum"
echoOperatorToString EOMinimum = "minimum"
echoOperatorToString EOCompositeBack = "composite-back"
echoOperatorToString EOCompositeFront = "composite-front"
echoOperatorToString EOBlend = "blend"

echoOperatorFromString :: String -> Maybe EchoOperator
echoOperatorFromString "add" = Just EOAdd
echoOperatorFromString "screen" = Just EOScreen
echoOperatorFromString "maximum" = Just EOMaximum
echoOperatorFromString "minimum" = Just EOMinimum
echoOperatorFromString "composite-back" = Just EOCompositeBack
echoOperatorFromString "composite-front" = Just EOCompositeFront
echoOperatorFromString "blend" = Just EOBlend
echoOperatorFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // time // resolution
-- ═════════════════════════════════════════════════════════════════════════════

-- | Resolution for time-based effects.
data TimeResolution
  = TRFrame    -- ^ Full frame
  | TRHalf     -- ^ Half frame
  | TRQuarter  -- ^ Quarter frame

derive instance eqTimeResolution :: Eq TimeResolution
derive instance ordTimeResolution :: Ord TimeResolution

instance showTimeResolution :: Show TimeResolution where
  show TRFrame = "TRFrame"
  show TRHalf = "TRHalf"
  show TRQuarter = "TRQuarter"

-- | All time resolutions for enumeration
allTimeResolutions :: Array TimeResolution
allTimeResolutions = [ TRFrame, TRHalf, TRQuarter ]

timeResolutionToString :: TimeResolution -> String
timeResolutionToString TRFrame = "frame"
timeResolutionToString TRHalf = "half"
timeResolutionToString TRQuarter = "quarter"

timeResolutionFromString :: String -> Maybe TimeResolution
timeResolutionFromString "frame" = Just TRFrame
timeResolutionFromString "half" = Just TRHalf
timeResolutionFromString "quarter" = Just TRQuarter
timeResolutionFromString _ = Nothing
