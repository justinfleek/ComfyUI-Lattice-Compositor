{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Animation
Description : Animation types
Copyright   : (c) Lattice, 2026
License     : MIT

Additional animation types not covered by Entities.
Clipboard operations and helper types.

Source: leancomfy/lean/Lattice/Animation.lean
-}

module Lattice.Animation
  ( -- * Interpolation
    FullInterpolationType(..)
  , isBaseInterpolation
  , isEasingInterpolation
    -- * Spatial Tangent
  , SpatialTangent(..)
  , mkSpatialTangent
  , defaultSpatialTangent
    -- * Extended Keyframe
  , ExtendedKeyframe(..)
    -- * Property Value
  , PropertyValue(..)
    -- * Clipboard
  , ClipboardKeyframeEntry(..)
  , KeyframeClipboard(..)
  , isClipboardEmpty
  , clipboardLayerIds
    -- * Selection
  , KeyframeSelection(..)
  , KeyframeSelectionSet(..)
  , isSelectionEmpty
  , selectionCount
  , isKeyframeSelected
    -- * Defaults
  , defaultInHandle
  , defaultOutHandle
  ) where

import GHC.Generics (Generic)
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.List as L
import Lattice.Primitives
import Lattice.Entities (BezierHandle(..), ControlMode(..))

--------------------------------------------------------------------------------
-- Full Interpolation Type
--------------------------------------------------------------------------------

data FullInterpolationType
  -- Base types
  = FITLinear | FITBezier | FITHold
  -- Sine
  | FITEaseInSine | FITEaseOutSine | FITEaseInOutSine
  -- Quadratic
  | FITEaseInQuad | FITEaseOutQuad | FITEaseInOutQuad
  -- Cubic
  | FITEaseInCubic | FITEaseOutCubic | FITEaseInOutCubic
  -- Quartic
  | FITEaseInQuart | FITEaseOutQuart | FITEaseInOutQuart
  -- Quintic
  | FITEaseInQuint | FITEaseOutQuint | FITEaseInOutQuint
  -- Exponential
  | FITEaseInExpo | FITEaseOutExpo | FITEaseInOutExpo
  -- Circular
  | FITEaseInCirc | FITEaseOutCirc | FITEaseInOutCirc
  -- Back
  | FITEaseInBack | FITEaseOutBack | FITEaseInOutBack
  -- Elastic
  | FITEaseInElastic | FITEaseOutElastic | FITEaseInOutElastic
  -- Bounce
  | FITEaseInBounce | FITEaseOutBounce | FITEaseInOutBounce
  deriving stock (Eq, Show, Generic)

isBaseInterpolation :: FullInterpolationType -> Bool
isBaseInterpolation FITLinear = True
isBaseInterpolation FITBezier = True
isBaseInterpolation FITHold   = True
isBaseInterpolation _         = False

isEasingInterpolation :: FullInterpolationType -> Bool
isEasingInterpolation = not . isBaseInterpolation

--------------------------------------------------------------------------------
-- Spatial Tangent
--------------------------------------------------------------------------------

data SpatialTangent = SpatialTangent
  { stX :: !FiniteFloat
  , stY :: !FiniteFloat
  , stZ :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

mkSpatialTangent :: Double -> Double -> Double -> Maybe SpatialTangent
mkSpatialTangent x y z = do
  fx <- mkFiniteFloat x
  fy <- mkFiniteFloat y
  fz <- mkFiniteFloat z
  pure $ SpatialTangent fx fy fz

-- | Default spatial tangent at origin. Uses Num instance for FiniteFloat
-- which is safe for literal constants (0 is always finite).
defaultSpatialTangent :: SpatialTangent
defaultSpatialTangent = SpatialTangent 0 0 0

--------------------------------------------------------------------------------
-- Extended Keyframe
--------------------------------------------------------------------------------

data ExtendedKeyframe = ExtendedKeyframe
  { ekId               :: !NonEmptyString
  , ekFrame            :: !FrameNumber
  , ekValue            :: !String  -- JSON-encoded
  , ekInterpolation    :: !FullInterpolationType
  , ekInHandle         :: !BezierHandle
  , ekOutHandle        :: !BezierHandle
  , ekControlMode      :: !ControlMode
  , ekSpatialInTangent :: !(Maybe SpatialTangent)
  , ekSpatialOutTangent :: !(Maybe SpatialTangent)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Property Value
--------------------------------------------------------------------------------

data PropertyValue
  = PVNumber !Double
  | PVHexColor !NonEmptyString
  | PVBoolean !Bool
  | PVVec2 !Double !Double
  | PVVec3 !Double !Double !Double
  | PVRGBA !Int !Int !Int !Double
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Clipboard
--------------------------------------------------------------------------------

data ClipboardKeyframeEntry = ClipboardKeyframeEntry
  { ckeLayerId      :: !NonEmptyString
  , ckePropertyPath :: !NonEmptyString
  , ckeKeyframeIds  :: !(Vector NonEmptyString)
  } deriving stock (Eq, Show, Generic)

data KeyframeClipboard = KeyframeClipboard
  { kcEntries     :: !(Vector ClipboardKeyframeEntry)
  , kcSourceFrame :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

isClipboardEmpty :: KeyframeClipboard -> Bool
isClipboardEmpty = V.null . kcEntries

clipboardLayerIds :: KeyframeClipboard -> Vector NonEmptyString
clipboardLayerIds kc = V.fromList $ L.nub $ V.toList $ V.map ckeLayerId (kcEntries kc)

--------------------------------------------------------------------------------
-- Selection
--------------------------------------------------------------------------------

data KeyframeSelection = KeyframeSelection
  { ksLayerId      :: !NonEmptyString
  , ksPropertyPath :: !NonEmptyString
  , ksKeyframeId   :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

newtype KeyframeSelectionSet = KeyframeSelectionSet
  { kssSelections :: Vector KeyframeSelection
  } deriving stock (Eq, Show, Generic)

isSelectionEmpty :: KeyframeSelectionSet -> Bool
isSelectionEmpty = V.null . kssSelections

selectionCount :: KeyframeSelectionSet -> Int
selectionCount = V.length . kssSelections

isKeyframeSelected :: KeyframeSelectionSet -> NonEmptyString -> NonEmptyString -> NonEmptyString -> Bool
isKeyframeSelected kss layerId propPath kfId =
  V.any matchSel (kssSelections kss)
  where
    matchSel sel = ksLayerId sel == layerId
                && ksPropertyPath sel == propPath
                && ksKeyframeId sel == kfId

--------------------------------------------------------------------------------
-- Defaults
--------------------------------------------------------------------------------

-- | Default in handle. Uses Num instance for FiniteFloat (safe for literals).
defaultInHandle :: BezierHandle
defaultInHandle = BezierHandle
  { bhFrame = -5  -- Num instance ensures this is a FiniteFloat
  , bhValue = 0
  , bhEnabled = True
  }

-- | Default out handle. Uses Num instance for FiniteFloat (safe for literals).
defaultOutHandle :: BezierHandle
defaultOutHandle = BezierHandle
  { bhFrame = 5  -- Num instance ensures this is a FiniteFloat
  , bhValue = 0
  , bhEnabled = True
  }
