-- | Lattice.Animation - Animation types
-- |
-- | Additional animation types not covered by Entities.
-- | Clipboard operations and helper types.
-- |
-- | Source: leancomfy/lean/Lattice/Animation.lean

module Lattice.Animation
  ( FullInterpolationType(..)
  , isBaseInterpolation
  , isEasingInterpolation
  , SpatialTangent
  , mkSpatialTangent
  , defaultSpatialTangent
  , ExtendedKeyframe
  , PropertyValue(..)
  , ClipboardKeyframeEntry
  , KeyframeClipboard
  , isClipboardEmpty
  , KeyframeSelection
  , KeyframeSelectionSet
  , isSelectionEmpty
  , selectionCount
  , isKeyframeSelected
  , defaultInHandle
  , defaultOutHandle
  , mkAnimatableProperty
  , mkKeyframe
  ) where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array as A
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives
import Lattice.Entities (BezierHandle, ControlMode(..), AnimatableProperty, PropertyValueType, Keyframe, PropertyExpression)
import Lattice.Enums (InterpolationType(..))

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

derive instance Eq FullInterpolationType
derive instance Generic FullInterpolationType _
instance Show FullInterpolationType where show = genericShow

isBaseInterpolation :: FullInterpolationType -> Boolean
isBaseInterpolation FITLinear = true
isBaseInterpolation FITBezier = true
isBaseInterpolation FITHold   = true
isBaseInterpolation _         = false

isEasingInterpolation :: FullInterpolationType -> Boolean
isEasingInterpolation = not <<< isBaseInterpolation

--------------------------------------------------------------------------------
-- Spatial Tangent
--------------------------------------------------------------------------------

type SpatialTangent =
  { x :: FiniteFloat
  , y :: FiniteFloat
  , z :: FiniteFloat
  }

mkSpatialTangent :: Number -> Number -> Number -> Maybe SpatialTangent
mkSpatialTangent x y z = do
  fx <- mkFiniteFloat x
  fy <- mkFiniteFloat y
  fz <- mkFiniteFloat z
  pure { x: fx, y: fy, z: fz }

defaultSpatialTangent :: SpatialTangent
defaultSpatialTangent = case mkSpatialTangent 0.0 0.0 0.0 of
  Just st -> st
  Nothing -> { x: unsafeFiniteFloat 0.0, y: unsafeFiniteFloat 0.0, z: unsafeFiniteFloat 0.0 }
  where
    unsafeFiniteFloat n = case mkFiniteFloat n of
      Just f -> f
      Nothing -> unsafeFiniteFloat 0.0  -- Will always succeed for 0.0

--------------------------------------------------------------------------------
-- Extended Keyframe
--------------------------------------------------------------------------------

type ExtendedKeyframe =
  { id               :: NonEmptyString
  , frame            :: FrameNumber
  , value            :: String  -- JSON-encoded
  , interpolation    :: FullInterpolationType
  , inHandle         :: BezierHandle
  , outHandle        :: BezierHandle
  , controlMode      :: ControlMode
  , spatialInTangent :: Maybe SpatialTangent
  , spatialOutTangent :: Maybe SpatialTangent
  }

--------------------------------------------------------------------------------
-- Property Value
--------------------------------------------------------------------------------

data PropertyValue
  = PVNumber Number
  | PVHexColor NonEmptyString
  | PVBoolean Boolean
  | PVVec2 Number Number
  | PVVec3 Number Number Number
  | PVRGBA Int Int Int Number

derive instance Eq PropertyValue
derive instance Generic PropertyValue _
instance Show PropertyValue where show = genericShow

--------------------------------------------------------------------------------
-- Clipboard
--------------------------------------------------------------------------------

type ClipboardKeyframeEntry =
  { layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , keyframeIds  :: Array NonEmptyString
  }

type KeyframeClipboard =
  { entries     :: Array ClipboardKeyframeEntry
  , sourceFrame :: FrameNumber
  }

isClipboardEmpty :: KeyframeClipboard -> Boolean
isClipboardEmpty kc = A.null kc.entries

--------------------------------------------------------------------------------
-- Selection
--------------------------------------------------------------------------------

type KeyframeSelection =
  { layerId      :: NonEmptyString
  , propertyPath :: NonEmptyString
  , keyframeId   :: NonEmptyString
  }

type KeyframeSelectionSet =
  { selections :: Array KeyframeSelection
  }

isSelectionEmpty :: KeyframeSelectionSet -> Boolean
isSelectionEmpty kss = A.null kss.selections

selectionCount :: KeyframeSelectionSet -> Int
selectionCount kss = A.length kss.selections

isKeyframeSelected :: KeyframeSelectionSet -> NonEmptyString -> NonEmptyString -> NonEmptyString -> Boolean
isKeyframeSelected kss layerId propPath kfId =
  A.any matchSel kss.selections
  where
    matchSel sel = sel.layerId == layerId
                && sel.propertyPath == propPath
                && sel.keyframeId == kfId

--------------------------------------------------------------------------------
-- Defaults
--------------------------------------------------------------------------------

defaultInHandle :: BezierHandle
defaultInHandle =
  { frame: fromMaybe (safeFinite 0.0) (mkFiniteFloat (-5.0))
  , value: fromMaybe (safeFinite 0.0) (mkFiniteFloat 0.0)
  , enabled: true
  }
  where
    safeFinite :: Number -> FiniteFloat
    safeFinite n = case mkFiniteFloat n of
      Just f -> f
      Nothing -> safeFinite 0.0

defaultOutHandle :: BezierHandle
defaultOutHandle =
  { frame: fromMaybe (safeFinite 0.0) (mkFiniteFloat 5.0)
  , value: fromMaybe (safeFinite 0.0) (mkFiniteFloat 0.0)
  , enabled: true
  }
  where
    safeFinite :: Number -> FiniteFloat
    safeFinite n = case mkFiniteFloat n of
      Just f -> f
      Nothing -> safeFinite 0.0

--------------------------------------------------------------------------------
-- Factory Functions
--------------------------------------------------------------------------------

-- | Create an AnimatableProperty with default values
-- | Pure factory - caller provides the ID
mkAnimatableProperty
  :: NonEmptyString
  -> NonEmptyString
  -> PropertyValueType
  -> String
  -> Maybe NonEmptyString
  -> AnimatableProperty
mkAnimatableProperty id name propType value group =
  { id
  , name
  , propertyType: propType
  , value
  , animated: false
  , keyframes: []
  , group
  , expression: Nothing :: Maybe PropertyExpression
  }

-- | Create a Keyframe with default interpolation and handles
-- | Pure factory - caller provides the ID
mkKeyframe :: NonEmptyString -> FrameNumber -> String -> Keyframe
mkKeyframe id frame value =
  { id
  , frame
  , value
  , interpolation: ITLinear
  , inHandle: defaultInHandle
  , outHandle: defaultOutHandle
  , controlMode: CMSmooth
  }
