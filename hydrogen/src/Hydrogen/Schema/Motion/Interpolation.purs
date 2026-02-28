-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // motion // interpolation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyframe interpolation types for motion graphics.
-- |
-- | Defines how values transition between keyframes:
-- | - Temporal interpolation: timing curves (linear, bezier, easing presets)
-- | - Spatial interpolation: position path tangents for motion paths
-- |
-- | ## Architecture
-- |
-- | This module mirrors `Lattice.Animation.FullInterpolationType` from the
-- | Lattice Haskell backend. It works with `Hydrogen.Schema.Motion.Easing`
-- | for the actual curve evaluation.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.Interpolation as Interp
-- |
-- | -- Linear interpolation (no easing)
-- | linear = Interp.fitLinear
-- |
-- | -- Ease-in-out cubic
-- | smooth = Interp.fitEaseInOutCubic
-- |
-- | -- Check if it's a base type
-- | Interp.isBaseInterpolation linear  -- true
-- | Interp.isBaseInterpolation smooth  -- false
-- | ```

module Hydrogen.Schema.Motion.Interpolation
  ( -- * Full Interpolation Type
    FullInterpolationType(..)
  , allFullInterpolationTypes
  , fullInterpolationTypeToString
  , fullInterpolationTypeFromString
  , isBaseInterpolation
  , isEasingInterpolation
  
  -- * Base Type Constructors
  , fitLinear
  , fitBezier
  , fitHold
  
  -- * Sine Constructors
  , fitEaseInSine
  , fitEaseOutSine
  , fitEaseInOutSine
  
  -- * Quadratic Constructors
  , fitEaseInQuad
  , fitEaseOutQuad
  , fitEaseInOutQuad
  
  -- * Cubic Constructors
  , fitEaseInCubic
  , fitEaseOutCubic
  , fitEaseInOutCubic
  
  -- * Quartic Constructors
  , fitEaseInQuart
  , fitEaseOutQuart
  , fitEaseInOutQuart
  
  -- * Quintic Constructors
  , fitEaseInQuint
  , fitEaseOutQuint
  , fitEaseInOutQuint
  
  -- * Exponential Constructors
  , fitEaseInExpo
  , fitEaseOutExpo
  , fitEaseInOutExpo
  
  -- * Circular Constructors
  , fitEaseInCirc
  , fitEaseOutCirc
  , fitEaseInOutCirc
  
  -- * Back Constructors
  , fitEaseInBack
  , fitEaseOutBack
  , fitEaseInOutBack
  
  -- * Elastic Constructors
  , fitEaseInElastic
  , fitEaseOutElastic
  , fitEaseInOutElastic
  
  -- * Bounce Constructors
  , fitEaseInBounce
  , fitEaseOutBounce
  , fitEaseInOutBounce
  
  -- * Spatial Tangent
  , SpatialTangent(..)
  , mkSpatialTangent
  , defaultSpatialTangent
  , spatialTangentZero
  
  -- * Bezier Handle
  , BezierHandle(..)
  , mkBezierHandle
  , defaultInHandle
  , defaultOutHandle
  
  -- * Control Mode
  , ControlMode(..)
  , allControlModes
  , controlModeToString
  , controlModeFromString
  
  -- * Extended Keyframe Data
  , ExtendedKeyframeData(..)
  , defaultExtendedKeyframeData
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , not
  , negate
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // full // interpolation // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete interpolation type enumeration.
-- |
-- | Covers all standard easing presets plus base types.
-- | Mirrors `Lattice.Animation.FullInterpolationType`.
data FullInterpolationType
  -- Base types
  = FITLinear           -- Linear interpolation
  | FITBezier           -- Custom bezier curve (uses handle data)
  | FITHold             -- Hold previous value until next keyframe
  
  -- Sine easing
  | FITEaseInSine
  | FITEaseOutSine
  | FITEaseInOutSine
  
  -- Quadratic easing
  | FITEaseInQuad
  | FITEaseOutQuad
  | FITEaseInOutQuad
  
  -- Cubic easing
  | FITEaseInCubic
  | FITEaseOutCubic
  | FITEaseInOutCubic
  
  -- Quartic easing
  | FITEaseInQuart
  | FITEaseOutQuart
  | FITEaseInOutQuart
  
  -- Quintic easing
  | FITEaseInQuint
  | FITEaseOutQuint
  | FITEaseInOutQuint
  
  -- Exponential easing
  | FITEaseInExpo
  | FITEaseOutExpo
  | FITEaseInOutExpo
  
  -- Circular easing
  | FITEaseInCirc
  | FITEaseOutCirc
  | FITEaseInOutCirc
  
  -- Back easing (overshoot)
  | FITEaseInBack
  | FITEaseOutBack
  | FITEaseInOutBack
  
  -- Elastic easing
  | FITEaseInElastic
  | FITEaseOutElastic
  | FITEaseInOutElastic
  
  -- Bounce easing
  | FITEaseInBounce
  | FITEaseOutBounce
  | FITEaseInOutBounce

derive instance eqFullInterpolationType :: Eq FullInterpolationType
derive instance ordFullInterpolationType :: Ord FullInterpolationType

instance showFullInterpolationType :: Show FullInterpolationType where
  show = fullInterpolationTypeToString

-- | Convert interpolation type to string.
fullInterpolationTypeToString :: FullInterpolationType -> String
fullInterpolationTypeToString FITLinear = "linear"
fullInterpolationTypeToString FITBezier = "bezier"
fullInterpolationTypeToString FITHold = "hold"
fullInterpolationTypeToString FITEaseInSine = "easeInSine"
fullInterpolationTypeToString FITEaseOutSine = "easeOutSine"
fullInterpolationTypeToString FITEaseInOutSine = "easeInOutSine"
fullInterpolationTypeToString FITEaseInQuad = "easeInQuad"
fullInterpolationTypeToString FITEaseOutQuad = "easeOutQuad"
fullInterpolationTypeToString FITEaseInOutQuad = "easeInOutQuad"
fullInterpolationTypeToString FITEaseInCubic = "easeInCubic"
fullInterpolationTypeToString FITEaseOutCubic = "easeOutCubic"
fullInterpolationTypeToString FITEaseInOutCubic = "easeInOutCubic"
fullInterpolationTypeToString FITEaseInQuart = "easeInQuart"
fullInterpolationTypeToString FITEaseOutQuart = "easeOutQuart"
fullInterpolationTypeToString FITEaseInOutQuart = "easeInOutQuart"
fullInterpolationTypeToString FITEaseInQuint = "easeInQuint"
fullInterpolationTypeToString FITEaseOutQuint = "easeOutQuint"
fullInterpolationTypeToString FITEaseInOutQuint = "easeInOutQuint"
fullInterpolationTypeToString FITEaseInExpo = "easeInExpo"
fullInterpolationTypeToString FITEaseOutExpo = "easeOutExpo"
fullInterpolationTypeToString FITEaseInOutExpo = "easeInOutExpo"
fullInterpolationTypeToString FITEaseInCirc = "easeInCirc"
fullInterpolationTypeToString FITEaseOutCirc = "easeOutCirc"
fullInterpolationTypeToString FITEaseInOutCirc = "easeInOutCirc"
fullInterpolationTypeToString FITEaseInBack = "easeInBack"
fullInterpolationTypeToString FITEaseOutBack = "easeOutBack"
fullInterpolationTypeToString FITEaseInOutBack = "easeInOutBack"
fullInterpolationTypeToString FITEaseInElastic = "easeInElastic"
fullInterpolationTypeToString FITEaseOutElastic = "easeOutElastic"
fullInterpolationTypeToString FITEaseInOutElastic = "easeInOutElastic"
fullInterpolationTypeToString FITEaseInBounce = "easeInBounce"
fullInterpolationTypeToString FITEaseOutBounce = "easeOutBounce"
fullInterpolationTypeToString FITEaseInOutBounce = "easeInOutBounce"

-- | Parse interpolation type from string.
fullInterpolationTypeFromString :: String -> Maybe FullInterpolationType
fullInterpolationTypeFromString "linear" = Just FITLinear
fullInterpolationTypeFromString "bezier" = Just FITBezier
fullInterpolationTypeFromString "hold" = Just FITHold
fullInterpolationTypeFromString "easeInSine" = Just FITEaseInSine
fullInterpolationTypeFromString "easeOutSine" = Just FITEaseOutSine
fullInterpolationTypeFromString "easeInOutSine" = Just FITEaseInOutSine
fullInterpolationTypeFromString "easeInQuad" = Just FITEaseInQuad
fullInterpolationTypeFromString "easeOutQuad" = Just FITEaseOutQuad
fullInterpolationTypeFromString "easeInOutQuad" = Just FITEaseInOutQuad
fullInterpolationTypeFromString "easeInCubic" = Just FITEaseInCubic
fullInterpolationTypeFromString "easeOutCubic" = Just FITEaseOutCubic
fullInterpolationTypeFromString "easeInOutCubic" = Just FITEaseInOutCubic
fullInterpolationTypeFromString "easeInQuart" = Just FITEaseInQuart
fullInterpolationTypeFromString "easeOutQuart" = Just FITEaseOutQuart
fullInterpolationTypeFromString "easeInOutQuart" = Just FITEaseInOutQuart
fullInterpolationTypeFromString "easeInQuint" = Just FITEaseInQuint
fullInterpolationTypeFromString "easeOutQuint" = Just FITEaseOutQuint
fullInterpolationTypeFromString "easeInOutQuint" = Just FITEaseInOutQuint
fullInterpolationTypeFromString "easeInExpo" = Just FITEaseInExpo
fullInterpolationTypeFromString "easeOutExpo" = Just FITEaseOutExpo
fullInterpolationTypeFromString "easeInOutExpo" = Just FITEaseInOutExpo
fullInterpolationTypeFromString "easeInCirc" = Just FITEaseInCirc
fullInterpolationTypeFromString "easeOutCirc" = Just FITEaseOutCirc
fullInterpolationTypeFromString "easeInOutCirc" = Just FITEaseInOutCirc
fullInterpolationTypeFromString "easeInBack" = Just FITEaseInBack
fullInterpolationTypeFromString "easeOutBack" = Just FITEaseOutBack
fullInterpolationTypeFromString "easeInOutBack" = Just FITEaseInOutBack
fullInterpolationTypeFromString "easeInElastic" = Just FITEaseInElastic
fullInterpolationTypeFromString "easeOutElastic" = Just FITEaseOutElastic
fullInterpolationTypeFromString "easeInOutElastic" = Just FITEaseInOutElastic
fullInterpolationTypeFromString "easeInBounce" = Just FITEaseInBounce
fullInterpolationTypeFromString "easeOutBounce" = Just FITEaseOutBounce
fullInterpolationTypeFromString "easeInOutBounce" = Just FITEaseInOutBounce
fullInterpolationTypeFromString _ = Nothing

-- | All interpolation types for enumeration
allFullInterpolationTypes :: Array FullInterpolationType
allFullInterpolationTypes =
  [ FITLinear
  , FITBezier
  , FITHold
  , FITEaseInSine
  , FITEaseOutSine
  , FITEaseInOutSine
  , FITEaseInQuad
  , FITEaseOutQuad
  , FITEaseInOutQuad
  , FITEaseInCubic
  , FITEaseOutCubic
  , FITEaseInOutCubic
  , FITEaseInQuart
  , FITEaseOutQuart
  , FITEaseInOutQuart
  , FITEaseInQuint
  , FITEaseOutQuint
  , FITEaseInOutQuint
  , FITEaseInExpo
  , FITEaseOutExpo
  , FITEaseInOutExpo
  , FITEaseInCirc
  , FITEaseOutCirc
  , FITEaseInOutCirc
  , FITEaseInBack
  , FITEaseOutBack
  , FITEaseInOutBack
  , FITEaseInElastic
  , FITEaseOutElastic
  , FITEaseInOutElastic
  , FITEaseInBounce
  , FITEaseOutBounce
  , FITEaseInOutBounce
  ]

-- | Check if interpolation type is a base type (linear, bezier, hold).
isBaseInterpolation :: FullInterpolationType -> Boolean
isBaseInterpolation FITLinear = true
isBaseInterpolation FITBezier = true
isBaseInterpolation FITHold = true
isBaseInterpolation _ = false

-- | Check if interpolation type is an easing preset.
isEasingInterpolation :: FullInterpolationType -> Boolean
isEasingInterpolation fit = not (isBaseInterpolation fit)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // constructor // aliases
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation (constant speed)
fitLinear :: FullInterpolationType
fitLinear = FITLinear

-- | Custom bezier curve (uses handle data)
fitBezier :: FullInterpolationType
fitBezier = FITBezier

-- | Hold value until next keyframe
fitHold :: FullInterpolationType
fitHold = FITHold

-- Sine
fitEaseInSine :: FullInterpolationType
fitEaseInSine = FITEaseInSine

fitEaseOutSine :: FullInterpolationType
fitEaseOutSine = FITEaseOutSine

fitEaseInOutSine :: FullInterpolationType
fitEaseInOutSine = FITEaseInOutSine

-- Quad
fitEaseInQuad :: FullInterpolationType
fitEaseInQuad = FITEaseInQuad

fitEaseOutQuad :: FullInterpolationType
fitEaseOutQuad = FITEaseOutQuad

fitEaseInOutQuad :: FullInterpolationType
fitEaseInOutQuad = FITEaseInOutQuad

-- Cubic
fitEaseInCubic :: FullInterpolationType
fitEaseInCubic = FITEaseInCubic

fitEaseOutCubic :: FullInterpolationType
fitEaseOutCubic = FITEaseOutCubic

fitEaseInOutCubic :: FullInterpolationType
fitEaseInOutCubic = FITEaseInOutCubic

-- Quart
fitEaseInQuart :: FullInterpolationType
fitEaseInQuart = FITEaseInQuart

fitEaseOutQuart :: FullInterpolationType
fitEaseOutQuart = FITEaseOutQuart

fitEaseInOutQuart :: FullInterpolationType
fitEaseInOutQuart = FITEaseInOutQuart

-- Quint
fitEaseInQuint :: FullInterpolationType
fitEaseInQuint = FITEaseInQuint

fitEaseOutQuint :: FullInterpolationType
fitEaseOutQuint = FITEaseOutQuint

fitEaseInOutQuint :: FullInterpolationType
fitEaseInOutQuint = FITEaseInOutQuint

-- Expo
fitEaseInExpo :: FullInterpolationType
fitEaseInExpo = FITEaseInExpo

fitEaseOutExpo :: FullInterpolationType
fitEaseOutExpo = FITEaseOutExpo

fitEaseInOutExpo :: FullInterpolationType
fitEaseInOutExpo = FITEaseInOutExpo

-- Circ
fitEaseInCirc :: FullInterpolationType
fitEaseInCirc = FITEaseInCirc

fitEaseOutCirc :: FullInterpolationType
fitEaseOutCirc = FITEaseOutCirc

fitEaseInOutCirc :: FullInterpolationType
fitEaseInOutCirc = FITEaseInOutCirc

-- Back
fitEaseInBack :: FullInterpolationType
fitEaseInBack = FITEaseInBack

fitEaseOutBack :: FullInterpolationType
fitEaseOutBack = FITEaseOutBack

fitEaseInOutBack :: FullInterpolationType
fitEaseInOutBack = FITEaseInOutBack

-- Elastic
fitEaseInElastic :: FullInterpolationType
fitEaseInElastic = FITEaseInElastic

fitEaseOutElastic :: FullInterpolationType
fitEaseOutElastic = FITEaseOutElastic

fitEaseInOutElastic :: FullInterpolationType
fitEaseInOutElastic = FITEaseInOutElastic

-- Bounce
fitEaseInBounce :: FullInterpolationType
fitEaseInBounce = FITEaseInBounce

fitEaseOutBounce :: FullInterpolationType
fitEaseOutBounce = FITEaseOutBounce

fitEaseInOutBounce :: FullInterpolationType
fitEaseInOutBounce = FITEaseInOutBounce

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // spatial // tangent
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spatial tangent for position keyframes.
-- |
-- | Defines the direction and magnitude of motion path tangents.
-- | Used for bezier paths between position keyframes.
newtype SpatialTangent = SpatialTangent
  { x :: Number
  , y :: Number
  , z :: Number
  }

derive instance eqSpatialTangent :: Eq SpatialTangent

instance showSpatialTangent :: Show SpatialTangent where
  show (SpatialTangent t) = 
    "SpatialTangent(" <> show t.x <> ", " <> show t.y <> ", " <> show t.z <> ")"

-- | Create spatial tangent
mkSpatialTangent :: Number -> Number -> Number -> SpatialTangent
mkSpatialTangent x y z = SpatialTangent { x, y, z }

-- | Default spatial tangent at origin
defaultSpatialTangent :: SpatialTangent
defaultSpatialTangent = SpatialTangent { x: 0.0, y: 0.0, z: 0.0 }

-- | Zero spatial tangent (alias for defaultSpatialTangent)
spatialTangentZero :: SpatialTangent
spatialTangentZero = defaultSpatialTangent

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // bezier // handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bezier handle for temporal interpolation.
-- |
-- | Defines the control point for bezier curve interpolation.
-- | Frame is relative to keyframe position (negative for in-handle).
-- | Value is the influence amount.
newtype BezierHandle = BezierHandle
  { frame :: Number     -- Relative frame offset (negative for in-handle)
  , value :: Number     -- Value influence
  , enabled :: Boolean  -- Is this handle active?
  }

derive instance eqBezierHandle :: Eq BezierHandle

instance showBezierHandle :: Show BezierHandle where
  show (BezierHandle h) = 
    "BezierHandle(" <> show h.frame <> ", " <> show h.value <> 
    (if h.enabled then ", enabled" else ", disabled") <> ")"

-- | Create bezier handle
mkBezierHandle :: Number -> Number -> Boolean -> BezierHandle
mkBezierHandle frame value enabled = BezierHandle { frame, value, enabled }

-- | Default in-handle (before keyframe)
defaultInHandle :: BezierHandle
defaultInHandle = BezierHandle { frame: -5.0, value: 0.0, enabled: true }

-- | Default out-handle (after keyframe)
defaultOutHandle :: BezierHandle
defaultOutHandle = BezierHandle { frame: 5.0, value: 0.0, enabled: true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // control // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Control mode for bezier handles.
-- |
-- | Determines how in/out handles relate to each other.
data ControlMode
  = CMSymmetric   -- Handles mirror each other exactly
  | CMSmooth      -- Handles are colinear but can have different lengths
  | CMCorner      -- Handles are independent

derive instance eqControlMode :: Eq ControlMode
derive instance ordControlMode :: Ord ControlMode

instance showControlMode :: Show ControlMode where
  show = controlModeToString

-- | All control modes for enumeration
allControlModes :: Array ControlMode
allControlModes = [ CMSymmetric, CMSmooth, CMCorner ]

-- | Convert control mode to string
controlModeToString :: ControlMode -> String
controlModeToString CMSymmetric = "symmetric"
controlModeToString CMSmooth = "smooth"
controlModeToString CMCorner = "corner"

-- | Parse control mode from string
controlModeFromString :: String -> Maybe ControlMode
controlModeFromString "symmetric" = Just CMSymmetric
controlModeFromString "smooth" = Just CMSmooth
controlModeFromString "corner" = Just CMCorner
controlModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // extended // keyframe // data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extended keyframe interpolation data.
-- |
-- | Contains all the interpolation settings for a keyframe:
-- | - Temporal: interpolation type, bezier handles, control mode
-- | - Spatial: tangent vectors for motion paths (position properties only)
newtype ExtendedKeyframeData = ExtendedKeyframeData
  { interpolation :: FullInterpolationType
  , inHandle :: BezierHandle
  , outHandle :: BezierHandle
  , controlMode :: ControlMode
  , spatialInTangent :: Maybe SpatialTangent
  , spatialOutTangent :: Maybe SpatialTangent
  }

derive instance eqExtendedKeyframeData :: Eq ExtendedKeyframeData

instance showExtendedKeyframeData :: Show ExtendedKeyframeData where
  show (ExtendedKeyframeData d) = 
    "ExtendedKeyframeData(" <> show d.interpolation <> ")"

-- | Default extended keyframe data (linear interpolation)
defaultExtendedKeyframeData :: ExtendedKeyframeData
defaultExtendedKeyframeData = ExtendedKeyframeData
  { interpolation: FITLinear
  , inHandle: defaultInHandle
  , outHandle: defaultOutHandle
  , controlMode: CMSmooth
  , spatialInTangent: Nothing
  , spatialOutTangent: Nothing
  }
