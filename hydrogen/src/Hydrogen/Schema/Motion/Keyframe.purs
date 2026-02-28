-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // keyframe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyframe data for motion graphics animation.
-- |
-- | A keyframe represents a specific value at a specific point in time.
-- | The interpolation between keyframes is controlled by tangent handles
-- | and interpolation type.
-- |
-- | ## Keyframe Structure
-- |
-- | ```
-- |     ┌───┐ in tangent
-- |     │   │
-- | ────●───────●────  value
-- |         │   │
-- |         └───┘ out tangent
-- |     frame
-- | ```
-- |
-- | ## Interpolation Types
-- |
-- | - **Linear**: Straight line between keyframes
-- | - **Bezier**: Smooth curve controlled by tangent handles
-- | - **Hold**: Value stays constant until next keyframe
-- | - **Auto**: System calculates smooth tangents automatically
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.Keyframe as KF
-- | import Hydrogen.Schema.Dimension.Temporal (frames)
-- |
-- | -- Create a numeric keyframe
-- | kf = KF.keyframe (frames 30.0) (KF.NumberValue 100.0)
-- |
-- | -- With bezier easing
-- | kfEased = KF.withBezierTangents (KF.tangent 0.0 0.0) (KF.tangent 0.3 0.0) kf
-- |
-- | -- Create position keyframe
-- | posKf = KF.keyframe (frames 0.0) (KF.Vec2Value { x: 100.0, y: 200.0 })
-- | ```
module Hydrogen.Schema.Motion.Keyframe
  ( -- * Core Types
    Keyframe(..)
  , KeyframeId(..)
  , KeyframeValue(..)
  , Tangent(..)
  , InterpolationType(..)
  
  -- * Constructors
  , keyframe
  , keyframeWithId
  , tangent
  , tangentFlat
  , tangentAuto
  
  -- * Keyframe Builders
  , withInterpolation
  , withInTangent
  , withOutTangent
  , withBezierTangents
  , withHold
  , withLinear
  , withAuto
  
  -- * Accessors
  , frame
  , value
  , interpolationType
  , inTangent
  , outTangent
  , keyframeId
  
  -- * Predicates
  , isBezier
  , isHold
  , isLinear
  , isAuto
  
  -- * Operations
  , setFrame
  , setValue
  , shiftFrame
  
  -- * Value Operations
  , lerpValue
  , addValues
  , scaleValue
  ) where

import Prelude

import Data.Int (round)
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a keyframe
newtype KeyframeId = KeyframeId String

derive instance eqKeyframeId :: Eq KeyframeId
derive instance ordKeyframeId :: Ord KeyframeId

instance showKeyframeId :: Show KeyframeId where
  show (KeyframeId id) = "KF:" <> id

-- | Interpolation type between keyframes
data InterpolationType
  = Linear     -- Straight line interpolation
  | Bezier     -- Smooth curve with tangent handles
  | Hold       -- Value stays constant until next keyframe
  | Auto       -- System calculates smooth tangents

derive instance eqInterpolationType :: Eq InterpolationType

instance showInterpolationType :: Show InterpolationType where
  show Linear = "linear"
  show Bezier = "bezier"
  show Hold = "hold"
  show Auto = "auto"

-- | Tangent handle for bezier interpolation
-- |
-- | Represents the control point offset from the keyframe.
-- | - `x` is the time offset (frames, normalized)
-- | - `y` is the value offset (property units, normalized)
newtype Tangent = Tangent
  { x :: Number
  , y :: Number
  }

derive instance eqTangent :: Eq Tangent

instance showTangent :: Show Tangent where
  show (Tangent t) = "(" <> show t.x <> ", " <> show t.y <> ")"

-- | Keyframe value types
-- |
-- | Supports various property value types commonly used in motion graphics.
data KeyframeValue
  = NumberValue Number
  | Vec2Value { x :: Number, y :: Number }
  | Vec3Value { x :: Number, y :: Number, z :: Number }
  | ColorValue { r :: Number, g :: Number, b :: Number, a :: Number }
  | AngleValue Number  -- Degrees
  | PercentValue Number  -- 0-100

derive instance eqKeyframeValue :: Eq KeyframeValue

instance showKeyframeValue :: Show KeyframeValue where
  show (NumberValue n) = show n
  show (Vec2Value v) = "[" <> show v.x <> ", " <> show v.y <> "]"
  show (Vec3Value v) = "[" <> show v.x <> ", " <> show v.y <> ", " <> show v.z <> "]"
  show (ColorValue c) = "rgba(" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ", " <> show c.a <> ")"
  show (AngleValue a) = show a <> "deg"
  show (PercentValue p) = show p <> "%"

-- | Complete keyframe data
newtype Keyframe = Keyframe
  { id :: KeyframeId
  , frame :: Frames
  , value :: KeyframeValue
  , interpolation :: InterpolationType
  , inTangent :: Tangent
  , outTangent :: Tangent
  }

derive instance eqKeyframe :: Eq Keyframe

instance showKeyframe :: Show Keyframe where
  show (Keyframe kf) = 
    "Keyframe@" <> show kf.frame <> " = " <> show kf.value

instance ordKeyframe :: Ord Keyframe where
  compare (Keyframe a) (Keyframe b) = compare a.frame b.frame

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a basic keyframe with auto-generated ID
-- |
-- | Default interpolation is Auto with flat tangents.
keyframe :: Frames -> KeyframeValue -> Keyframe
keyframe fr val = Keyframe
  { id: generateId fr val
  , frame: fr
  , value: val
  , interpolation: Auto
  , inTangent: tangentFlat
  , outTangent: tangentFlat
  }

-- | Create keyframe with explicit ID
keyframeWithId :: KeyframeId -> Frames -> KeyframeValue -> Keyframe
keyframeWithId id fr val = Keyframe
  { id: id
  , frame: fr
  , value: val
  , interpolation: Auto
  , inTangent: tangentFlat
  , outTangent: tangentFlat
  }

-- | Create a tangent with explicit values
tangent :: Number -> Number -> Tangent
tangent x y = Tangent { x, y }

-- | Flat tangent (no influence)
tangentFlat :: Tangent
tangentFlat = Tangent { x: 0.0, y: 0.0 }

-- | Auto-calculated tangent marker
-- |
-- | When tangent is (0.33, 0.0), system will auto-calculate smooth tangent
tangentAuto :: Tangent
tangentAuto = Tangent { x: 0.33, y: 0.0 }

-- | Generate deterministic ID from frame and value
generateId :: Frames -> KeyframeValue -> KeyframeId
generateId (Frames f) val = 
  KeyframeId ("kf-" <> show (round f) <> "-" <> valueHash val)
  where
    valueHash :: KeyframeValue -> String
    valueHash (NumberValue n) = show (round (n * 1000.0))
    valueHash (Vec2Value v) = show (round (v.x * 100.0)) <> "x" <> show (round (v.y * 100.0))
    valueHash (Vec3Value v) = show (round (v.x * 100.0)) <> "x" <> show (round (v.y * 100.0)) <> "x" <> show (round (v.z * 100.0))
    valueHash (ColorValue c) = show (round (c.r * 255.0)) <> show (round (c.g * 255.0)) <> show (round (c.b * 255.0))
    valueHash (AngleValue a) = show (round a)
    valueHash (PercentValue p) = show (round p) <> "p"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // keyframe builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set interpolation type
withInterpolation :: InterpolationType -> Keyframe -> Keyframe
withInterpolation interp (Keyframe kf) = Keyframe kf { interpolation = interp }

-- | Set incoming tangent
withInTangent :: Tangent -> Keyframe -> Keyframe
withInTangent t (Keyframe kf) = Keyframe kf { inTangent = t }

-- | Set outgoing tangent
withOutTangent :: Tangent -> Keyframe -> Keyframe
withOutTangent t (Keyframe kf) = Keyframe kf { outTangent = t }

-- | Set both tangents for bezier interpolation
withBezierTangents :: Tangent -> Tangent -> Keyframe -> Keyframe
withBezierTangents inT outT (Keyframe kf) = Keyframe kf 
  { interpolation = Bezier
  , inTangent = inT
  , outTangent = outT
  }

-- | Set to hold interpolation
withHold :: Keyframe -> Keyframe
withHold = withInterpolation Hold

-- | Set to linear interpolation
withLinear :: Keyframe -> Keyframe
withLinear = withInterpolation Linear

-- | Set to auto interpolation
withAuto :: Keyframe -> Keyframe
withAuto = withInterpolation Auto

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get keyframe frame position
frame :: Keyframe -> Frames
frame (Keyframe kf) = kf.frame

-- | Get keyframe value
value :: Keyframe -> KeyframeValue
value (Keyframe kf) = kf.value

-- | Get interpolation type
interpolationType :: Keyframe -> InterpolationType
interpolationType (Keyframe kf) = kf.interpolation

-- | Get incoming tangent
inTangent :: Keyframe -> Tangent
inTangent (Keyframe kf) = kf.inTangent

-- | Get outgoing tangent
outTangent :: Keyframe -> Tangent
outTangent (Keyframe kf) = kf.outTangent

-- | Get keyframe ID
keyframeId :: Keyframe -> KeyframeId
keyframeId (Keyframe kf) = kf.id

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if keyframe uses bezier interpolation
isBezier :: Keyframe -> Boolean
isBezier kf = interpolationType kf == Bezier

-- | Check if keyframe uses hold interpolation
isHold :: Keyframe -> Boolean
isHold kf = interpolationType kf == Hold

-- | Check if keyframe uses linear interpolation
isLinear :: Keyframe -> Boolean
isLinear kf = interpolationType kf == Linear

-- | Check if keyframe uses auto interpolation
isAuto :: Keyframe -> Boolean
isAuto kf = interpolationType kf == Auto

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set keyframe to a new frame position
setFrame :: Frames -> Keyframe -> Keyframe
setFrame fr (Keyframe kf) = Keyframe kf { frame = fr }

-- | Set keyframe value
setValue :: KeyframeValue -> Keyframe -> Keyframe
setValue val (Keyframe kf) = Keyframe kf { value = val }

-- | Shift keyframe by frame offset
shiftFrame :: Frames -> Keyframe -> Keyframe
shiftFrame (Frames offset) (Keyframe kf) =
  let
    Frames f = kf.frame
    newFrame = max 0.0 (f + offset)
  in
    Keyframe kf { frame = Frames newFrame }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // value operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two values
-- |
-- | ```purescript
-- | interpolated = lerpValue 0.5 start end
-- | -- Returns value halfway between start and end
-- | ```
lerpValue :: Number -> KeyframeValue -> KeyframeValue -> KeyframeValue
lerpValue t (NumberValue a) (NumberValue b) = 
  NumberValue (a + (b - a) * t)
lerpValue t (Vec2Value a) (Vec2Value b) = 
  Vec2Value 
    { x: a.x + (b.x - a.x) * t
    , y: a.y + (b.y - a.y) * t
    }
lerpValue t (Vec3Value a) (Vec3Value b) = 
  Vec3Value 
    { x: a.x + (b.x - a.x) * t
    , y: a.y + (b.y - a.y) * t
    , z: a.z + (b.z - a.z) * t
    }
lerpValue t (ColorValue a) (ColorValue b) = 
  ColorValue 
    { r: a.r + (b.r - a.r) * t
    , g: a.g + (b.g - a.g) * t
    , b: a.b + (b.b - a.b) * t
    , a: a.a + (b.a - a.a) * t
    }
lerpValue t (AngleValue a) (AngleValue b) = 
  AngleValue (a + (b - a) * t)
lerpValue t (PercentValue a) (PercentValue b) = 
  PercentValue (a + (b - a) * t)
-- Mismatched types: return first value
lerpValue _ a _ = a

-- | Add two keyframe values
addValues :: KeyframeValue -> KeyframeValue -> KeyframeValue
addValues (NumberValue a) (NumberValue b) = NumberValue (a + b)
addValues (Vec2Value a) (Vec2Value b) = Vec2Value { x: a.x + b.x, y: a.y + b.y }
addValues (Vec3Value a) (Vec3Value b) = Vec3Value { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }
addValues (AngleValue a) (AngleValue b) = AngleValue (a + b)
addValues (PercentValue a) (PercentValue b) = PercentValue (a + b)
addValues a _ = a  -- Can't add mismatched or color values meaningfully

-- | Scale a keyframe value
scaleValue :: Number -> KeyframeValue -> KeyframeValue
scaleValue s (NumberValue n) = NumberValue (n * s)
scaleValue s (Vec2Value v) = Vec2Value { x: v.x * s, y: v.y * s }
scaleValue s (Vec3Value v) = Vec3Value { x: v.x * s, y: v.y * s, z: v.z * s }
scaleValue s (AngleValue a) = AngleValue (a * s)
scaleValue s (PercentValue p) = PercentValue (p * s)
scaleValue _ c = c  -- Can't scale colors meaningfully
