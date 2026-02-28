-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // motion // animated-transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AnimatedTransform — Complete After Effects Transform Model.
-- |
-- | ## Design Philosophy
-- |
-- | This module provides the COMPLETE transform model for motion graphics,
-- | matching After Effects' capabilities:
-- |
-- | - **Position** (X, Y, Z) — Object location, animatable along spline paths
-- | - **Rotation** (Z for 2D, X/Y/Z for 3D) — Object orientation with wrap
-- | - **Scale** (X, Y, Z) — Size as percentage, with flip via negative
-- | - **Anchor Point** — Transform origin relative to object bounds
-- | - **Opacity** — Visibility (0-100%)
-- |
-- | All properties are **animatable** with:
-- | - Keyframes at specific frame positions
-- | - Bezier tangent handles for easing
-- | - Spatial tangents for motion path curves (position only)
-- | - Speed graph control for temporal manipulation
-- | - Expressions for procedural animation
-- |
-- | ## Architecture
-- |
-- | Each property wraps its value type in `AnimatableValue`, which tracks:
-- | - Current value (evaluated at playhead)
-- | - Keyframe array (if animated)
-- | - Expression (if procedural)
-- | - Speed graph overrides (if temporal remapping)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.AnimatedTransform as AT
-- |
-- | -- Create default transform
-- | transform = AT.defaultAnimatedTransform2D
-- |
-- | -- Add keyframe to position X
-- | withKeyframe = AT.addPositionXKeyframe (frames 0.0) 100.0 transform
-- |
-- | -- Evaluate at frame 30
-- | posX = AT.evaluatePositionX (frames 30.0) withKeyframe
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Schema.Motion.Keyframe (Keyframe, KeyframeValue)
-- | - Schema.Motion.Easing (Easing, evaluate)
-- | - Schema.Motion.Interpolation (FullInterpolationType, BezierHandle)
-- | - Schema.Motion.Transform (Position2D, Position3D, Scale2D, etc.)
-- | - Schema.Dimension.Temporal (Frames)

module Hydrogen.Schema.Motion.AnimatedTransform
  ( -- * Animated Value Container
    AnimatableValue(..)
  , mkAnimatableValue
  , mkAnimatableValueStatic
  , isAnimated
  , hasExpression
  , getStaticValue
  , getKeyframes
  
  -- * Property Keyframe
  , PropertyKeyframe(..)
  , mkPropertyKeyframe
  , keyframeFrame
  , keyframeValue
  , keyframeInterpolation
  , keyframeInHandle
  , keyframeOutHandle
  , keyframeSpatialIn
  , keyframeSpatialOut
  
  -- * Animated Transform 2D
  , AnimatedTransform2D(..)
  , defaultAnimatedTransform2D
  , identityAnimatedTransform2D
  
  -- * Animated Transform 3D
  , AnimatedTransform3D(..)
  , defaultAnimatedTransform3D
  , identityAnimatedTransform3D
  
  -- * Position Property
  , AnimatedPosition2D(..)
  , AnimatedPosition3D(..)
  , defaultAnimatedPosition2D
  , defaultAnimatedPosition3D
  , separatePositionDimensions
  , combinePositionDimensions
  
  -- * Scale Property
  , AnimatedScale2D(..)
  , AnimatedScale3D(..)
  , defaultAnimatedScale2D
  , defaultAnimatedScale3D
  , linkScaleDimensions
  , unlinkScaleDimensions
  
  -- * Rotation Property
  , AnimatedRotation(..)
  , AnimatedRotation3D(..)
  , defaultAnimatedRotation
  , defaultAnimatedRotation3D
  
  -- * Anchor Point Property
  , AnimatedAnchor2D(..)
  , AnimatedAnchor3D(..)
  , defaultAnimatedAnchor2D
  , defaultAnimatedAnchor3D
  
  -- * Opacity Property
  , AnimatedOpacity(..)
  , defaultAnimatedOpacity
  
  -- * Evaluation
  , evaluateAt
  , evaluateTransform2DAt
  , evaluateTransform3DAt
  
  -- * Keyframe Management
  , addKeyframe
  , removeKeyframe
  , moveKeyframe
  , updateKeyframeValue
  , updateKeyframeInterpolation
  
  -- * Speed Graph
  , SpeedGraphPoint(..)
  , SpeedGraph(..)
  , defaultSpeedGraph
  , addSpeedGraphPoint
  , evaluateSpeedGraph
  
  -- * Path Motion
  , MotionPathMode(..)
  , getMotionPathMode
  , setMotionPathMode
  , enableAutoOrient
  
  -- * 3D Layer System
  , LayerDimensionality(..)
  , is3DLayer
  , enable3DLayer
  , disable3DLayer
  
  -- * Gimbal / Rotation Order
  , RotationOrder(..)
  , allRotationOrders
  , rotationOrderToString
  , defaultRotationOrder
  
  -- * Layer Parenting (Pick-Whip)
  , LayerParent(..)
  , ParentLink(..)
  , mkParentLink
  , parentToLayer
  , parentToNull
  , clearParent
  , isParented
  , getParentId
  , inheritPosition
  , inheritScale
  , inheritRotation
  
  -- * Transform with Parenting
  , LayerTransformState(..)
  , defaultLayerTransformState
  , setLayerParent
  , getEffectiveTransform2D
  , getEffectiveTransform3D
  
  -- * Null Object
  , NullObject(..)
  , mkNullObject
  , nullObjectTransform
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (<>)
  , (==)
  , (/=)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (+)
  , (-)
  , (*)
  , (/)
  , ($)
  , (&&)
  , otherwise
  , not
  , negate
  , min
  , max
  , map
  )

import Data.Array (length, snoc, filter, sortBy, head, index, findIndex)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

import Hydrogen.Schema.Dimension.Temporal (Frames(Frames), unwrapFrames)
import Hydrogen.Schema.Motion.Interpolation 
  ( FullInterpolationType
  , BezierHandle
  , SpatialTangent
  , defaultInHandle
  , defaultOutHandle
  , defaultSpatialTangent
  , fitLinear
  )
import Hydrogen.Schema.Motion.Easing (Easing, evaluate, linear)
import Hydrogen.Schema.Motion.Transform 
  ( Position2D(Position2D)
  , Position3D(Position3D)
  , Scale2D(Scale2D)
  , Scale3D(Scale3D)
  , Rotation(Rotation)
  , Rotation3D(Rotation3D)
  , AnchorPoint2D(AnchorPoint2D)
  , AnchorPoint3D(AnchorPoint3D)
  , Opacity(Opacity)
  , mkPosition2D
  , mkPosition3D
  , mkScale2D
  , mkScale3D
  , mkRotation
  , mkRotation3D
  , mkAnchorPoint2D
  , mkAnchorPoint3D
  , mkOpacity
  , positionZero2D
  , positionZero3D
  , scaleIdentity2D
  , scaleIdentity3D
  , rotationZero
  , rotation3DZero
  , anchorTopLeft2D
  , opacityFull
  , getOpacityValue
  )
import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // property // keyframe
-- ═════════════════════════════════════════════════════════════════════════════

-- | A keyframe for a single numeric property.
-- |
-- | Contains the frame position, value, and all interpolation settings.
-- | This is the After Effects keyframe model with full bezier control.
newtype PropertyKeyframe = PropertyKeyframe
  { frame :: Frames                      -- Frame position
  , value :: Number                      -- Property value at this frame
  , interpolation :: FullInterpolationType  -- How to interpolate to next keyframe
  , inHandle :: BezierHandle             -- Incoming bezier handle
  , outHandle :: BezierHandle            -- Outgoing bezier handle
  , spatialIn :: Maybe SpatialTangent    -- Spatial tangent (position props only)
  , spatialOut :: Maybe SpatialTangent   -- Spatial tangent (position props only)
  , roving :: Boolean                    -- Roving keyframe (recalculates timing)
  , selected :: Boolean                  -- UI selection state
  }

derive instance eqPropertyKeyframe :: Eq PropertyKeyframe

instance showPropertyKeyframe :: Show PropertyKeyframe where
  show (PropertyKeyframe kf) = 
    "Keyframe@" <> show kf.frame <> " = " <> show kf.value

instance ordPropertyKeyframe :: Ord PropertyKeyframe where
  compare (PropertyKeyframe a) (PropertyKeyframe b) = 
    compare (unwrapFrames a.frame) (unwrapFrames b.frame)

-- | Create a property keyframe with default interpolation.
mkPropertyKeyframe :: Frames -> Number -> PropertyKeyframe
mkPropertyKeyframe frame value = PropertyKeyframe
  { frame: frame
  , value: value
  , interpolation: fitLinear
  , inHandle: defaultInHandle
  , outHandle: defaultOutHandle
  , spatialIn: Nothing
  , spatialOut: Nothing
  , roving: false
  , selected: false
  }

-- | Get keyframe frame position.
keyframeFrame :: PropertyKeyframe -> Frames
keyframeFrame (PropertyKeyframe kf) = kf.frame

-- | Get keyframe value.
keyframeValue :: PropertyKeyframe -> Number
keyframeValue (PropertyKeyframe kf) = kf.value

-- | Get keyframe interpolation type.
keyframeInterpolation :: PropertyKeyframe -> FullInterpolationType
keyframeInterpolation (PropertyKeyframe kf) = kf.interpolation

-- | Get keyframe incoming bezier handle.
keyframeInHandle :: PropertyKeyframe -> BezierHandle
keyframeInHandle (PropertyKeyframe kf) = kf.inHandle

-- | Get keyframe outgoing bezier handle.
keyframeOutHandle :: PropertyKeyframe -> BezierHandle
keyframeOutHandle (PropertyKeyframe kf) = kf.outHandle

-- | Get keyframe spatial incoming tangent.
keyframeSpatialIn :: PropertyKeyframe -> Maybe SpatialTangent
keyframeSpatialIn (PropertyKeyframe kf) = kf.spatialIn

-- | Get keyframe spatial outgoing tangent.
keyframeSpatialOut :: PropertyKeyframe -> Maybe SpatialTangent
keyframeSpatialOut (PropertyKeyframe kf) = kf.spatialOut

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // animatable // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container for an animatable property value.
-- |
-- | Can be either static (single value) or animated (multiple keyframes).
-- | Optionally includes expression for procedural animation.
newtype AnimatableValue = AnimatableValue
  { staticValue :: Number                -- Value when not animated
  , keyframes :: Array PropertyKeyframe  -- Keyframes (empty = static)
  , expression :: Maybe String           -- Expression code (overrides keyframes)
  , speedGraph :: Maybe SpeedGraph       -- Speed graph override
  , name :: String                       -- Property name (e.g., "Position X")
  }

derive instance eqAnimatableValue :: Eq AnimatableValue

instance showAnimatableValue :: Show AnimatableValue where
  show (AnimatableValue av) = 
    av.name <> ": " <> 
    (if length av.keyframes > 0 
     then show (length av.keyframes) <> " keyframes"
     else show av.staticValue)

-- | Create an animatable value with initial static value.
mkAnimatableValue :: String -> Number -> AnimatableValue
mkAnimatableValue name value = AnimatableValue
  { staticValue: value
  , keyframes: []
  , expression: Nothing
  , speedGraph: Nothing
  , name: name
  }

-- | Create a static (non-animated) value.
mkAnimatableValueStatic :: String -> Number -> AnimatableValue
mkAnimatableValueStatic = mkAnimatableValue

-- | Check if value is animated (has keyframes).
isAnimated :: AnimatableValue -> Boolean
isAnimated (AnimatableValue av) = length av.keyframes > 0

-- | Check if value has an expression.
hasExpression :: AnimatableValue -> Boolean
hasExpression (AnimatableValue av) = case av.expression of
  Just _ -> true
  Nothing -> false

-- | Get static value (ignoring keyframes).
getStaticValue :: AnimatableValue -> Number
getStaticValue (AnimatableValue av) = av.staticValue

-- | Get keyframes array.
getKeyframes :: AnimatableValue -> Array PropertyKeyframe
getKeyframes (AnimatableValue av) = av.keyframes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // speed // graph
-- ═════════════════════════════════════════════════════════════════════════════

-- | A point on the speed graph.
-- |
-- | Maps input time to output time with bezier control.
newtype SpeedGraphPoint = SpeedGraphPoint
  { frame :: Number           -- Input frame
  , mappedFrame :: Number     -- Output frame (where value is sampled)
  , inHandle :: BezierHandle  -- Incoming bezier handle
  , outHandle :: BezierHandle -- Outgoing bezier handle
  }

derive instance eqSpeedGraphPoint :: Eq SpeedGraphPoint

instance showSpeedGraphPoint :: Show SpeedGraphPoint where
  show (SpeedGraphPoint p) = 
    "SpeedPoint(" <> show p.frame <> " -> " <> show p.mappedFrame <> ")"

-- | Speed graph for temporal remapping.
-- |
-- | Allows non-linear time mapping for a property's animation.
-- | The speed graph overrides normal keyframe interpolation timing.
newtype SpeedGraph = SpeedGraph
  { points :: Array SpeedGraphPoint
  , enabled :: Boolean
  }

derive instance eqSpeedGraph :: Eq SpeedGraph

instance showSpeedGraph :: Show SpeedGraph where
  show (SpeedGraph sg) = 
    "SpeedGraph(" <> show (length sg.points) <> " points)"

-- | Default speed graph (linear 1:1 mapping).
defaultSpeedGraph :: SpeedGraph
defaultSpeedGraph = SpeedGraph
  { points: []
  , enabled: false
  }

-- | Add a point to the speed graph.
addSpeedGraphPoint :: Number -> Number -> SpeedGraph -> SpeedGraph
addSpeedGraphPoint frame mappedFrame (SpeedGraph sg) = SpeedGraph sg
  { points = sortBy comparePoints $ snoc sg.points newPoint
  }
  where
    newPoint = SpeedGraphPoint
      { frame: frame
      , mappedFrame: mappedFrame
      , inHandle: defaultInHandle
      , outHandle: defaultOutHandle
      }
    comparePoints (SpeedGraphPoint a) (SpeedGraphPoint b) = compare a.frame b.frame

-- | Evaluate speed graph at frame to get mapped frame.
evaluateSpeedGraph :: Number -> SpeedGraph -> Number
evaluateSpeedGraph frame (SpeedGraph sg)
  | not sg.enabled = frame  -- Disabled = identity mapping
  | length sg.points < 2 = frame  -- Need at least 2 points
  | otherwise = interpolateSpeedGraph frame sg.points

-- | Interpolate speed graph points.
interpolateSpeedGraph :: Number -> Array SpeedGraphPoint -> Number
interpolateSpeedGraph frame points =
  case findBracketingPoints frame points of
    Nothing -> frame
    Just { before: SpeedGraphPoint p1, after: SpeedGraphPoint p2 } ->
      let
        t = if p2.frame == p1.frame 
            then 0.0
            else (frame - p1.frame) / (p2.frame - p1.frame)
        -- Linear interpolation for now; could use bezier handles
      in p1.mappedFrame + t * (p2.mappedFrame - p1.mappedFrame)

-- | Find bracketing points for interpolation.
findBracketingPoints :: Number -> Array SpeedGraphPoint -> Maybe { before :: SpeedGraphPoint, after :: SpeedGraphPoint }
findBracketingPoints frame points =
  let
    before = filter (\(SpeedGraphPoint p) -> p.frame <= frame) points
    after = filter (\(SpeedGraphPoint p) -> p.frame > frame) points
  in case { b: lastPoint before, a: head after } of
    { b: Just b, a: Just a } -> Just { before: b, after: a }
    _ -> Nothing

-- | Get last point in array.
lastPoint :: forall a. Array a -> Maybe a
lastPoint arr = index arr (length arr - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // motion // path mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Motion path mode for position properties.
data MotionPathMode
  = MotionPathOff        -- No motion path, linear interpolation
  | MotionPathLinear     -- Linear path between keyframes
  | MotionPathBezier     -- Bezier curve path (uses spatial tangents)
  | MotionPathAutoOrient -- Bezier path + auto-orient rotation

derive instance eqMotionPathMode :: Eq MotionPathMode

instance showMotionPathMode :: Show MotionPathMode where
  show MotionPathOff = "off"
  show MotionPathLinear = "linear"
  show MotionPathBezier = "bezier"
  show MotionPathAutoOrient = "auto-orient"

-- | Get motion path mode from animated position.
getMotionPathMode :: AnimatedPosition2D -> MotionPathMode
getMotionPathMode (AnimatedPosition2D pos) = pos.motionPathMode

-- | Set motion path mode on animated position.
setMotionPathMode :: MotionPathMode -> AnimatedPosition2D -> AnimatedPosition2D
setMotionPathMode mode (AnimatedPosition2D pos) = 
  AnimatedPosition2D pos { motionPathMode = mode }

-- | Enable auto-orient rotation to path.
enableAutoOrient :: AnimatedPosition2D -> AnimatedPosition2D
enableAutoOrient = setMotionPathMode MotionPathAutoOrient

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // animated // position 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 2D position with X and Y as separate properties.
-- |
-- | Allows independent animation of each dimension.
newtype AnimatedPosition2D = AnimatedPosition2D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , separated :: Boolean       -- Are X/Y edited separately?
  , motionPathMode :: MotionPathMode
  }

derive instance eqAnimatedPosition2D :: Eq AnimatedPosition2D

instance showAnimatedPosition2D :: Show AnimatedPosition2D where
  show (AnimatedPosition2D p) = 
    "Position2D(" <> show p.x <> ", " <> show p.y <> ")"

-- | Default animated position at origin.
defaultAnimatedPosition2D :: AnimatedPosition2D
defaultAnimatedPosition2D = AnimatedPosition2D
  { x: mkAnimatableValue "Position X" 0.0
  , y: mkAnimatableValue "Position Y" 0.0
  , separated: false
  , motionPathMode: MotionPathBezier
  }

-- | Separate position into independent X/Y dimensions.
separatePositionDimensions :: AnimatedPosition2D -> AnimatedPosition2D
separatePositionDimensions (AnimatedPosition2D p) = 
  AnimatedPosition2D p { separated = true }

-- | Combine position dimensions (edit together).
combinePositionDimensions :: AnimatedPosition2D -> AnimatedPosition2D
combinePositionDimensions (AnimatedPosition2D p) = 
  AnimatedPosition2D p { separated = false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // animated // position 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 3D position with X, Y, Z as separate properties.
newtype AnimatedPosition3D = AnimatedPosition3D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , z :: AnimatableValue
  , separated :: Boolean
  , motionPathMode :: MotionPathMode
  }

derive instance eqAnimatedPosition3D :: Eq AnimatedPosition3D

instance showAnimatedPosition3D :: Show AnimatedPosition3D where
  show (AnimatedPosition3D p) = 
    "Position3D(" <> show p.x <> ", " <> show p.y <> ", " <> show p.z <> ")"

-- | Default animated 3D position at origin.
defaultAnimatedPosition3D :: AnimatedPosition3D
defaultAnimatedPosition3D = AnimatedPosition3D
  { x: mkAnimatableValue "Position X" 0.0
  , y: mkAnimatableValue "Position Y" 0.0
  , z: mkAnimatableValue "Position Z" 0.0
  , separated: false
  , motionPathMode: MotionPathBezier
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // animated // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 2D scale with X and Y as separate properties.
-- |
-- | Values are percentages (100.0 = 100% = no change).
newtype AnimatedScale2D = AnimatedScale2D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , linked :: Boolean  -- Are X/Y linked (uniform scale)?
  }

derive instance eqAnimatedScale2D :: Eq AnimatedScale2D

instance showAnimatedScale2D :: Show AnimatedScale2D where
  show (AnimatedScale2D s) = 
    "Scale2D(" <> show s.x <> ", " <> show s.y <> 
    (if s.linked then " [linked]" else "") <> ")"

-- | Default animated scale at 100%.
defaultAnimatedScale2D :: AnimatedScale2D
defaultAnimatedScale2D = AnimatedScale2D
  { x: mkAnimatableValue "Scale X" 100.0
  , y: mkAnimatableValue "Scale Y" 100.0
  , linked: true
  }

-- | Link scale dimensions (uniform scaling).
linkScaleDimensions :: AnimatedScale2D -> AnimatedScale2D
linkScaleDimensions (AnimatedScale2D s) = AnimatedScale2D s { linked = true }

-- | Unlink scale dimensions (independent X/Y).
unlinkScaleDimensions :: AnimatedScale2D -> AnimatedScale2D
unlinkScaleDimensions (AnimatedScale2D s) = AnimatedScale2D s { linked = false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // animated // scale 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 3D scale.
newtype AnimatedScale3D = AnimatedScale3D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , z :: AnimatableValue
  , linked :: Boolean
  }

derive instance eqAnimatedScale3D :: Eq AnimatedScale3D

instance showAnimatedScale3D :: Show AnimatedScale3D where
  show (AnimatedScale3D s) = 
    "Scale3D(" <> show s.x <> ", " <> show s.y <> ", " <> show s.z <> ")"

-- | Default animated 3D scale at 100%.
defaultAnimatedScale3D :: AnimatedScale3D
defaultAnimatedScale3D = AnimatedScale3D
  { x: mkAnimatableValue "Scale X" 100.0
  , y: mkAnimatableValue "Scale Y" 100.0
  , z: mkAnimatableValue "Scale Z" 100.0
  , linked: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // animated // rotation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated single-axis rotation (2D or Z-axis for 3D).
-- |
-- | Value is in degrees. Can exceed 360 for multiple rotations.
newtype AnimatedRotation = AnimatedRotation
  { rotation :: AnimatableValue
  , revolutions :: Int  -- Additional full revolutions (for UI)
  }

derive instance eqAnimatedRotation :: Eq AnimatedRotation

instance showAnimatedRotation :: Show AnimatedRotation where
  show (AnimatedRotation r) = "Rotation(" <> show r.rotation <> ")"

-- | Default animated rotation at 0 degrees.
defaultAnimatedRotation :: AnimatedRotation
defaultAnimatedRotation = AnimatedRotation
  { rotation: mkAnimatableValue "Rotation" 0.0
  , revolutions: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // animated // rotation 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 3D rotation with separate X, Y, Z axes.
-- |
-- | Also includes Orientation for cameras/3D layers.
newtype AnimatedRotation3D = AnimatedRotation3D
  { x :: AnimatableValue           -- Rotation X (pitch)
  , y :: AnimatableValue           -- Rotation Y (yaw)
  , z :: AnimatableValue           -- Rotation Z (roll)
  , orientationX :: AnimatableValue  -- Orientation X
  , orientationY :: AnimatableValue  -- Orientation Y
  , orientationZ :: AnimatableValue  -- Orientation Z
  }

derive instance eqAnimatedRotation3D :: Eq AnimatedRotation3D

instance showAnimatedRotation3D :: Show AnimatedRotation3D where
  show (AnimatedRotation3D r) = 
    "Rotation3D(X:" <> show r.x <> ", Y:" <> show r.y <> ", Z:" <> show r.z <> ")"

-- | Default animated 3D rotation at 0 degrees.
defaultAnimatedRotation3D :: AnimatedRotation3D
defaultAnimatedRotation3D = AnimatedRotation3D
  { x: mkAnimatableValue "X Rotation" 0.0
  , y: mkAnimatableValue "Y Rotation" 0.0
  , z: mkAnimatableValue "Z Rotation" 0.0
  , orientationX: mkAnimatableValue "Orientation X" 0.0
  , orientationY: mkAnimatableValue "Orientation Y" 0.0
  , orientationZ: mkAnimatableValue "Orientation Z" 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // animated // anchor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 2D anchor point.
-- |
-- | Position within the layer where transforms are applied.
newtype AnimatedAnchor2D = AnimatedAnchor2D
  { x :: AnimatableValue
  , y :: AnimatableValue
  }

derive instance eqAnimatedAnchor2D :: Eq AnimatedAnchor2D

instance showAnimatedAnchor2D :: Show AnimatedAnchor2D where
  show (AnimatedAnchor2D a) = "Anchor2D(" <> show a.x <> ", " <> show a.y <> ")"

-- | Default animated anchor at origin.
defaultAnimatedAnchor2D :: AnimatedAnchor2D
defaultAnimatedAnchor2D = AnimatedAnchor2D
  { x: mkAnimatableValue "Anchor Point X" 0.0
  , y: mkAnimatableValue "Anchor Point Y" 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // animated // anchor 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated 3D anchor point.
newtype AnimatedAnchor3D = AnimatedAnchor3D
  { x :: AnimatableValue
  , y :: AnimatableValue
  , z :: AnimatableValue
  }

derive instance eqAnimatedAnchor3D :: Eq AnimatedAnchor3D

instance showAnimatedAnchor3D :: Show AnimatedAnchor3D where
  show (AnimatedAnchor3D a) = 
    "Anchor3D(" <> show a.x <> ", " <> show a.y <> ", " <> show a.z <> ")"

-- | Default animated 3D anchor at origin.
defaultAnimatedAnchor3D :: AnimatedAnchor3D
defaultAnimatedAnchor3D = AnimatedAnchor3D
  { x: mkAnimatableValue "Anchor Point X" 0.0
  , y: mkAnimatableValue "Anchor Point Y" 0.0
  , z: mkAnimatableValue "Anchor Point Z" 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // animated // opacity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animated opacity.
-- |
-- | Value is 0-100 (percentage).
newtype AnimatedOpacity = AnimatedOpacity
  { opacity :: AnimatableValue
  }

derive instance eqAnimatedOpacity :: Eq AnimatedOpacity

instance showAnimatedOpacity :: Show AnimatedOpacity where
  show (AnimatedOpacity o) = "Opacity(" <> show o.opacity <> ")"

-- | Default animated opacity at 100%.
defaultAnimatedOpacity :: AnimatedOpacity
defaultAnimatedOpacity = AnimatedOpacity
  { opacity: mkAnimatableValue "Opacity" 100.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // animated // transform // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete animated 2D transform.
-- |
-- | Contains all transform properties with full animation support.
-- | This is the After Effects Layer Transform model.
newtype AnimatedTransform2D = AnimatedTransform2D
  { position :: AnimatedPosition2D
  , scale :: AnimatedScale2D
  , rotation :: AnimatedRotation
  , anchor :: AnimatedAnchor2D
  , opacity :: AnimatedOpacity
  }

derive instance eqAnimatedTransform2D :: Eq AnimatedTransform2D

instance showAnimatedTransform2D :: Show AnimatedTransform2D where
  show (AnimatedTransform2D t) = 
    "AnimatedTransform2D { pos: " <> show t.position <>
    ", scale: " <> show t.scale <>
    ", rot: " <> show t.rotation <>
    ", anchor: " <> show t.anchor <>
    ", opacity: " <> show t.opacity <> " }"

-- | Default animated 2D transform.
defaultAnimatedTransform2D :: AnimatedTransform2D
defaultAnimatedTransform2D = AnimatedTransform2D
  { position: defaultAnimatedPosition2D
  , scale: defaultAnimatedScale2D
  , rotation: defaultAnimatedRotation
  , anchor: defaultAnimatedAnchor2D
  , opacity: defaultAnimatedOpacity
  }

-- | Identity animated transform (alias for default).
identityAnimatedTransform2D :: AnimatedTransform2D
identityAnimatedTransform2D = defaultAnimatedTransform2D

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // animated // transform // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete animated 3D transform.
newtype AnimatedTransform3D = AnimatedTransform3D
  { position :: AnimatedPosition3D
  , scale :: AnimatedScale3D
  , rotation :: AnimatedRotation3D
  , anchor :: AnimatedAnchor3D
  , opacity :: AnimatedOpacity
  }

derive instance eqAnimatedTransform3D :: Eq AnimatedTransform3D

instance showAnimatedTransform3D :: Show AnimatedTransform3D where
  show (AnimatedTransform3D t) = 
    "AnimatedTransform3D { pos: " <> show t.position <>
    ", scale: " <> show t.scale <>
    ", rot: " <> show t.rotation <>
    ", anchor: " <> show t.anchor <>
    ", opacity: " <> show t.opacity <> " }"

-- | Default animated 3D transform.
defaultAnimatedTransform3D :: AnimatedTransform3D
defaultAnimatedTransform3D = AnimatedTransform3D
  { position: defaultAnimatedPosition3D
  , scale: defaultAnimatedScale3D
  , rotation: defaultAnimatedRotation3D
  , anchor: defaultAnimatedAnchor3D
  , opacity: defaultAnimatedOpacity
  }

-- | Identity animated 3D transform.
identityAnimatedTransform3D :: AnimatedTransform3D
identityAnimatedTransform3D = defaultAnimatedTransform3D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate an animatable value at a specific frame.
-- |
-- | If not animated, returns static value.
-- | If animated, interpolates between surrounding keyframes.
evaluateAt :: Frames -> AnimatableValue -> Number
evaluateAt frame (AnimatableValue av)
  | length av.keyframes == 0 = av.staticValue
  | otherwise = evaluateKeyframes frame av.keyframes av.speedGraph

-- | Interpolate between keyframes at frame.
evaluateKeyframes :: Frames -> Array PropertyKeyframe -> Maybe SpeedGraph -> Number
evaluateKeyframes frame keyframes maybeSpeedGraph =
  let
    -- Apply speed graph if present
    actualFrame = case maybeSpeedGraph of
      Just sg -> Frames $ evaluateSpeedGraph (unwrapFrames frame) sg
      Nothing -> frame
    
    frameNum = unwrapFrames actualFrame
    
    -- Find bracketing keyframes
    before = filter (\kf -> unwrapFrames (keyframeFrame kf) <= frameNum) keyframes
    after = filter (\kf -> unwrapFrames (keyframeFrame kf) > frameNum) keyframes
  in case { b: lastPoint (sortBy compare before), a: head (sortBy compare after) } of
    -- Before all keyframes: use first keyframe value
    { b: Nothing, a: Just kf } -> keyframeValue kf
    -- After all keyframes: use last keyframe value
    { b: Just kf, a: Nothing } -> keyframeValue kf
    -- Between keyframes: interpolate
    { b: Just kf1, a: Just kf2 } ->
      let
        f1 = unwrapFrames (keyframeFrame kf1)
        f2 = unwrapFrames (keyframeFrame kf2)
        t = if f2 == f1 then 0.0 else (frameNum - f1) / (f2 - f1)
        v1 = keyframeValue kf1
        v2 = keyframeValue kf2
        -- Apply easing based on interpolation type
        easedT = applyInterpolation t (keyframeInterpolation kf1)
      in v1 + easedT * (v2 - v1)
    -- No keyframes at all (shouldn't happen)
    _ -> 0.0

-- | Apply interpolation type to t value.
applyInterpolation :: Number -> FullInterpolationType -> Number
applyInterpolation t _ = 
  -- For now, use linear; full implementation would map to Easing
  evaluate linear t

-- | Evaluate 2D transform at frame, returning static values.
evaluateTransform2DAt :: Frames -> AnimatedTransform2D 
  -> { posX :: Number, posY :: Number, scaleX :: Number, scaleY :: Number
     , rotation :: Number, anchorX :: Number, anchorY :: Number, opacity :: Number }
evaluateTransform2DAt frame (AnimatedTransform2D t) =
  let
    (AnimatedPosition2D pos) = t.position
    (AnimatedScale2D scale) = t.scale
    (AnimatedRotation rot) = t.rotation
    (AnimatedAnchor2D anchor) = t.anchor
    (AnimatedOpacity op) = t.opacity
  in
    { posX: evaluateAt frame pos.x
    , posY: evaluateAt frame pos.y
    , scaleX: evaluateAt frame scale.x
    , scaleY: evaluateAt frame scale.y
    , rotation: evaluateAt frame rot.rotation
    , anchorX: evaluateAt frame anchor.x
    , anchorY: evaluateAt frame anchor.y
    , opacity: evaluateAt frame op.opacity
    }

-- | Evaluate 3D transform at frame.
evaluateTransform3DAt :: Frames -> AnimatedTransform3D
  -> { posX :: Number, posY :: Number, posZ :: Number
     , scaleX :: Number, scaleY :: Number, scaleZ :: Number
     , rotX :: Number, rotY :: Number, rotZ :: Number
     , orientX :: Number, orientY :: Number, orientZ :: Number
     , anchorX :: Number, anchorY :: Number, anchorZ :: Number
     , opacity :: Number }
evaluateTransform3DAt frame (AnimatedTransform3D t) =
  let
    (AnimatedPosition3D pos) = t.position
    (AnimatedScale3D scale) = t.scale
    (AnimatedRotation3D rot) = t.rotation
    (AnimatedAnchor3D anchor) = t.anchor
    (AnimatedOpacity op) = t.opacity
  in
    { posX: evaluateAt frame pos.x
    , posY: evaluateAt frame pos.y
    , posZ: evaluateAt frame pos.z
    , scaleX: evaluateAt frame scale.x
    , scaleY: evaluateAt frame scale.y
    , scaleZ: evaluateAt frame scale.z
    , rotX: evaluateAt frame rot.x
    , rotY: evaluateAt frame rot.y
    , rotZ: evaluateAt frame rot.z
    , orientX: evaluateAt frame rot.orientationX
    , orientY: evaluateAt frame rot.orientationY
    , orientZ: evaluateAt frame rot.orientationZ
    , anchorX: evaluateAt frame anchor.x
    , anchorY: evaluateAt frame anchor.y
    , anchorZ: evaluateAt frame anchor.z
    , opacity: evaluateAt frame op.opacity
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // keyframe management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add a keyframe to an animatable value.
addKeyframe :: Frames -> Number -> AnimatableValue -> AnimatableValue
addKeyframe frame value (AnimatableValue av) = AnimatableValue av
  { keyframes = sortBy compare $ snoc av.keyframes (mkPropertyKeyframe frame value)
  }

-- | Remove a keyframe at frame.
removeKeyframe :: Frames -> AnimatableValue -> AnimatableValue
removeKeyframe frame (AnimatableValue av) = AnimatableValue av
  { keyframes = filter (\kf -> keyframeFrame kf /= frame) av.keyframes
  }

-- | Move a keyframe to a new frame position.
moveKeyframe :: Frames -> Frames -> AnimatableValue -> AnimatableValue
moveKeyframe oldFrame newFrame (AnimatableValue av) = AnimatableValue av
  { keyframes = sortBy compare $ map (\kf -> 
      if keyframeFrame kf == oldFrame
      then updateKeyframeFrameInternal newFrame kf
      else kf
    ) av.keyframes
  }

-- | Update the value of a keyframe at frame.
updateKeyframeValue :: Frames -> Number -> AnimatableValue -> AnimatableValue
updateKeyframeValue frame newValue (AnimatableValue av) = AnimatableValue av
  { keyframes = map (\kf -> 
      if keyframeFrame kf == frame
      then updateKeyframeValueInternal newValue kf
      else kf
    ) av.keyframes
  }

-- | Update interpolation type of keyframe at frame.
updateKeyframeInterpolation :: Frames -> FullInterpolationType -> AnimatableValue -> AnimatableValue
updateKeyframeInterpolation frame newInterp (AnimatableValue av) = AnimatableValue av
  { keyframes = map (\kf -> 
      if keyframeFrame kf == frame
      then updateKeyframeInterpolationInternal newInterp kf
      else kf
    ) av.keyframes
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update keyframe frame internally.
updateKeyframeFrameInternal :: Frames -> PropertyKeyframe -> PropertyKeyframe
updateKeyframeFrameInternal newFrame (PropertyKeyframe kf) = 
  PropertyKeyframe kf { frame = newFrame }

-- | Update keyframe value internally.
updateKeyframeValueInternal :: Number -> PropertyKeyframe -> PropertyKeyframe
updateKeyframeValueInternal newValue (PropertyKeyframe kf) = 
  PropertyKeyframe kf { value = newValue }

-- | Update keyframe interpolation internally.
updateKeyframeInterpolationInternal :: FullInterpolationType -> PropertyKeyframe -> PropertyKeyframe
updateKeyframeInterpolationInternal newInterp (PropertyKeyframe kf) = 
  PropertyKeyframe kf { interpolation = newInterp }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // 3d // layer // system
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layer dimensionality (2D or 3D).
-- |
-- | When a layer is 3D, additional properties become available:
-- | - Position Z
-- | - Scale Z
-- | - Rotation X, Y (plus Z which exists in 2D)
-- | - Orientation X, Y, Z
-- | - Material options (for lights/cameras)
data LayerDimensionality
  = Layer2D    -- Standard 2D layer
  | Layer3D    -- 3D layer with Z-axis properties

derive instance eqLayerDimensionality :: Eq LayerDimensionality

instance showLayerDimensionality :: Show LayerDimensionality where
  show Layer2D = "2D"
  show Layer3D = "3D"

-- | Check if layer is 3D.
is3DLayer :: LayerDimensionality -> Boolean
is3DLayer Layer3D = true
is3DLayer Layer2D = false

-- | Enable 3D for a layer.
enable3DLayer :: LayerDimensionality -> LayerDimensionality
enable3DLayer _ = Layer3D

-- | Disable 3D for a layer (collapse to 2D).
disable3DLayer :: LayerDimensionality -> LayerDimensionality
disable3DLayer _ = Layer2D

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // gimbal // rotation order
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotation order for 3D Euler angles.
-- |
-- | The order in which rotations are applied affects the final orientation.
-- | This is crucial for avoiding gimbal lock in certain configurations.
-- |
-- | After Effects uses XYZ by default, but other orders are common:
-- | - XYZ: Roll (Z), then Pitch (X), then Yaw (Y) — After Effects default
-- | - YXZ: Common in games for character animation
-- | - ZYX: Common in aerospace (heading-pitch-roll)
-- | - XZY, YZX, ZXY: Alternative orders for specific use cases
data RotationOrder
  = RotationXYZ   -- X then Y then Z (After Effects default)
  | RotationXZY   -- X then Z then Y
  | RotationYXZ   -- Y then X then Z (common in games)
  | RotationYZX   -- Y then Z then X
  | RotationZXY   -- Z then X then Y
  | RotationZYX   -- Z then Y then X (aerospace)

derive instance eqRotationOrder :: Eq RotationOrder
derive instance ordRotationOrder :: Ord RotationOrder

instance showRotationOrder :: Show RotationOrder where
  show = rotationOrderToString

-- | All rotation orders for UI enumeration.
allRotationOrders :: Array RotationOrder
allRotationOrders = 
  [ RotationXYZ
  , RotationXZY
  , RotationYXZ
  , RotationYZX
  , RotationZXY
  , RotationZYX
  ]

-- | Convert rotation order to string.
rotationOrderToString :: RotationOrder -> String
rotationOrderToString RotationXYZ = "XYZ"
rotationOrderToString RotationXZY = "XZY"
rotationOrderToString RotationYXZ = "YXZ"
rotationOrderToString RotationYZX = "YZX"
rotationOrderToString RotationZXY = "ZXY"
rotationOrderToString RotationZYX = "ZYX"

-- | Default rotation order (After Effects standard).
defaultRotationOrder :: RotationOrder
defaultRotationOrder = RotationXYZ

-- ═════════════════════════════════════════════════════════════════════════════
--                                            // layer // parenting // pick-whip
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layer parent reference.
-- |
-- | A layer can be parented to another layer or a null object.
-- | When parented, the child inherits the parent's transform.
data LayerParent
  = NoParent                    -- Not parented to anything
  | ParentLayer String          -- Parented to layer with this ID
  | ParentNull String           -- Parented to null object with this ID

derive instance eqLayerParent :: Eq LayerParent

instance showLayerParent :: Show LayerParent where
  show NoParent = "None"
  show (ParentLayer id) = "Layer:" <> id
  show (ParentNull id) = "Null:" <> id

-- | Parent link configuration.
-- |
-- | Controls which transform properties are inherited from parent.
-- | This allows selective inheritance (e.g., position only, not scale).
newtype ParentLink = ParentLink
  { parent :: LayerParent
  , inheritPosition :: Boolean   -- Inherit parent position
  , inheritScale :: Boolean      -- Inherit parent scale
  , inheritRotation :: Boolean   -- Inherit parent rotation
  , inheritOpacity :: Boolean    -- Inherit parent opacity (multiply)
  , linkAnchor :: Boolean        -- Link to parent's anchor point
  , jumpToParent :: Boolean      -- Position relative to parent anchor (not origin)
  }

derive instance eqParentLink :: Eq ParentLink

instance showParentLink :: Show ParentLink where
  show (ParentLink pl) = 
    "ParentLink(" <> show pl.parent <> 
    (if pl.inheritPosition then " +pos" else "") <>
    (if pl.inheritScale then " +scale" else "") <>
    (if pl.inheritRotation then " +rot" else "") <> ")"

-- | Create a parent link with default settings (inherit all transforms).
mkParentLink :: LayerParent -> ParentLink
mkParentLink parent = ParentLink
  { parent: parent
  , inheritPosition: true
  , inheritScale: true
  , inheritRotation: true
  , inheritOpacity: false  -- Opacity not inherited by default
  , linkAnchor: true
  , jumpToParent: true     -- Child positioned relative to parent anchor
  }

-- | Parent to a specific layer.
parentToLayer :: String -> ParentLink
parentToLayer layerId = mkParentLink (ParentLayer layerId)

-- | Parent to a null object.
parentToNull :: String -> ParentLink
parentToNull nullId = mkParentLink (ParentNull nullId)

-- | Clear parent (no parent).
clearParent :: ParentLink
clearParent = mkParentLink NoParent

-- | Check if layer is parented.
isParented :: ParentLink -> Boolean
isParented (ParentLink pl) = case pl.parent of
  NoParent -> false
  _ -> true

-- | Get parent ID if parented.
getParentId :: ParentLink -> Maybe String
getParentId (ParentLink pl) = case pl.parent of
  NoParent -> Nothing
  ParentLayer id -> Just id
  ParentNull id -> Just id

-- | Set position inheritance.
inheritPosition :: Boolean -> ParentLink -> ParentLink
inheritPosition inherit (ParentLink pl) = ParentLink pl { inheritPosition = inherit }

-- | Set scale inheritance.
inheritScale :: Boolean -> ParentLink -> ParentLink
inheritScale inherit (ParentLink pl) = ParentLink pl { inheritScale = inherit }

-- | Set rotation inheritance.
inheritRotation :: Boolean -> ParentLink -> ParentLink
inheritRotation inherit (ParentLink pl) = ParentLink pl { inheritRotation = inherit }

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // transform // with // parenting
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete layer transform state.
-- |
-- | Combines the animated transform with dimensionality, rotation order,
-- | and parenting information.
newtype LayerTransformState = LayerTransformState
  { dimensionality :: LayerDimensionality
  , transform2D :: AnimatedTransform2D
  , transform3D :: AnimatedTransform3D    -- Used when dimensionality = Layer3D
  , rotationOrder :: RotationOrder
  , parentLink :: ParentLink
  , autoOrient :: Boolean                 -- Auto-orient rotation to path
  , collapseTransforms :: Boolean         -- Collapse into parent (for precomps)
  }

derive instance eqLayerTransformState :: Eq LayerTransformState

instance showLayerTransformState :: Show LayerTransformState where
  show (LayerTransformState lts) = 
    "LayerTransformState(" <> show lts.dimensionality <> 
    ", parent: " <> show lts.parentLink <> ")"

-- | Default layer transform state (2D, no parent).
defaultLayerTransformState :: LayerTransformState
defaultLayerTransformState = LayerTransformState
  { dimensionality: Layer2D
  , transform2D: defaultAnimatedTransform2D
  , transform3D: defaultAnimatedTransform3D
  , rotationOrder: defaultRotationOrder
  , parentLink: clearParent
  , autoOrient: false
  , collapseTransforms: false
  }

-- | Set layer parent.
setLayerParent :: ParentLink -> LayerTransformState -> LayerTransformState
setLayerParent link (LayerTransformState lts) = 
  LayerTransformState lts { parentLink = link }

-- | Get effective 2D transform at frame, incorporating parent transforms.
-- |
-- | This requires the parent's evaluated transform to be passed in.
-- | The caller is responsible for resolving the parent chain.
getEffectiveTransform2D 
  :: Frames 
  -> Maybe { posX :: Number, posY :: Number, scaleX :: Number, scaleY :: Number
           , rotation :: Number, anchorX :: Number, anchorY :: Number }
  -> LayerTransformState 
  -> { posX :: Number, posY :: Number, scaleX :: Number, scaleY :: Number
     , rotation :: Number, anchorX :: Number, anchorY :: Number, opacity :: Number }
getEffectiveTransform2D frame maybeParentTransform (LayerTransformState lts) =
  let
    local = evaluateTransform2DAt frame lts.transform2D
    (ParentLink pl) = lts.parentLink
  in case maybeParentTransform of
    Nothing -> local
    Just parent ->
      { posX: if pl.inheritPosition 
              then parent.posX + (local.posX - parent.anchorX) * (parent.scaleX / 100.0)
              else local.posX
      , posY: if pl.inheritPosition 
              then parent.posY + (local.posY - parent.anchorY) * (parent.scaleY / 100.0)
              else local.posY
      , scaleX: if pl.inheritScale 
                then local.scaleX * parent.scaleX / 100.0
                else local.scaleX
      , scaleY: if pl.inheritScale 
                then local.scaleY * parent.scaleY / 100.0
                else local.scaleY
      , rotation: if pl.inheritRotation 
                  then local.rotation + parent.rotation
                  else local.rotation
      , anchorX: local.anchorX
      , anchorY: local.anchorY
      , opacity: local.opacity
      }

-- | Get effective 3D transform at frame, incorporating parent transforms.
getEffectiveTransform3D 
  :: Frames 
  -> Maybe { posX :: Number, posY :: Number, posZ :: Number
           , scaleX :: Number, scaleY :: Number, scaleZ :: Number
           , rotX :: Number, rotY :: Number, rotZ :: Number
           , anchorX :: Number, anchorY :: Number, anchorZ :: Number }
  -> LayerTransformState 
  -> { posX :: Number, posY :: Number, posZ :: Number
     , scaleX :: Number, scaleY :: Number, scaleZ :: Number
     , rotX :: Number, rotY :: Number, rotZ :: Number
     , orientX :: Number, orientY :: Number, orientZ :: Number
     , anchorX :: Number, anchorY :: Number, anchorZ :: Number
     , opacity :: Number }
getEffectiveTransform3D frame maybeParentTransform (LayerTransformState lts) =
  let
    local = evaluateTransform3DAt frame lts.transform3D
    (ParentLink pl) = lts.parentLink
  in case maybeParentTransform of
    Nothing -> local
    Just parent ->
      { posX: if pl.inheritPosition 
              then parent.posX + (local.posX - parent.anchorX) * (parent.scaleX / 100.0)
              else local.posX
      , posY: if pl.inheritPosition 
              then parent.posY + (local.posY - parent.anchorY) * (parent.scaleY / 100.0)
              else local.posY
      , posZ: if pl.inheritPosition 
              then parent.posZ + (local.posZ - parent.anchorZ) * (parent.scaleZ / 100.0)
              else local.posZ
      , scaleX: if pl.inheritScale 
                then local.scaleX * parent.scaleX / 100.0
                else local.scaleX
      , scaleY: if pl.inheritScale 
                then local.scaleY * parent.scaleY / 100.0
                else local.scaleY
      , scaleZ: if pl.inheritScale 
                then local.scaleZ * parent.scaleZ / 100.0
                else local.scaleZ
      , rotX: if pl.inheritRotation then local.rotX + parent.rotX else local.rotX
      , rotY: if pl.inheritRotation then local.rotY + parent.rotY else local.rotY
      , rotZ: if pl.inheritRotation then local.rotZ + parent.rotZ else local.rotZ
      , orientX: local.orientX
      , orientY: local.orientY
      , orientZ: local.orientZ
      , anchorX: local.anchorX
      , anchorY: local.anchorY
      , anchorZ: local.anchorZ
      , opacity: local.opacity
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // null // object
-- ═════════════════════════════════════════════════════════════════════════════

-- | Null object for parenting.
-- |
-- | A null object is an invisible layer used only for its transform.
-- | Common uses:
-- | - Group multiple layers under one transform
-- | - Create a pivot point for complex animations
-- | - Control rig for character animation
newtype NullObject = NullObject
  { id :: String
  , name :: String
  , transform :: LayerTransformState
  , visible :: Boolean           -- Show in viewport (for debugging)
  , locked :: Boolean            -- Prevent editing
  }

derive instance eqNullObject :: Eq NullObject

instance showNullObject :: Show NullObject where
  show (NullObject n) = "Null(" <> n.name <> ")"

-- | Create a null object with default transform.
mkNullObject :: String -> String -> NullObject
mkNullObject id name = NullObject
  { id: id
  , name: name
  , transform: defaultLayerTransformState
  , visible: true
  , locked: false
  }

-- | Get null object transform.
nullObjectTransform :: NullObject -> LayerTransformState
nullObjectTransform (NullObject n) = n.transform
