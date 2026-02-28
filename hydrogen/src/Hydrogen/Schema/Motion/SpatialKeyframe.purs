-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // motion // spatial-keyframe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spatial Keyframes — Motion path keyframes with bezier handles in 2D/3D space.
-- |
-- | ## After Effects Parity
-- |
-- | In After Effects, position keyframes have TWO sets of bezier handles:
-- |
-- | 1. **Spatial Handles**: Control the SHAPE of the motion path
-- |    - Visible in the composition viewport as path tangents
-- |    - Define the curve the object travels through space
-- |
-- | 2. **Temporal Handles**: Control the SPEED along the path
-- |    - Visible in the Graph Editor (speed graph / value graph)
-- |    - Define how fast the object moves between keyframes
-- |
-- | ## Architecture
-- |
-- | ```
-- |                    ┌─────────────────────────────────────┐
-- |                    │         SPATIAL DOMAIN              │
-- |                    │   (Composition Viewport)            │
-- |                    │                                     │
-- |       inSpatial ──►●────────────────●◄── outSpatial      │
-- |                   KF1              KF2                   │
-- |                    │   motion path curve                 │
-- |                    └─────────────────────────────────────┘
-- |
-- |                    ┌─────────────────────────────────────┐
-- |                    │         TEMPORAL DOMAIN             │
-- |                    │   (Graph Editor)                    │
-- |                    │                                     │
-- |                    │         ╭───────╮                   │
-- |      inTemporal ──►●────────╯       ╰────●◄── outTemporal│
-- |                   KF1                   KF2              │
-- |                    │   speed curve (ease in/out)         │
-- |                    └─────────────────────────────────────┘
-- | ```
-- |
-- | ## Roving Keyframes
-- |
-- | Roving keyframes auto-adjust their temporal position to create
-- | uniform speed along the motion path. The spatial position is fixed,
-- | but the time at which that position is reached adjusts automatically.
-- |
-- | ## Separate Dimensions
-- |
-- | Position can be animated as:
-- | - **Unified**: Single property with 2D/3D spatial handles
-- | - **Separated**: X, Y, Z as independent 1D value properties
-- |
-- | When separated, each dimension has its own keyframes and temporal
-- | curves, but no spatial handles (they're just value graphs).

module Hydrogen.Schema.Motion.SpatialKeyframe
  ( -- * Spatial Handle (2D)
    SpatialHandle2D
  , spatialHandle2D
  , spatialHandle2DZero
  , unwrapSpatialHandle2D
  
  -- * Spatial Handle (3D)
  , SpatialHandle3D
  , spatialHandle3D
  , spatialHandle3DZero
  , unwrapSpatialHandle3D
  
  -- * Temporal Handle
  , TemporalHandle
  , temporalHandle
  , temporalHandleLinear
  , temporalHandleEaseIn
  , temporalHandleEaseOut
  , temporalHandleEaseInOut
  , temporalHandleHold
  , unwrapTemporalHandle
  
  -- * Spatial Keyframe 2D
  , SpatialKeyframe2D
  , spatialKeyframe2D
  , spatialKeyframe2DLinear
  , spatialKeyframe2DWithHandles
  
  -- * Spatial Keyframe 3D
  , SpatialKeyframe3D
  , spatialKeyframe3D
  , spatialKeyframe3DLinear
  , spatialKeyframe3DWithHandles
  
  -- * Keyframe Flags
  , KeyframeFlags
  , defaultKeyframeFlags
  , setRoving
  , setLockToTime
  , setContinuousBezier
  , setAutoBezier
  
  -- * Spatial Interpolation Type
  , SpatialInterpolation(..)
  , spatialInterpolationToString
  , spatialInterpolationFromString
  
  -- * Temporal Interpolation Type  
  , TemporalInterpolation(..)
  , temporalInterpolationToString
  , temporalInterpolationFromString
  
  -- * Motion Path
  , MotionPath2D
  , motionPath2D
  , motionPath2DFromKeyframes
  , evaluateMotionPath2D
  , motionPathLength2D
  
  , MotionPath3D
  , motionPath3D
  , motionPath3DFromKeyframes
  , evaluateMotionPath3D
  , motionPathLength3D
  
  -- * Speed Graph
  , SpeedGraph
  , speedGraph
  , speedAt
  , averageSpeed
  , maxSpeed
  , minSpeed
  
  -- * Dimension Mode
  , DimensionMode(..)
  , dimensionModeToString
  , dimensionModeFromString
  
  -- * Accessors
  , keyframePosition2D
  , keyframePosition3D
  , keyframeFrame
  , keyframeSpatialIn2D
  , keyframeSpatialOut2D
  , keyframeSpatialIn3D
  , keyframeSpatialOut3D
  , keyframeTemporalIn
  , keyframeTemporalOut
  , keyframeFlags
  
  -- * Operations
  , setPosition2D
  , setPosition3D
  , setSpatialHandles2D
  , setSpatialHandles3D
  , setTemporalHandles
  , convertToRoving
  , convertToLinear
  , convertToBezier
  , convertToHold
  , convertToAuto
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , class Monoid
  , ($)
  , (#)
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , compare
  , min
  , max
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , show
  , map
  , pure
  , bind
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (length, index, foldl, zip, drop) as Array
import Data.Int (toNumber) as Int
import Data.Tuple (Tuple(Tuple), fst, snd)
import Hydrogen.Schema.Bounded (clampNumber)
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames), unwrapFrames)
import Hydrogen.Math.Core as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // spatial // handle 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spatial bezier handle in 2D space.
-- |
-- | Defines the tangent direction and magnitude for motion path curves.
-- | Coordinates are relative to the keyframe position.
-- |
-- | ```
-- |           handle (dx, dy)
-- |              ●
-- |             /
-- |            /
-- |           ●────────►  keyframe position
-- | ```
newtype SpatialHandle2D = SpatialHandle2D
  { dx :: Number  -- ^ X offset from keyframe
  , dy :: Number  -- ^ Y offset from keyframe
  }

derive instance eqSpatialHandle2D :: Eq SpatialHandle2D
derive instance ordSpatialHandle2D :: Ord SpatialHandle2D

instance showSpatialHandle2D :: Show SpatialHandle2D where
  show (SpatialHandle2D h) = "Spatial2D(" <> show h.dx <> ", " <> show h.dy <> ")"

-- | Create a 2D spatial handle.
spatialHandle2D :: Number -> Number -> SpatialHandle2D
spatialHandle2D dx dy = SpatialHandle2D { dx, dy }

-- | Zero-length handle (linear interpolation).
spatialHandle2DZero :: SpatialHandle2D
spatialHandle2DZero = SpatialHandle2D { dx: 0.0, dy: 0.0 }

-- | Extract handle values.
unwrapSpatialHandle2D :: SpatialHandle2D -> { dx :: Number, dy :: Number }
unwrapSpatialHandle2D (SpatialHandle2D h) = h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // spatial // handle 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spatial bezier handle in 3D space.
newtype SpatialHandle3D = SpatialHandle3D
  { dx :: Number
  , dy :: Number
  , dz :: Number
  }

derive instance eqSpatialHandle3D :: Eq SpatialHandle3D
derive instance ordSpatialHandle3D :: Ord SpatialHandle3D

instance showSpatialHandle3D :: Show SpatialHandle3D where
  show (SpatialHandle3D h) = 
    "Spatial3D(" <> show h.dx <> ", " <> show h.dy <> ", " <> show h.dz <> ")"

-- | Create a 3D spatial handle.
spatialHandle3D :: Number -> Number -> Number -> SpatialHandle3D
spatialHandle3D dx dy dz = SpatialHandle3D { dx, dy, dz }

-- | Zero-length handle (linear interpolation).
spatialHandle3DZero :: SpatialHandle3D
spatialHandle3DZero = SpatialHandle3D { dx: 0.0, dy: 0.0, dz: 0.0 }

-- | Extract handle values.
unwrapSpatialHandle3D :: SpatialHandle3D -> { dx :: Number, dy :: Number, dz :: Number }
unwrapSpatialHandle3D (SpatialHandle3D h) = h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // temporal // handle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal bezier handle for speed/easing control.
-- |
-- | Defines the easing curve in the graph editor.
-- | - `influence`: How far the handle extends (0-100%)
-- | - `speed`: Velocity at the keyframe (units/frame)
-- |
-- | In normalized form (for cubic bezier):
-- | - x: time influence (0.0 to 1.0)
-- | - y: value influence (can exceed 0-1 for overshoot)
newtype TemporalHandle = TemporalHandle
  { influence :: Number  -- ^ Influence percentage (0-100)
  , speed :: Number      -- ^ Speed at keyframe (units/frame)
  }

derive instance eqTemporalHandle :: Eq TemporalHandle
derive instance ordTemporalHandle :: Ord TemporalHandle

instance showTemporalHandle :: Show TemporalHandle where
  show (TemporalHandle h) = 
    "Temporal(inf:" <> show h.influence <> "%, spd:" <> show h.speed <> ")"

-- | Create a temporal handle.
temporalHandle :: Number -> Number -> TemporalHandle
temporalHandle inf spd = TemporalHandle 
  { influence: clampNumber 0.0 100.0 inf
  , speed: spd
  }

-- | Linear temporal handle (constant speed).
temporalHandleLinear :: TemporalHandle
temporalHandleLinear = TemporalHandle { influence: 0.0, speed: 0.0 }

-- | Ease-in preset (slow start).
temporalHandleEaseIn :: TemporalHandle
temporalHandleEaseIn = TemporalHandle { influence: 33.0, speed: 0.0 }

-- | Ease-out preset (slow end).
temporalHandleEaseOut :: TemporalHandle
temporalHandleEaseOut = TemporalHandle { influence: 33.0, speed: 0.0 }

-- | Ease-in-out preset (slow start and end).
temporalHandleEaseInOut :: TemporalHandle
temporalHandleEaseInOut = TemporalHandle { influence: 50.0, speed: 0.0 }

-- | Hold (instant change, no interpolation).
temporalHandleHold :: TemporalHandle
temporalHandleHold = TemporalHandle { influence: 0.0, speed: 0.0 }

-- | Extract handle values.
unwrapTemporalHandle :: TemporalHandle -> { influence :: Number, speed :: Number }
unwrapTemporalHandle (TemporalHandle h) = h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // keyframe // flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyframe behavior flags.
-- |
-- | - roving: Auto-adjust time for uniform speed
-- | - lockToTime: Prevent temporal adjustment
-- | - continuousBezier: Tangents are continuous (smooth)
-- | - autoBezier: System calculates tangents automatically
type KeyframeFlags =
  { roving :: Boolean            -- ^ Roving keyframe (auto-time adjustment)
  , lockToTime :: Boolean        -- ^ Locked to specific time
  , continuousBezier :: Boolean  -- ^ Continuous bezier tangents
  , autoBezier :: Boolean        -- ^ Auto-calculated tangents
  }

-- | Default keyframe flags.
defaultKeyframeFlags :: KeyframeFlags
defaultKeyframeFlags =
  { roving: not true
  , lockToTime: not true
  , continuousBezier: not true
  , autoBezier: not true
  }

-- | Set roving flag.
setRoving :: Boolean -> KeyframeFlags -> KeyframeFlags
setRoving r flags = flags { roving = r }

-- | Set lock to time flag.
setLockToTime :: Boolean -> KeyframeFlags -> KeyframeFlags
setLockToTime l flags = flags { lockToTime = l }

-- | Set continuous bezier flag.
setContinuousBezier :: Boolean -> KeyframeFlags -> KeyframeFlags
setContinuousBezier c flags = flags { continuousBezier = c }

-- | Set auto bezier flag.
setAutoBezier :: Boolean -> KeyframeFlags -> KeyframeFlags
setAutoBezier a flags = flags { autoBezier = a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // spatial // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spatial interpolation type (motion path shape).
data SpatialInterpolation
  = SILinear      -- ^ Straight line between keyframes
  | SIBezier      -- ^ Curved path with spatial handles
  | SIAuto        -- ^ Auto-calculated smooth path

derive instance eqSpatialInterpolation :: Eq SpatialInterpolation
derive instance ordSpatialInterpolation :: Ord SpatialInterpolation

instance showSpatialInterpolation :: Show SpatialInterpolation where
  show SILinear = "linear"
  show SIBezier = "bezier"
  show SIAuto = "auto"

spatialInterpolationToString :: SpatialInterpolation -> String
spatialInterpolationToString = show

spatialInterpolationFromString :: String -> Maybe SpatialInterpolation
spatialInterpolationFromString "linear" = Just SILinear
spatialInterpolationFromString "bezier" = Just SIBezier
spatialInterpolationFromString "auto" = Just SIAuto
spatialInterpolationFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // temporal // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Temporal interpolation type (speed curve shape).
data TemporalInterpolation
  = TILinear      -- ^ Constant speed
  | TIBezier      -- ^ Curved speed with temporal handles
  | TIHold        -- ^ No interpolation (instant jump)
  | TIAuto        -- ^ Auto-calculated smooth easing

derive instance eqTemporalInterpolation :: Eq TemporalInterpolation
derive instance ordTemporalInterpolation :: Ord TemporalInterpolation

instance showTemporalInterpolation :: Show TemporalInterpolation where
  show TILinear = "linear"
  show TIBezier = "bezier"
  show TIHold = "hold"
  show TIAuto = "auto"

temporalInterpolationToString :: TemporalInterpolation -> String
temporalInterpolationToString = show

temporalInterpolationFromString :: String -> Maybe TemporalInterpolation
temporalInterpolationFromString "linear" = Just TILinear
temporalInterpolationFromString "bezier" = Just TIBezier
temporalInterpolationFromString "hold" = Just TIHold
temporalInterpolationFromString "auto" = Just TIAuto
temporalInterpolationFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // dimension // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How position dimensions are animated.
data DimensionMode
  = DMUnified      -- ^ Single property with spatial handles
  | DMSeparated    -- ^ X, Y, Z as separate properties

derive instance eqDimensionMode :: Eq DimensionMode
derive instance ordDimensionMode :: Ord DimensionMode

instance showDimensionMode :: Show DimensionMode where
  show DMUnified = "unified"
  show DMSeparated = "separated"

dimensionModeToString :: DimensionMode -> String
dimensionModeToString = show

dimensionModeFromString :: String -> Maybe DimensionMode
dimensionModeFromString "unified" = Just DMUnified
dimensionModeFromString "separated" = Just DMSeparated
dimensionModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // spatial // keyframe 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 2D spatial keyframe with all handles.
type SpatialKeyframe2D =
  { frame :: Frames                         -- ^ Time position
  , position :: { x :: Number, y :: Number } -- ^ Spatial position
  , spatialIn :: SpatialHandle2D            -- ^ Incoming spatial tangent
  , spatialOut :: SpatialHandle2D           -- ^ Outgoing spatial tangent
  , temporalIn :: TemporalHandle            -- ^ Incoming temporal tangent
  , temporalOut :: TemporalHandle           -- ^ Outgoing temporal tangent
  , spatialInterp :: SpatialInterpolation   -- ^ Spatial interpolation type
  , temporalInterp :: TemporalInterpolation -- ^ Temporal interpolation type
  , flags :: KeyframeFlags                  -- ^ Behavior flags
  }

-- | Create a basic 2D spatial keyframe.
spatialKeyframe2D :: Frames -> Number -> Number -> SpatialKeyframe2D
spatialKeyframe2D frameTime x y =
  { frame: frameTime
  , position: { x, y }
  , spatialIn: spatialHandle2DZero
  , spatialOut: spatialHandle2DZero
  , temporalIn: temporalHandleLinear
  , temporalOut: temporalHandleLinear
  , spatialInterp: SIAuto
  , temporalInterp: TIAuto
  , flags: defaultKeyframeFlags
  }

-- | Create a linear 2D keyframe (no curves).
spatialKeyframe2DLinear :: Frames -> Number -> Number -> SpatialKeyframe2D
spatialKeyframe2DLinear frameTime x y =
  { frame: frameTime
  , position: { x, y }
  , spatialIn: spatialHandle2DZero
  , spatialOut: spatialHandle2DZero
  , temporalIn: temporalHandleLinear
  , temporalOut: temporalHandleLinear
  , spatialInterp: SILinear
  , temporalInterp: TILinear
  , flags: defaultKeyframeFlags
  }

-- | Create a 2D keyframe with explicit handles.
spatialKeyframe2DWithHandles 
  :: Frames 
  -> Number -> Number 
  -> SpatialHandle2D -> SpatialHandle2D
  -> TemporalHandle -> TemporalHandle
  -> SpatialKeyframe2D
spatialKeyframe2DWithHandles frameTime x y spatialIn spatialOut temporalIn temporalOut =
  { frame: frameTime
  , position: { x, y }
  , spatialIn: spatialIn
  , spatialOut: spatialOut
  , temporalIn: temporalIn
  , temporalOut: temporalOut
  , spatialInterp: SIBezier
  , temporalInterp: TIBezier
  , flags: defaultKeyframeFlags
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // spatial // keyframe 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete 3D spatial keyframe with all handles.
type SpatialKeyframe3D =
  { frame :: Frames
  , position :: { x :: Number, y :: Number, z :: Number }
  , spatialIn :: SpatialHandle3D
  , spatialOut :: SpatialHandle3D
  , temporalIn :: TemporalHandle
  , temporalOut :: TemporalHandle
  , spatialInterp :: SpatialInterpolation
  , temporalInterp :: TemporalInterpolation
  , flags :: KeyframeFlags
  }

-- | Create a basic 3D spatial keyframe.
spatialKeyframe3D :: Frames -> Number -> Number -> Number -> SpatialKeyframe3D
spatialKeyframe3D frameTime x y z =
  { frame: frameTime
  , position: { x, y, z }
  , spatialIn: spatialHandle3DZero
  , spatialOut: spatialHandle3DZero
  , temporalIn: temporalHandleLinear
  , temporalOut: temporalHandleLinear
  , spatialInterp: SIAuto
  , temporalInterp: TIAuto
  , flags: defaultKeyframeFlags
  }

-- | Create a linear 3D keyframe (no curves).
spatialKeyframe3DLinear :: Frames -> Number -> Number -> Number -> SpatialKeyframe3D
spatialKeyframe3DLinear frameTime x y z =
  { frame: frameTime
  , position: { x, y, z }
  , spatialIn: spatialHandle3DZero
  , spatialOut: spatialHandle3DZero
  , temporalIn: temporalHandleLinear
  , temporalOut: temporalHandleLinear
  , spatialInterp: SILinear
  , temporalInterp: TILinear
  , flags: defaultKeyframeFlags
  }

-- | Create a 3D keyframe with explicit handles.
spatialKeyframe3DWithHandles 
  :: Frames 
  -> Number -> Number -> Number
  -> SpatialHandle3D -> SpatialHandle3D
  -> TemporalHandle -> TemporalHandle
  -> SpatialKeyframe3D
spatialKeyframe3DWithHandles frameTime x y z spatialIn spatialOut temporalIn temporalOut =
  { frame: frameTime
  , position: { x, y, z }
  , spatialIn: spatialIn
  , spatialOut: spatialOut
  , temporalIn: temporalIn
  , temporalOut: temporalOut
  , spatialInterp: SIBezier
  , temporalInterp: TIBezier
  , flags: defaultKeyframeFlags
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // motion // path 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D motion path — sequence of spatial keyframes defining a path through space.
type MotionPath2D =
  { keyframes :: Array SpatialKeyframe2D
  , closed :: Boolean           -- ^ Does path loop?
  , dimensionMode :: DimensionMode
  }

-- | Create an empty motion path.
motionPath2D :: MotionPath2D
motionPath2D =
  { keyframes: []
  , closed: false
  , dimensionMode: DMUnified
  }

-- | Create motion path from keyframes.
motionPath2DFromKeyframes :: Array SpatialKeyframe2D -> MotionPath2D
motionPath2DFromKeyframes kfs =
  { keyframes: kfs
  , closed: false
  , dimensionMode: DMUnified
  }

-- | Evaluate position on motion path at a given frame.
-- |
-- | Returns the interpolated position considering both spatial
-- | and temporal curves.
-- |
-- | ## Algorithm
-- |
-- | 1. Find the two keyframes surrounding the target frame
-- | 2. Calculate the normalized time t between them
-- | 3. Apply temporal easing to get the eased parameter u
-- | 4. Evaluate the cubic bezier curve at parameter u
evaluateMotionPath2D :: Frames -> MotionPath2D -> Maybe { x :: Number, y :: Number }
evaluateMotionPath2D targetFrame path =
  case Array.length path.keyframes of
    0 -> Nothing
    1 -> case Array.index path.keyframes 0 of
      Just kf -> Just kf.position
      Nothing -> Nothing
    _ -> findAndInterpolate2D targetFrame path.keyframes

-- | Calculate total arc length of motion path.
-- |
-- | Uses Gaussian quadrature to numerically integrate the arc length
-- | of each bezier segment, then sums them.
motionPathLength2D :: MotionPath2D -> Number
motionPathLength2D path =
  case Array.length path.keyframes of
    0 -> 0.0
    1 -> 0.0
    _ -> sumSegmentLengths2D path.keyframes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // motion // path 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D motion path — sequence of spatial keyframes in 3D space.
type MotionPath3D =
  { keyframes :: Array SpatialKeyframe3D
  , closed :: Boolean
  , dimensionMode :: DimensionMode
  }

-- | Create an empty 3D motion path.
motionPath3D :: MotionPath3D
motionPath3D =
  { keyframes: []
  , closed: false
  , dimensionMode: DMUnified
  }

-- | Create 3D motion path from keyframes.
motionPath3DFromKeyframes :: Array SpatialKeyframe3D -> MotionPath3D
motionPath3DFromKeyframes kfs =
  { keyframes: kfs
  , closed: false
  , dimensionMode: DMUnified
  }

-- | Evaluate position on 3D motion path at a given frame.
-- |
-- | Returns the interpolated position considering both spatial
-- | and temporal curves in 3D space.
evaluateMotionPath3D :: Frames -> MotionPath3D -> Maybe { x :: Number, y :: Number, z :: Number }
evaluateMotionPath3D targetFrame path =
  case Array.length path.keyframes of
    0 -> Nothing
    1 -> case Array.index path.keyframes 0 of
      Just kf -> Just kf.position
      Nothing -> Nothing
    _ -> findAndInterpolate3D targetFrame path.keyframes

-- | Calculate total arc length of 3D motion path.
-- |
-- | Uses Gaussian quadrature to numerically integrate the arc length
-- | of each bezier segment in 3D space.
motionPathLength3D :: MotionPath3D -> Number
motionPathLength3D path =
  case Array.length path.keyframes of
    0 -> 0.0
    1 -> 0.0
    _ -> sumSegmentLengths3D path.keyframes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // speed // graph
-- ═════════════════════════════════════════════════════════════════════════════

-- | Speed graph — represents velocity over time for a property.
-- |
-- | The speed graph shows how fast a property is changing at any point.
-- | For position, this is the actual velocity (distance/time).
type SpeedGraph =
  { samples :: Array { frame :: Number, speed :: Number }
  , minSpeed :: Number
  , maxSpeed :: Number
  , averageSpeed :: Number
  }

-- | Create a speed graph from sample points.
speedGraph :: Array { frame :: Number, speed :: Number } -> SpeedGraph
speedGraph samples =
  let speeds = map (\s -> s.speed) samples
      minS = Array.foldl min 0.0 speeds
      maxS = Array.foldl max 0.0 speeds
      avgS = case Array.length speeds of
        0 -> 0.0
        n -> Array.foldl (+) 0.0 speeds / toNumber n
  in { samples, minSpeed: minS, maxSpeed: maxS, averageSpeed: avgS }

-- | Get speed at a specific frame.
-- |
-- | Finds the two samples surrounding the target frame and linearly
-- | interpolates between them to get the instantaneous speed.
speedAt :: Number -> SpeedGraph -> Number
speedAt fr graph = speedAtImpl fr graph.samples

-- | Get average speed.
averageSpeed :: SpeedGraph -> Number
averageSpeed graph = graph.averageSpeed

-- | Get maximum speed.
maxSpeed :: SpeedGraph -> Number
maxSpeed graph = graph.maxSpeed

-- | Get minimum speed.
minSpeed :: SpeedGraph -> Number
minSpeed graph = graph.minSpeed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get position from 2D keyframe.
keyframePosition2D :: SpatialKeyframe2D -> { x :: Number, y :: Number }
keyframePosition2D kf = kf.position

-- | Get position from 3D keyframe.
keyframePosition3D :: SpatialKeyframe3D -> { x :: Number, y :: Number, z :: Number }
keyframePosition3D kf = kf.position

-- | Get frame from 2D keyframe.
keyframeFrame :: forall r. { frame :: Frames | r } -> Frames
keyframeFrame kf = kf.frame

-- | Get incoming spatial handle from 2D keyframe.
keyframeSpatialIn2D :: SpatialKeyframe2D -> SpatialHandle2D
keyframeSpatialIn2D kf = kf.spatialIn

-- | Get outgoing spatial handle from 2D keyframe.
keyframeSpatialOut2D :: SpatialKeyframe2D -> SpatialHandle2D
keyframeSpatialOut2D kf = kf.spatialOut

-- | Get incoming spatial handle from 3D keyframe.
keyframeSpatialIn3D :: SpatialKeyframe3D -> SpatialHandle3D
keyframeSpatialIn3D kf = kf.spatialIn

-- | Get outgoing spatial handle from 3D keyframe.
keyframeSpatialOut3D :: SpatialKeyframe3D -> SpatialHandle3D
keyframeSpatialOut3D kf = kf.spatialOut

-- | Get incoming temporal handle.
keyframeTemporalIn :: forall r. { temporalIn :: TemporalHandle | r } -> TemporalHandle
keyframeTemporalIn kf = kf.temporalIn

-- | Get outgoing temporal handle.
keyframeTemporalOut :: forall r. { temporalOut :: TemporalHandle | r } -> TemporalHandle
keyframeTemporalOut kf = kf.temporalOut

-- | Get keyframe flags.
keyframeFlags :: forall r. { flags :: KeyframeFlags | r } -> KeyframeFlags
keyframeFlags kf = kf.flags

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set position on 2D keyframe.
setPosition2D :: Number -> Number -> SpatialKeyframe2D -> SpatialKeyframe2D
setPosition2D x y kf = kf { position = { x, y } }

-- | Set position on 3D keyframe.
setPosition3D :: Number -> Number -> Number -> SpatialKeyframe3D -> SpatialKeyframe3D
setPosition3D x y z kf = kf { position = { x, y, z } }

-- | Set spatial handles on 2D keyframe.
setSpatialHandles2D :: SpatialHandle2D -> SpatialHandle2D -> SpatialKeyframe2D -> SpatialKeyframe2D
setSpatialHandles2D spIn spOut kf = kf { spatialIn = spIn, spatialOut = spOut }

-- | Set spatial handles on 3D keyframe.
setSpatialHandles3D :: SpatialHandle3D -> SpatialHandle3D -> SpatialKeyframe3D -> SpatialKeyframe3D
setSpatialHandles3D spIn spOut kf = kf { spatialIn = spIn, spatialOut = spOut }

-- | Set temporal handles.
setTemporalHandles :: forall r. TemporalHandle -> TemporalHandle -> { temporalIn :: TemporalHandle, temporalOut :: TemporalHandle | r } -> { temporalIn :: TemporalHandle, temporalOut :: TemporalHandle | r }
setTemporalHandles tmpIn tmpOut kf = kf { temporalIn = tmpIn, temporalOut = tmpOut }

-- | Convert keyframe to roving (auto-time adjustment).
convertToRoving :: SpatialKeyframe2D -> SpatialKeyframe2D
convertToRoving kf = kf { flags = kf.flags { roving = true } }

-- | Convert keyframe to linear interpolation.
convertToLinear :: SpatialKeyframe2D -> SpatialKeyframe2D
convertToLinear kf = kf 
  { spatialInterp = SILinear
  , temporalInterp = TILinear
  , spatialIn = spatialHandle2DZero
  , spatialOut = spatialHandle2DZero
  }

-- | Convert keyframe to bezier interpolation.
convertToBezier :: SpatialKeyframe2D -> SpatialKeyframe2D
convertToBezier kf = kf 
  { spatialInterp = SIBezier
  , temporalInterp = TIBezier
  }

-- | Convert keyframe to hold (no interpolation).
convertToHold :: SpatialKeyframe2D -> SpatialKeyframe2D
convertToHold kf = kf { temporalInterp = TIHold }

-- | Convert keyframe to auto (system-calculated tangents).
convertToAuto :: SpatialKeyframe2D -> SpatialKeyframe2D
convertToAuto kf = kf 
  { spatialInterp = SIAuto
  , temporalInterp = TIAuto
  , flags = kf.flags { autoBezier = true }
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to Number.
toNumber :: Int -> Number
toNumber = Int.toNumber

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // cubic // bezier // math
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cubic bezier evaluation for a single component.
-- |
-- | B(t) = (1-t)³P₀ + 3(1-t)²tP₁ + 3(1-t)t²P₂ + t³P₃
-- |
-- | Where:
-- | - P₀ = start point
-- | - P₁ = start point + outgoing tangent
-- | - P₂ = end point + incoming tangent  
-- | - P₃ = end point
cubicBezier :: Number -> Number -> Number -> Number -> Number -> Number
cubicBezier p0 p1 p2 p3 t =
  let t2 = t * t
      t3 = t2 * t
      mt = 1.0 - t
      mt2 = mt * mt
      mt3 = mt2 * mt
  in mt3 * p0 + 3.0 * mt2 * t * p1 + 3.0 * mt * t2 * p2 + t3 * p3

-- | Derivative of cubic bezier (velocity).
-- |
-- | B'(t) = 3(1-t)²(P₁-P₀) + 6(1-t)t(P₂-P₁) + 3t²(P₃-P₂)
cubicBezierDerivative :: Number -> Number -> Number -> Number -> Number -> Number
cubicBezierDerivative p0 p1 p2 p3 t =
  let mt = 1.0 - t
      mt2 = mt * mt
      t2 = t * t
  in 3.0 * mt2 * (p1 - p0) + 6.0 * mt * t * (p2 - p1) + 3.0 * t2 * (p3 - p2)

-- | Evaluate 2D cubic bezier at parameter t.
-- |
-- | Given two keyframes KF1 and KF2, construct the bezier:
-- | - P₀ = KF1.position
-- | - P₁ = KF1.position + KF1.spatialOut
-- | - P₂ = KF2.position + KF2.spatialIn
-- | - P₃ = KF2.position
evalBezier2D 
  :: SpatialKeyframe2D 
  -> SpatialKeyframe2D 
  -> Number 
  -> { x :: Number, y :: Number }
evalBezier2D kf1 kf2 t =
  let -- Extract positions
      p0x = kf1.position.x
      p0y = kf1.position.y
      p3x = kf2.position.x
      p3y = kf2.position.y
      -- Extract tangent handles (relative to their keyframes)
      out1 = unwrapSpatialHandle2D kf1.spatialOut
      in2 = unwrapSpatialHandle2D kf2.spatialIn
      -- Control points (absolute positions)
      p1x = p0x + out1.dx
      p1y = p0y + out1.dy
      p2x = p3x + in2.dx
      p2y = p3y + in2.dy
  in { x: cubicBezier p0x p1x p2x p3x t
     , y: cubicBezier p0y p1y p2y p3y t
     }

-- | Evaluate 3D cubic bezier at parameter t.
evalBezier3D 
  :: SpatialKeyframe3D 
  -> SpatialKeyframe3D 
  -> Number 
  -> { x :: Number, y :: Number, z :: Number }
evalBezier3D kf1 kf2 t =
  let p0x = kf1.position.x
      p0y = kf1.position.y
      p0z = kf1.position.z
      p3x = kf2.position.x
      p3y = kf2.position.y
      p3z = kf2.position.z
      out1 = unwrapSpatialHandle3D kf1.spatialOut
      in2 = unwrapSpatialHandle3D kf2.spatialIn
      p1x = p0x + out1.dx
      p1y = p0y + out1.dy
      p1z = p0z + out1.dz
      p2x = p3x + in2.dx
      p2y = p3y + in2.dy
      p2z = p3z + in2.dz
  in { x: cubicBezier p0x p1x p2x p3x t
     , y: cubicBezier p0y p1y p2y p3y t
     , z: cubicBezier p0z p1z p2z p3z t
     }

-- | Apply temporal easing to convert normalized time to bezier parameter.
-- |
-- | Temporal handles define a 1D bezier curve that maps linear time to
-- | eased time. This creates ease-in, ease-out effects.
-- |
-- | The temporal bezier goes from (0,0) to (1,1) with control points
-- | derived from the influence values.
applyTemporalEasing :: TemporalHandle -> TemporalHandle -> Number -> Number
applyTemporalEasing outHandle inHandle t =
  let out = unwrapTemporalHandle outHandle
      inp = unwrapTemporalHandle inHandle
      -- Convert influence (0-100%) to bezier control points
      -- For ease-out: control point moves right (x increases)
      -- For ease-in: control point moves left from end (x decreases from 1)
      p1x = out.influence / 100.0
      p1y = 0.0  -- Start at 0 value
      p2x = 1.0 - (inp.influence / 100.0)
      p2y = 1.0  -- End at 1 value
  in cubicBezier 0.0 p1y p2y 1.0 (solveForT p1x p2x t)

-- | Newton-Raphson solver to find t for a given x on the temporal bezier.
-- |
-- | Given x, find t such that cubicBezier(0, p1x, p2x, 1, t) = x
solveForT :: Number -> Number -> Number -> Number
solveForT p1x p2x targetX = newtonSolve p1x p2x targetX targetX 0

newtonSolve :: Number -> Number -> Number -> Number -> Int -> Number
newtonSolve p1x p2x targetX guess iter
  | iter >= 10 = guess  -- Max iterations
  | otherwise =
      let currentX = cubicBezier 0.0 p1x p2x 1.0 guess
          deriv = cubicBezierDerivative 0.0 p1x p2x 1.0 guess
          error = currentX - targetX
      in if Math.abs error < 1.0e-10
           then guess
           else if Math.abs deriv < 1.0e-10
             then guess  -- Avoid division by near-zero
             else newtonSolve p1x p2x targetX (guess - error / deriv) (iter + 1)

-- | Find the two keyframes surrounding a target frame and interpolate.
findAndInterpolate2D 
  :: Frames 
  -> Array SpatialKeyframe2D 
  -> Maybe { x :: Number, y :: Number }
findAndInterpolate2D targetFrame keyframes =
  findSurroundingPair2D targetFrame keyframes 0

-- | Search through keyframes to find the surrounding pair.
findSurroundingPair2D 
  :: Frames 
  -> Array SpatialKeyframe2D 
  -> Int 
  -> Maybe { x :: Number, y :: Number }
findSurroundingPair2D targetFrame keyframes idx =
  let targetFrameNum = unwrapFrames targetFrame
      len = Array.length keyframes
  in if idx >= len - 1
       then 
         -- Past the last keyframe, return last position
         case Array.index keyframes (len - 1) of
           Just lastKeyframe -> Just lastKeyframe.position
           Nothing -> Nothing
       else
         case Tuple (Array.index keyframes idx) (Array.index keyframes (idx + 1)) of
           Tuple (Just keyframe1) (Just keyframe2) ->
             let frameTime1 = unwrapFrames keyframe1.frame
                 frameTime2 = unwrapFrames keyframe2.frame
             in if targetFrameNum < frameTime1
                  then Just keyframe1.position  -- Before first keyframe
                  else if targetFrameNum >= frameTime1 && targetFrameNum <= frameTime2
                    then interpolateBetween2D keyframe1 keyframe2 targetFrameNum
                    else findSurroundingPair2D targetFrame keyframes (idx + 1)
           _ -> Nothing

-- | Interpolate between two 2D keyframes at a specific frame.
interpolateBetween2D 
  :: SpatialKeyframe2D 
  -> SpatialKeyframe2D 
  -> Number 
  -> Maybe { x :: Number, y :: Number }
interpolateBetween2D keyframe1 keyframe2 targetFrameNum =
  let frameTime1 = unwrapFrames keyframe1.frame
      frameTime2 = unwrapFrames keyframe2.frame
      duration = frameTime2 - frameTime1
  in if duration <= 0.0
       then Just keyframe1.position
       else
         let -- Normalized linear time (0 to 1)
             linearT = (targetFrameNum - frameTime1) / duration
             -- Apply temporal easing based on interpolation type
             easedT = case keyframe1.temporalInterp of
               TILinear -> linearT
               TIHold -> 0.0  -- Hold stays at start value
               TIBezier -> applyTemporalEasing keyframe1.temporalOut keyframe2.temporalIn linearT
               TIAuto -> applyTemporalEasing keyframe1.temporalOut keyframe2.temporalIn linearT
             -- Evaluate spatial bezier based on interpolation type
             position = case keyframe1.spatialInterp of
               SILinear -> 
                 { x: Math.lerp keyframe1.position.x keyframe2.position.x easedT
                 , y: Math.lerp keyframe1.position.y keyframe2.position.y easedT
                 }
               SIBezier -> evalBezier2D keyframe1 keyframe2 easedT
               SIAuto -> evalBezier2D keyframe1 keyframe2 easedT
         in Just position

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // arc // length // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sum arc lengths of all bezier segments in a 2D path.
sumSegmentLengths2D :: Array SpatialKeyframe2D -> Number
sumSegmentLengths2D keyframes =
  sumPairs2D keyframes 0 0.0

sumPairs2D :: Array SpatialKeyframe2D -> Int -> Number -> Number
sumPairs2D keyframes idx acc =
  let len = Array.length keyframes
  in if idx >= len - 1
       then acc
       else
         case Tuple (Array.index keyframes idx) (Array.index keyframes (idx + 1)) of
           Tuple (Just kf1) (Just kf2) ->
             let segmentLen = bezierArcLength2D kf1 kf2
             in sumPairs2D keyframes (idx + 1) (acc + segmentLen)
           _ -> acc

-- | Calculate arc length of a single 2D bezier segment using Gaussian quadrature.
-- |
-- | Arc length = ∫₀¹ |B'(t)| dt
-- |
-- | Using 5-point Gaussian quadrature for good accuracy.
bezierArcLength2D :: SpatialKeyframe2D -> SpatialKeyframe2D -> Number
bezierArcLength2D kf1 kf2 =
  let -- Gaussian quadrature nodes and weights for [-1, 1] interval
      -- 5-point Legendre-Gauss
      nodes = [ -0.9061798459386640, -0.5384693101056831, 0.0, 0.5384693101056831, 0.9061798459386640 ]
      weights = [ 0.2369268850561891, 0.4786286704993665, 0.5688888888888889, 0.4786286704993665, 0.2369268850561891 ]
      -- Transform from [-1,1] to [0,1]: t = (x + 1) / 2, dt = dx / 2
      -- So integral becomes (1/2) * sum(w_i * f((x_i + 1)/2))
  in 0.5 * gaussSum2D kf1 kf2 nodes weights 0.0

gaussSum2D :: SpatialKeyframe2D -> SpatialKeyframe2D -> Array Number -> Array Number -> Number -> Number
gaussSum2D kf1 kf2 nodes weights acc =
  case Tuple (Array.index nodes 0) (Array.index weights 0) of
    Tuple (Just node) (Just weight) ->
      let t = (node + 1.0) / 2.0  -- Transform to [0,1]
          speed = bezierSpeed2D kf1 kf2 t
          newAcc = acc + weight * speed
          remainingNodes = Array.drop 1 nodes
          remainingWeights = Array.drop 1 weights
      in if Array.length remainingNodes == 0
           then newAcc
           else gaussSum2D kf1 kf2 remainingNodes remainingWeights newAcc
    _ -> acc

-- | Calculate instantaneous speed (magnitude of velocity) on a 2D bezier.
bezierSpeed2D :: SpatialKeyframe2D -> SpatialKeyframe2D -> Number -> Number
bezierSpeed2D kf1 kf2 t =
  let p0x = kf1.position.x
      p0y = kf1.position.y
      p3x = kf2.position.x
      p3y = kf2.position.y
      out1 = unwrapSpatialHandle2D kf1.spatialOut
      in2 = unwrapSpatialHandle2D kf2.spatialIn
      p1x = p0x + out1.dx
      p1y = p0y + out1.dy
      p2x = p3x + in2.dx
      p2y = p3y + in2.dy
      -- Velocity components
      vx = cubicBezierDerivative p0x p1x p2x p3x t
      vy = cubicBezierDerivative p0y p1y p2y p3y t
  in Math.hypot vx vy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 3d // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find surrounding keyframes and interpolate for 3D path.
findAndInterpolate3D 
  :: Frames 
  -> Array SpatialKeyframe3D 
  -> Maybe { x :: Number, y :: Number, z :: Number }
findAndInterpolate3D targetFrame keyframes =
  findSurroundingPair3D targetFrame keyframes 0

findSurroundingPair3D 
  :: Frames 
  -> Array SpatialKeyframe3D 
  -> Int 
  -> Maybe { x :: Number, y :: Number, z :: Number }
findSurroundingPair3D targetFrame keyframes idx =
  let targetFrameNum = unwrapFrames targetFrame
      len = Array.length keyframes
  in if idx >= len - 1
       then 
         case Array.index keyframes (len - 1) of
           Just lastKeyframe -> Just lastKeyframe.position
           Nothing -> Nothing
       else
         case Tuple (Array.index keyframes idx) (Array.index keyframes (idx + 1)) of
           Tuple (Just keyframe1) (Just keyframe2) ->
             let frameTime1 = unwrapFrames keyframe1.frame
                 frameTime2 = unwrapFrames keyframe2.frame
             in if targetFrameNum < frameTime1
                  then Just keyframe1.position
                  else if targetFrameNum >= frameTime1 && targetFrameNum <= frameTime2
                    then interpolateBetween3D keyframe1 keyframe2 targetFrameNum
                    else findSurroundingPair3D targetFrame keyframes (idx + 1)
           _ -> Nothing

interpolateBetween3D 
  :: SpatialKeyframe3D 
  -> SpatialKeyframe3D 
  -> Number 
  -> Maybe { x :: Number, y :: Number, z :: Number }
interpolateBetween3D keyframe1 keyframe2 targetFrameNum =
  let frameTime1 = unwrapFrames keyframe1.frame
      frameTime2 = unwrapFrames keyframe2.frame
      duration = frameTime2 - frameTime1
  in if duration <= 0.0
       then Just keyframe1.position
       else
         let linearT = (targetFrameNum - frameTime1) / duration
             easedT = case keyframe1.temporalInterp of
               TILinear -> linearT
               TIHold -> 0.0
               TIBezier -> applyTemporalEasing keyframe1.temporalOut keyframe2.temporalIn linearT
               TIAuto -> applyTemporalEasing keyframe1.temporalOut keyframe2.temporalIn linearT
             position = case keyframe1.spatialInterp of
               SILinear -> 
                 { x: Math.lerp keyframe1.position.x keyframe2.position.x easedT
                 , y: Math.lerp keyframe1.position.y keyframe2.position.y easedT
                 , z: Math.lerp keyframe1.position.z keyframe2.position.z easedT
                 }
               SIBezier -> evalBezier3D keyframe1 keyframe2 easedT
               SIAuto -> evalBezier3D keyframe1 keyframe2 easedT
         in Just position

-- | Sum arc lengths of all bezier segments in a 3D path.
sumSegmentLengths3D :: Array SpatialKeyframe3D -> Number
sumSegmentLengths3D keyframes =
  sumPairs3D keyframes 0 0.0

sumPairs3D :: Array SpatialKeyframe3D -> Int -> Number -> Number
sumPairs3D keyframes idx acc =
  let len = Array.length keyframes
  in if idx >= len - 1
       then acc
       else
         case Tuple (Array.index keyframes idx) (Array.index keyframes (idx + 1)) of
           Tuple (Just kf1) (Just kf2) ->
             let segmentLen = bezierArcLength3D kf1 kf2
             in sumPairs3D keyframes (idx + 1) (acc + segmentLen)
           _ -> acc

bezierArcLength3D :: SpatialKeyframe3D -> SpatialKeyframe3D -> Number
bezierArcLength3D kf1 kf2 =
  let nodes = [ -0.9061798459386640, -0.5384693101056831, 0.0, 0.5384693101056831, 0.9061798459386640 ]
      weights = [ 0.2369268850561891, 0.4786286704993665, 0.5688888888888889, 0.4786286704993665, 0.2369268850561891 ]
  in 0.5 * gaussSum3D kf1 kf2 nodes weights 0.0

gaussSum3D :: SpatialKeyframe3D -> SpatialKeyframe3D -> Array Number -> Array Number -> Number -> Number
gaussSum3D kf1 kf2 nodes weights acc =
  case Tuple (Array.index nodes 0) (Array.index weights 0) of
    Tuple (Just node) (Just weight) ->
      let t = (node + 1.0) / 2.0
          speed = bezierSpeed3D kf1 kf2 t
          newAcc = acc + weight * speed
          remainingNodes = Array.drop 1 nodes
          remainingWeights = Array.drop 1 weights
      in if Array.length remainingNodes == 0
           then newAcc
           else gaussSum3D kf1 kf2 remainingNodes remainingWeights newAcc
    _ -> acc

bezierSpeed3D :: SpatialKeyframe3D -> SpatialKeyframe3D -> Number -> Number
bezierSpeed3D kf1 kf2 t =
  let p0x = kf1.position.x
      p0y = kf1.position.y
      p0z = kf1.position.z
      p3x = kf2.position.x
      p3y = kf2.position.y
      p3z = kf2.position.z
      out1 = unwrapSpatialHandle3D kf1.spatialOut
      in2 = unwrapSpatialHandle3D kf2.spatialIn
      p1x = p0x + out1.dx
      p1y = p0y + out1.dy
      p1z = p0z + out1.dz
      p2x = p3x + in2.dx
      p2y = p3y + in2.dy
      p2z = p3z + in2.dz
      vx = cubicBezierDerivative p0x p1x p2x p3x t
      vy = cubicBezierDerivative p0y p1y p2y p3y t
      vz = cubicBezierDerivative p0z p1z p2z p3z t
  in Math.hypot3 vx vy vz

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // speed // graph // impl
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find speed at a specific frame by interpolating between samples.
speedAtImpl :: Number -> Array { frame :: Number, speed :: Number } -> Number
speedAtImpl targetFr samples =
  findSpeedSample targetFr samples 0

findSpeedSample :: Number -> Array { frame :: Number, speed :: Number } -> Int -> Number
findSpeedSample targetFr samples idx =
  let len = Array.length samples
  in if len == 0
       then 0.0
       else if idx >= len - 1
         then 
           case Array.index samples (len - 1) of
             Just s -> s.speed
             Nothing -> 0.0
         else
           case Tuple (Array.index samples idx) (Array.index samples (idx + 1)) of
             Tuple (Just s1) (Just s2) ->
               if targetFr < s1.frame
                 then s1.speed
                 else if targetFr >= s1.frame && targetFr <= s2.frame
                   then 
                     let t = if s2.frame == s1.frame 
                               then 0.0 
                               else (targetFr - s1.frame) / (s2.frame - s1.frame)
                     in Math.lerp s1.speed s2.speed t
                   else findSpeedSample targetFr samples (idx + 1)
             _ -> 0.0
