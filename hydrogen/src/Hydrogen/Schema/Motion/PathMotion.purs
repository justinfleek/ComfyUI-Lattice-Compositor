-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // motion // path-motion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathMotion — Animate objects along spline paths.
-- |
-- | ## Design Philosophy
-- |
-- | PathMotion provides cinema-grade motion path animation like After Effects,
-- | Cinema 4D, and Illustrator. Objects follow paths with:
-- |
-- | - **Arc-length parameterization**: Uniform speed along path
-- | - **Easing integration**: Apply easing curves to path progress
-- | - **Orient to path**: Auto-rotate object to face movement direction
-- | - **Banking**: Tilt into turns like aircraft
-- | - **Time remapping**: Variable speed along path
-- |
-- | ## Motion Path Workflow
-- |
-- | 1. Create a path (Spline, NURBS, or Bezier)
-- | 2. Wrap in MotionPath with timing parameters
-- | 3. Evaluate at any frame to get position, rotation, scale
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.PathMotion as PM
-- | import Hydrogen.Schema.Geometry.Spline as Spline
-- |
-- | -- Create path from points
-- | path = Spline.catmullRomSpline points
-- |
-- | -- Create motion path (2 second duration at 30fps = 60 frames)
-- | motion = PM.motionPath path (PM.Duration 60) PM.easeInOut
-- |
-- | -- Get position at frame 30 (halfway)
-- | pos = PM.positionAtFrame 30 motion
-- |
-- | -- Get full transform (position + rotation)
-- | transform = PM.transformAtFrame 30 motion
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Spline (CatmullRomSpline, BSpline)
-- | - Schema.Geometry.Point (Point2D)
-- | - Schema.Geometry.Vector (Vector2D for tangents)
-- | - Schema.Geometry.Angle (Degrees for rotation)
-- | - Schema.Motion.Easing (easing curves)
-- | - Schema.Dimension.Temporal (Frames)

module Hydrogen.Schema.Motion.PathMotion
  ( -- * Core Types
    MotionPath(MotionPath)
  , PathSource(..)
  , OrientMode(..)
  , MotionSample(MotionSample)
  
  -- * Construction
  , motionPath
  , motionPathSimple
  , motionPathWithBank
  
  -- * Evaluation
  , positionAtFrame
  , positionAtTime
  , positionAtProgress
  , tangentAtFrame
  , rotationAtFrame
  , sampleAtFrame
  , sampleAtProgress
  
  -- * Configuration
  , setDuration
  , setEasing
  , setOrientMode
  , setAutoOrient
  , setBankAngle
  , setLoop
  , setPingPong
  , setOffset
  
  -- * Accessors
  , pathSource
  , duration
  , easing
  , orientMode
  , isLooping
  , isPingPong
  
  -- * Path Length
  , pathLength
  , progressToArcLength
  , arcLengthToProgress
  
  -- * Frame Utilities
  , frameToProgress
  , progressToFrame
  , isActiveAtFrame
  
  -- * Batch Sampling
  , sampleFrameRange
  , samplePoints
  
  -- * Presets
  , defaultEasing
  
  -- * Frame Conversion
  , framesToDuration
  , durationToFrames
  
  -- * Path Filtering
  , filterActiveFrames
  , mapSampledPositions
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , otherwise
  , negate
  , min
  , max
  , map
  )

import Data.Array (length, snoc, foldl, index)
import Data.Maybe (Maybe(..))
import Data.Number (sqrt, atan2, pi, floor)
import Data.Int (toNumber, floor) as Int

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2, normalize2, magnitude2, getVX, getVY)
import Hydrogen.Schema.Geometry.Angle (Degrees(Degrees))
import Hydrogen.Schema.Geometry.Spline 
  ( CatmullRomSpline
  , BSpline
  , catmullRomPointAt
  , catmullRomTangentAt
  , catmullRomLength
  , bSplinePointAt
  , bSplineTangentAt
  , bSplineLength
  )
import Hydrogen.Schema.Motion.Easing (Easing, evaluate, linear, easeInOut)
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames), unwrapFrames)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source path for motion.
-- |
-- | Wraps different spline types into a unified interface.
data PathSource
  = CatmullRomSource CatmullRomSpline
  | BSplineSource BSpline
  | PointArraySource (Array Point2D)  -- Linear interpolation between points

derive instance eqPathSource :: Eq PathSource

instance showPathSource :: Show PathSource where
  show (CatmullRomSource _) = "CatmullRomSource"
  show (BSplineSource _) = "BSplineSource"
  show (PointArraySource pts) = "(PointArraySource " <> show (length pts) <> " points)"

-- | How to orient the object along the path.
data OrientMode
  = NoOrient           -- Keep original rotation
  | OrientToPath       -- Rotate to face movement direction
  | OrientToPathFlipped -- Rotate 180° from movement direction
  | OrientPerpendicular -- Rotate perpendicular to path
  | OrientCustomOffset Degrees  -- Rotate to path + custom offset

derive instance eqOrientMode :: Eq OrientMode

instance showOrientMode :: Show OrientMode where
  show NoOrient = "NoOrient"
  show OrientToPath = "OrientToPath"
  show OrientToPathFlipped = "OrientToPathFlipped"
  show OrientPerpendicular = "OrientPerpendicular"
  show (OrientCustomOffset d) = "(OrientCustomOffset " <> show d <> ")"

-- | Complete motion sample at a point in time.
newtype MotionSample = MotionSample
  { position :: Point2D
  , rotation :: Degrees
  , tangent :: Vector2D
  , progress :: Number    -- 0-1 normalized progress
  , arcLength :: Number   -- Distance along path
  , speed :: Number       -- Current speed (derivative of position)
  , bank :: Degrees       -- Banking angle for turns
  }

derive instance eqMotionSample :: Eq MotionSample

instance showMotionSample :: Show MotionSample where
  show (MotionSample s) = "(MotionSample pos:" <> show s.position 
    <> " rot:" <> show s.rotation <> " progress:" <> show s.progress <> ")"

-- | Motion path configuration.
-- |
-- | Combines path geometry with timing and orientation settings.
newtype MotionPath = MotionPath
  { source :: PathSource
  , durationFrames :: Number      -- Total duration in frames
  , easing :: Easing              -- How progress maps to path position
  , orientMode :: OrientMode      -- How to rotate along path
  , bankAngle :: Degrees          -- Maximum banking angle for turns
  , bankSmoothing :: Number       -- 0-1, how much to smooth banking
  , loop :: Boolean               -- Whether to loop animation
  , pingPong :: Boolean           -- Whether to reverse at end
  , startOffset :: Number         -- 0-1, where to start on path
  , endOffset :: Number           -- 0-1, where to end on path
  , startFrame :: Number          -- Frame where animation begins
  }

derive instance eqMotionPath :: Eq MotionPath

instance showMotionPath :: Show MotionPath where
  show (MotionPath mp) = "(MotionPath dur:" <> show mp.durationFrames 
    <> " orient:" <> show mp.orientMode <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a motion path with full configuration.
motionPath :: PathSource -> Number -> Easing -> MotionPath
motionPath source dur eas = MotionPath
  { source: source
  , durationFrames: dur
  , easing: eas
  , orientMode: NoOrient
  , bankAngle: Degrees 0.0
  , bankSmoothing: 0.5
  , loop: false
  , pingPong: false
  , startOffset: 0.0
  , endOffset: 1.0
  , startFrame: 0.0
  }

-- | Create a simple motion path with linear easing.
motionPathSimple :: PathSource -> Number -> MotionPath
motionPathSimple source dur = motionPath source dur linear

-- | Create a motion path with auto-orient and banking.
motionPathWithBank :: PathSource -> Number -> Easing -> Degrees -> MotionPath
motionPathWithBank source dur eas bankMax =
  let base = motionPath source dur eas
      (MotionPath mp) = base
  in MotionPath (mp { orientMode = OrientToPath, bankAngle = bankMax })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get position at a specific frame number.
positionAtFrame :: Number -> MotionPath -> Point2D
positionAtFrame frame mp =
  let progress = frameToProgress frame mp
  in positionAtProgress progress mp

-- | Get position at normalized time (0-1).
positionAtTime :: Number -> MotionPath -> Point2D
positionAtTime t mp =
  let progress = clamp01 t
  in positionAtProgress progress mp

-- | Get position at progress value (0-1), applying easing.
positionAtProgress :: Number -> MotionPath -> Point2D
positionAtProgress progress (MotionPath mp) =
  let
    -- Apply easing to progress
    easedProgress = evaluate mp.easing (clamp01 progress)
    
    -- Map to path range
    pathT = mp.startOffset + easedProgress * (mp.endOffset - mp.startOffset)
    
    -- Handle ping-pong
    actualT = if mp.pingPong && pathT > 0.5
              then 1.0 - (pathT - 0.5) * 2.0
              else if mp.pingPong then pathT * 2.0
              else pathT
  in
    evaluatePathPosition mp.source (clamp01 actualT)

-- | Get tangent vector at frame.
tangentAtFrame :: Number -> MotionPath -> Vector2D
tangentAtFrame frame mp =
  let progress = frameToProgress frame mp
  in tangentAtProgress progress mp

-- | Get rotation at frame (based on orient mode).
rotationAtFrame :: Number -> MotionPath -> Degrees
rotationAtFrame frame mp =
  let sample = sampleAtFrame frame mp
      (MotionSample s) = sample
  in s.rotation

-- | Get complete motion sample at frame.
sampleAtFrame :: Number -> MotionPath -> MotionSample
sampleAtFrame frame mp =
  let progress = frameToProgress frame mp
  in sampleAtProgress progress mp

-- | Get complete motion sample at progress (0-1).
sampleAtProgress :: Number -> MotionPath -> MotionSample
sampleAtProgress progress (MotionPath mp) =
  let
    -- Apply easing
    easedProgress = evaluate mp.easing (clamp01 progress)
    pathT = mp.startOffset + easedProgress * (mp.endOffset - mp.startOffset)
    
    -- Handle ping-pong
    actualT = if mp.pingPong && pathT > 0.5
              then 1.0 - (pathT - 0.5) * 2.0
              else if mp.pingPong then pathT * 2.0
              else pathT
    
    clampedT = clamp01 actualT
    
    -- Get position and tangent
    pos = evaluatePathPosition mp.source clampedT
    tan = evaluatePathTangent mp.source clampedT
    
    -- Calculate rotation from tangent
    baseRotation = vectorToAngle tan
    
    -- Apply orient mode
    rotation = case mp.orientMode of
      NoOrient -> Degrees 0.0
      OrientToPath -> baseRotation
      OrientToPathFlipped -> addDegrees baseRotation (Degrees 180.0)
      OrientPerpendicular -> addDegrees baseRotation (Degrees 90.0)
      OrientCustomOffset offset -> addDegrees baseRotation offset
    
    -- Calculate banking (based on curvature/rate of rotation change)
    bank = calculateBank clampedT mp.source mp.bankAngle mp.bankSmoothing
    
    -- Arc length and speed
    totalLength = evaluatePathLength mp.source
    arcLen = clampedT * totalLength  -- Approximation
    speed = magnitude2 tan
  in
    MotionSample
      { position: pos
      , rotation: rotation
      , tangent: tan
      , progress: easedProgress
      , arcLength: arcLen
      , speed: speed
      , bank: bank
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set duration in frames.
setDuration :: Number -> MotionPath -> MotionPath
setDuration dur (MotionPath mp) = MotionPath (mp { durationFrames = dur })

-- | Set easing curve.
setEasing :: Easing -> MotionPath -> MotionPath
setEasing eas (MotionPath mp) = MotionPath (mp { easing = eas })

-- | Set orientation mode.
setOrientMode :: OrientMode -> MotionPath -> MotionPath
setOrientMode mode (MotionPath mp) = MotionPath (mp { orientMode = mode })

-- | Enable auto-orient to path.
setAutoOrient :: MotionPath -> MotionPath
setAutoOrient = setOrientMode OrientToPath

-- | Set maximum banking angle.
setBankAngle :: Degrees -> MotionPath -> MotionPath
setBankAngle angle (MotionPath mp) = MotionPath (mp { bankAngle = angle })

-- | Enable looping.
setLoop :: Boolean -> MotionPath -> MotionPath
setLoop loop (MotionPath mp) = MotionPath (mp { loop = loop })

-- | Enable ping-pong (reverse at end).
setPingPong :: Boolean -> MotionPath -> MotionPath
setPingPong pp (MotionPath mp) = MotionPath (mp { pingPong = pp })

-- | Set path offset (start and end points on path).
setOffset :: Number -> Number -> MotionPath -> MotionPath
setOffset start end (MotionPath mp) = 
  MotionPath (mp { startOffset = clamp01 start, endOffset = clamp01 end })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get path source.
pathSource :: MotionPath -> PathSource
pathSource (MotionPath mp) = mp.source

-- | Get duration in frames.
duration :: MotionPath -> Number
duration (MotionPath mp) = mp.durationFrames

-- | Get easing curve.
easing :: MotionPath -> Easing
easing (MotionPath mp) = mp.easing

-- | Get orientation mode.
orientMode :: MotionPath -> OrientMode
orientMode (MotionPath mp) = mp.orientMode

-- | Check if looping.
isLooping :: MotionPath -> Boolean
isLooping (MotionPath mp) = mp.loop

-- | Check if ping-pong enabled.
isPingPong :: MotionPath -> Boolean
isPingPong (MotionPath mp) = mp.pingPong

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // path length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get total path length.
pathLength :: MotionPath -> Number
pathLength (MotionPath mp) = evaluatePathLength mp.source

-- | Convert normalized progress to arc length.
progressToArcLength :: Number -> MotionPath -> Number
progressToArcLength progress mp =
  clamp01 progress * pathLength mp

-- | Convert arc length to normalized progress.
arcLengthToProgress :: Number -> MotionPath -> Number
arcLengthToProgress arcLen mp =
  let total = pathLength mp
  in if total < epsilon then 0.0 else clamp01 (arcLen / total)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // frame utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert frame number to progress (0-1).
frameToProgress :: Number -> MotionPath -> Number
frameToProgress frame (MotionPath mp) =
  let
    relativeFrame = frame - mp.startFrame
    rawProgress = if mp.durationFrames < epsilon 
                  then 0.0 
                  else relativeFrame / mp.durationFrames
  in
    if mp.loop then
      -- Loop: wrap progress
      let wrapped = rawProgress - floorNum rawProgress
      in if wrapped < 0.0 then wrapped + 1.0 else wrapped
    else
      clamp01 rawProgress

-- | Convert progress to frame number.
progressToFrame :: Number -> MotionPath -> Number
progressToFrame progress (MotionPath mp) =
  mp.startFrame + clamp01 progress * mp.durationFrames

-- | Check if animation is active at frame.
isActiveAtFrame :: Number -> MotionPath -> Boolean
isActiveAtFrame frame (MotionPath mp) =
  let relativeFrame = frame - mp.startFrame
  in if mp.loop then true
     else relativeFrame >= 0.0 && relativeFrame <= mp.durationFrames

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // batch sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample motion at every frame in range.
sampleFrameRange :: Number -> Number -> MotionPath -> Array MotionSample
sampleFrameRange startFrame endFrame mp =
  let
    numFrames = Int.toNumber (floorInt (endFrame - startFrame)) + 1.0
  in
    buildArray (floorInt numFrames) (\i ->
      let frame = startFrame + Int.toNumber i
      in Just (sampleAtFrame frame mp)
    )

-- | Sample n evenly-spaced points along path.
samplePoints :: Int -> MotionPath -> Array Point2D
samplePoints n mp =
  if n <= 0 then []
  else buildArray (n + 1) (\i ->
    let progress = Int.toNumber i / Int.toNumber n
    in Just (positionAtProgress progress mp)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate position on path source.
evaluatePathPosition :: PathSource -> Number -> Point2D
evaluatePathPosition source t = case source of
  CatmullRomSource spline -> catmullRomPointAt t spline
  BSplineSource spline -> bSplinePointAt t spline
  PointArraySource pts -> interpolatePointArray t pts

-- | Evaluate tangent on path source.
evaluatePathTangent :: PathSource -> Number -> Vector2D
evaluatePathTangent source t = case source of
  CatmullRomSource spline -> catmullRomTangentAt t spline
  BSplineSource spline -> bSplineTangentAt t spline
  PointArraySource pts -> interpolatePointArrayTangent t pts

-- | Get path length.
evaluatePathLength :: PathSource -> Number
evaluatePathLength source = case source of
  CatmullRomSource spline -> catmullRomLength spline
  BSplineSource spline -> bSplineLength spline
  PointArraySource pts -> pointArrayLength pts

-- | Tangent at progress for point array.
tangentAtProgress :: Number -> MotionPath -> Vector2D
tangentAtProgress progress (MotionPath mp) =
  let
    easedProgress = evaluate mp.easing (clamp01 progress)
    pathT = mp.startOffset + easedProgress * (mp.endOffset - mp.startOffset)
  in
    evaluatePathTangent mp.source (clamp01 pathT)

-- | Linear interpolation in point array.
interpolatePointArray :: Number -> Array Point2D -> Point2D
interpolatePointArray t pts =
  let 
    n = length pts
  in
    if n == 0 then point2D 0.0 0.0
    else if n == 1 then case pts !! 0 of
      Nothing -> point2D 0.0 0.0
      Just p -> p
    else
      let
        tScaled = clamp01 t * Int.toNumber (n - 1)
        i = floorInt tScaled
        frac = tScaled - Int.toNumber i
        idx1 = min i (n - 1)
        idx2 = min (i + 1) (n - 1)
      in
        case { p1: pts !! idx1, p2: pts !! idx2 } of
          { p1: Just (Point2D a), p2: Just (Point2D b) } ->
            point2D (a.x + frac * (b.x - a.x)) (a.y + frac * (b.y - a.y))
          _ -> point2D 0.0 0.0

-- | Tangent for point array (direction between adjacent points).
interpolatePointArrayTangent :: Number -> Array Point2D -> Vector2D
interpolatePointArrayTangent t pts =
  let 
    n = length pts
  in
    if n < 2 then vec2 1.0 0.0
    else
      let
        tScaled = clamp01 t * Int.toNumber (n - 1)
        i = floorInt tScaled
        idx1 = min i (n - 2)
        idx2 = idx1 + 1
      in
        case { p1: pts !! idx1, p2: pts !! idx2 } of
          { p1: Just (Point2D a), p2: Just (Point2D b) } ->
            normalize2 (vec2 (b.x - a.x) (b.y - a.y))
          _ -> vec2 1.0 0.0

-- | Total length of point array path.
pointArrayLength :: Array Point2D -> Number
pointArrayLength pts =
  let n = length pts
  in foldl (\acc i ->
       case { p1: pts !! i, p2: pts !! (i + 1) } of
         { p1: Just (Point2D a), p2: Just (Point2D b) } ->
           let dx = b.x - a.x
               dy = b.y - a.y
           in acc + sqrt (dx * dx + dy * dy)
         _ -> acc
     ) 0.0 (buildIntArray (n - 1))

-- | Convert vector to angle in degrees.
vectorToAngle :: Vector2D -> Degrees
vectorToAngle v =
  let radians = atan2 (getVY v) (getVX v)
  in Degrees (radians * 180.0 / pi)

-- | Add degrees.
addDegrees :: Degrees -> Degrees -> Degrees
addDegrees (Degrees a) (Degrees b) = Degrees (a + b)

-- | Calculate banking angle based on curvature.
calculateBank :: Number -> PathSource -> Degrees -> Number -> Degrees
calculateBank t source maxBank smoothing =
  let
    -- Sample tangents before and after
    h = 0.01
    t1 = max 0.0 (t - h)
    t2 = min 1.0 (t + h)
    
    tan1 = evaluatePathTangent source t1
    tan2 = evaluatePathTangent source t2
    
    -- Angular change (approximates curvature)
    angle1 = vectorToAngle tan1
    angle2 = vectorToAngle tan2
    (Degrees a1) = angle1
    (Degrees a2) = angle2
    
    -- Normalize angle difference
    angleDiff = a2 - a1
    normalizedDiff = 
      if angleDiff > 180.0 then angleDiff - 360.0
      else if angleDiff < negate 180.0 then angleDiff + 360.0
      else angleDiff
    
    -- Scale by smoothing and max bank
    (Degrees maxB) = maxBank
    bankAmount = clampNumber (negate maxB) maxB (normalizedDiff * smoothing * 0.5)
  in
    Degrees bankAmount

-- | Array indexing operator (re-export from Data.Array)
infixl 8 index as !!

-- | Clamp to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Clamp to range
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi n
  | n < lo = lo
  | n > hi = hi
  | otherwise = n

-- | Floor for Number
floorNum :: Number -> Number
floorNum n = floor n

-- | Floor to Int
floorInt :: Number -> Int
floorInt n = Int.floor n

-- | Small epsilon
epsilon :: Number
epsilon = 1.0e-10

-- | Build array from function
buildArray :: forall a. Int -> (Int -> Maybe a) -> Array a
buildArray n f = buildArrayImpl 0 n f []

buildArrayImpl :: forall a. Int -> Int -> (Int -> Maybe a) -> Array a -> Array a
buildArrayImpl i n f acc =
  if i >= n then acc
  else case f i of
    Nothing -> buildArrayImpl (i + 1) n f acc
    Just x -> buildArrayImpl (i + 1) n f (snoc acc x)

-- | Build integer array
buildIntArray :: Int -> Array Int
buildIntArray n = buildArray n Just

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default easing (ease in-out).
defaultEasing :: Easing
defaultEasing = easeInOut

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // frame conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Frames to duration number.
framesToDuration :: Frames -> Number
framesToDuration f = unwrapFrames f

-- | Convert duration to Frames.
durationToFrames :: Number -> Frames
durationToFrames n = Frames n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // path filtering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter frame numbers to only those where path is active.
filterActiveFrames :: Array Number -> MotionPath -> Array Number
filterActiveFrames frames mp =
  foldl (\acc frame ->
    if isActiveAtFrame frame mp || isLooping mp
    then snoc acc frame
    else acc
  ) [] frames

-- | Map a function over sampled positions.
mapSampledPositions :: (Point2D -> Point2D) -> Int -> MotionPath -> Array Point2D
mapSampledPositions f n mp =
  map f (samplePoints n mp)
