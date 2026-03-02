{-|
Module      : Lattice.Services.Camera.MotionAnalysis
Description : Camera motion pattern detection
Copyright   : (c) Lattice Compositor, 2026
License     : MIT

Pure functions for analyzing camera motion patterns:
- Pan, zoom, orbit, rotation detection
- Motion magnitude calculations
- Motion type classification for export formats

Source: ui/src/services/export/cameraExportFormats.ts (lines 398-696)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Camera.MotionAnalysis
  ( -- * Types
    Vec3(..)
  , CameraKeyframe(..)
  , PanDirection(..)
  , ZoomDirection(..)
  , OrbitDirection(..)
  , CameraMotionAnalysis(..)
  , MotionCtrlSVDPreset(..)
  , CameraCtrlMotionType(..)
  , Wan22CameraMotion(..)
  , Uni3CTrajType(..)
    -- * Constants
  , panThreshold
  , zoomThreshold
  , orbitThreshold
  , rotationThreshold
    -- * Delta Calculations
  , calculatePositionDelta
  , calculateOrientationDelta
    -- * Detection Functions
  , detectPanDirection
  , detectZoomDirection
  , detectOrbitDirection
    -- * Full Analysis
  , emptyMotionAnalysis
  , analyzeCameraMotion
    -- * Preset Detection
  , detectMotionCtrlSVDPreset
  , detectCameraCtrlMotionType
  , mapToWan22FunCamera
  , detectUni3CTrajectoryType
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 3D vector.
data Vec3 = Vec3
  { v3X :: Double
  , v3Y :: Double
  , v3Z :: Double
  } deriving (Show, Eq)

-- | Camera keyframe.
data CameraKeyframe = CameraKeyframe
  { ckfFrame       :: Int
  , ckfPosition    :: Maybe Vec3
  , ckfOrientation :: Maybe Vec3
  } deriving (Show, Eq)

-- | Pan direction.
data PanDirection = PanUp | PanDown | PanLeft | PanRight
  deriving (Show, Eq)

-- | Zoom direction.
data ZoomDirection = ZoomIn | ZoomOut
  deriving (Show, Eq)

-- | Orbit direction.
data OrbitDirection = OrbitLeft | OrbitRight
  deriving (Show, Eq)

-- | Camera motion analysis result.
data CameraMotionAnalysis = CameraMotionAnalysis
  { cmaHasPan            :: Bool
  , cmaPanDirection      :: Maybe PanDirection
  , cmaPanMagnitude      :: Double
  , cmaHasZoom           :: Bool
  , cmaZoomDirection     :: Maybe ZoomDirection
  , cmaZoomMagnitude     :: Double
  , cmaHasOrbit          :: Bool
  , cmaOrbitDirection    :: Maybe OrbitDirection
  , cmaOrbitMagnitude    :: Double
  , cmaHasRotation       :: Bool
  , cmaRotationMagnitude :: Double
  } deriving (Show, Eq)

-- | MotionCtrl-SVD preset.
data MotionCtrlSVDPreset
  = SVDStatic
  | SVDZoomIn | SVDZoomOut
  | SVDRotateCW | SVDRotateCCW
  | SVDPanLeft | SVDPanRight | SVDPanUp | SVDPanDown
  deriving (Show, Eq)

-- | AnimateDiff CameraCtrl motion type.
data CameraCtrlMotionType
  = CCStatic
  | CCMoveForward | CCMoveBackward
  | CCMoveLeft | CCMoveRight | CCMoveUp | CCMoveDown
  | CCRotateLeft | CCRotateRight | CCRotateUp | CCRotateDown
  | CCRollLeft | CCRollRight
  deriving (Show, Eq)

-- | Wan 2.2 Fun Camera motion preset.
data Wan22CameraMotion
  = W22Static
  | W22ZoomIn | W22ZoomOut
  | W22PanUp | W22PanDown | W22PanLeft | W22PanRight
  | W22OrbitalLeft | W22OrbitalRight
  | W22PanUpZoomIn | W22PanUpZoomOut
  | W22PanDownZoomIn | W22PanDownZoomOut
  | W22PanLeftZoomIn | W22PanLeftZoomOut
  | W22PanRightZoomIn | W22PanRightZoomOut
  deriving (Show, Eq)

-- | Uni3C trajectory type.
data Uni3CTrajType = Uni3COrbit | Uni3CFree1 | Uni3CCustom
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Movement threshold for pan detection.
panThreshold :: Double
panThreshold = 30.0

-- | Movement threshold for zoom detection.
zoomThreshold :: Double
zoomThreshold = 50.0

-- | Rotation threshold for orbit detection.
orbitThreshold :: Double
orbitThreshold = 20.0

-- | Rotation threshold for rotation detection.
rotationThreshold :: Double
rotationThreshold = 5.0

-- | Default position.
defaultPosition :: Vec3
defaultPosition = Vec3 0 0 0

--------------------------------------------------------------------------------
-- Delta Calculations
--------------------------------------------------------------------------------

-- | Get position with default fallback.
getPosition :: CameraKeyframe -> Vec3
getPosition kf = maybe defaultPosition id (ckfPosition kf)

-- | Get orientation with default fallback.
getOrientation :: CameraKeyframe -> Vec3
getOrientation kf = maybe defaultPosition id (ckfOrientation kf)

-- | Calculate position delta.
calculatePositionDelta :: CameraKeyframe -> CameraKeyframe -> Vec3
calculatePositionDelta first lastKf =
  let fp = getPosition first
      lp = getPosition lastKf
  in Vec3 (v3X lp - v3X fp) (v3Y lp - v3Y fp) (v3Z lp - v3Z fp)

-- | Calculate orientation delta.
calculateOrientationDelta :: CameraKeyframe -> CameraKeyframe -> Vec3
calculateOrientationDelta first lastKf =
  let fo = getOrientation first
      lo = getOrientation lastKf
  in Vec3 (v3X lo - v3X fo) (v3Y lo - v3Y fo) (v3Z lo - v3Z fo)

--------------------------------------------------------------------------------
-- Detection Functions
--------------------------------------------------------------------------------

-- | Detect pan direction from position delta.
detectPanDirection :: Double -> Double -> Maybe PanDirection
detectPanDirection deltaX deltaY
  | absX > panThreshold || absY > panThreshold =
      if absX > absY
      then Just $ if deltaX > 0 then PanRight else PanLeft
      else Just $ if deltaY > 0 then PanDown else PanUp
  | otherwise = Nothing
  where
    absX = abs deltaX
    absY = abs deltaY

-- | Detect zoom direction from Z delta.
detectZoomDirection :: Double -> Maybe ZoomDirection
detectZoomDirection deltaZ
  | abs deltaZ > zoomThreshold = Just $ if deltaZ < 0 then ZoomIn else ZoomOut
  | otherwise = Nothing

-- | Detect orbit direction.
detectOrbitDirection :: Double -> Double -> Maybe OrbitDirection
detectOrbitDirection deltaRy deltaX
  | abs deltaRy > orbitThreshold && abs deltaX > panThreshold =
      Just $ if deltaRy > 0 then OrbitRight else OrbitLeft
  | otherwise = Nothing

--------------------------------------------------------------------------------
-- Full Analysis
--------------------------------------------------------------------------------

-- | Empty motion analysis.
emptyMotionAnalysis :: CameraMotionAnalysis
emptyMotionAnalysis = CameraMotionAnalysis
  { cmaHasPan = False, cmaPanDirection = Nothing, cmaPanMagnitude = 0
  , cmaHasZoom = False, cmaZoomDirection = Nothing, cmaZoomMagnitude = 0
  , cmaHasOrbit = False, cmaOrbitDirection = Nothing, cmaOrbitMagnitude = 0
  , cmaHasRotation = False, cmaRotationMagnitude = 0
  }

-- | Analyze camera motion from keyframes.
analyzeCameraMotion :: [CameraKeyframe] -> CameraMotionAnalysis
analyzeCameraMotion kfs
  | length kfs < 2 = emptyMotionAnalysis
  | otherwise =
      let first = head kfs
          lastKf = last kfs
          posDelta = calculatePositionDelta first lastKf
          oriDelta = calculateOrientationDelta first lastKf
          panDir = detectPanDirection (v3X posDelta) (v3Y posDelta)
          zoomDir = detectZoomDirection (v3Z posDelta)
          orbitDir = detectOrbitDirection (v3Y oriDelta) (v3X posDelta)
      in CameraMotionAnalysis
          { cmaHasPan = panDir /= Nothing
          , cmaPanDirection = panDir
          , cmaPanMagnitude = max (abs (v3X posDelta)) (abs (v3Y posDelta))
          , cmaHasZoom = zoomDir /= Nothing
          , cmaZoomDirection = zoomDir
          , cmaZoomMagnitude = abs (v3Z posDelta)
          , cmaHasOrbit = orbitDir /= Nothing
          , cmaOrbitDirection = orbitDir
          , cmaOrbitMagnitude = abs (v3Y oriDelta)
          , cmaHasRotation = abs (v3Y oriDelta) > rotationThreshold
          , cmaRotationMagnitude = abs (v3Y oriDelta)
          }

--------------------------------------------------------------------------------
-- Preset Detection
--------------------------------------------------------------------------------

-- | Detect MotionCtrl-SVD preset.
detectMotionCtrlSVDPreset :: [CameraKeyframe] -> MotionCtrlSVDPreset
detectMotionCtrlSVDPreset kfs
  | length kfs < 2 = SVDStatic
  | otherwise =
      let first = head kfs
          lastKf = last kfs
          posDelta = calculatePositionDelta first lastKf
          oriDelta = calculateOrientationDelta first lastKf
          threshold = 50.0
      in if abs (v3Z posDelta) > threshold
         then let distStart = abs $ v3Z $ getPosition first
                  distEnd = abs $ v3Z $ getPosition lastKf
              in if distEnd < distStart then SVDZoomIn else SVDZoomOut
         else if abs (v3Y oriDelta) > 15
         then if v3Y oriDelta > 0 then SVDRotateCW else SVDRotateCCW
         else if abs (v3X posDelta) > threshold
         then if v3X posDelta > 0 then SVDPanRight else SVDPanLeft
         else if abs (v3Y posDelta) > threshold
         then if v3Y posDelta > 0 then SVDPanDown else SVDPanUp
         else SVDStatic

-- | Detect CameraCtrl motion type.
detectCameraCtrlMotionType :: [CameraKeyframe] -> CameraCtrlMotionType
detectCameraCtrlMotionType kfs =
  let motion = analyzeCameraMotion kfs
  in if not (cmaHasPan motion) && not (cmaHasZoom motion) && not (cmaHasRotation motion)
     then CCStatic
     else if cmaHasZoom motion
     then case cmaZoomDirection motion of
            Just ZoomIn -> CCMoveForward
            Just ZoomOut -> CCMoveBackward
            Nothing -> CCStatic
     else if cmaHasPan motion
     then case cmaPanDirection motion of
            Just PanLeft -> CCMoveLeft
            Just PanRight -> CCMoveRight
            Just PanUp -> CCMoveUp
            Just PanDown -> CCMoveDown
            Nothing -> CCStatic
     else if cmaHasRotation motion && length kfs >= 2
     then let first = head kfs
              lastKf = last kfs
              oriDelta = calculateOrientationDelta first lastKf
              absRx = abs (v3X oriDelta)
              absRy = abs (v3Y oriDelta)
              absRz = abs (v3Z oriDelta)
          in if absRy > absRx && absRy > absRz
             then if v3Y oriDelta > 0 then CCRotateRight else CCRotateLeft
             else if absRx > absRz
             then if v3X oriDelta > 0 then CCRotateDown else CCRotateUp
             else if v3Z oriDelta > 0 then CCRollRight else CCRollLeft
     else CCStatic

-- | Map to Wan 2.2 Fun Camera preset.
mapToWan22FunCamera :: [CameraKeyframe] -> Wan22CameraMotion
mapToWan22FunCamera kfs =
  let motion = analyzeCameraMotion kfs
  in if cmaHasOrbit motion
     then case cmaOrbitDirection motion of
            Just OrbitLeft -> W22OrbitalLeft
            Just OrbitRight -> W22OrbitalRight
            Nothing -> W22Static
     else if cmaHasZoom motion && cmaHasPan motion
     then case (cmaPanDirection motion, cmaZoomDirection motion) of
            (Just PanUp, Just ZoomIn) -> W22PanUpZoomIn
            (Just PanUp, Just ZoomOut) -> W22PanUpZoomOut
            (Just PanDown, Just ZoomIn) -> W22PanDownZoomIn
            (Just PanDown, Just ZoomOut) -> W22PanDownZoomOut
            (Just PanLeft, Just ZoomIn) -> W22PanLeftZoomIn
            (Just PanLeft, Just ZoomOut) -> W22PanLeftZoomOut
            (Just PanRight, Just ZoomIn) -> W22PanRightZoomIn
            (Just PanRight, Just ZoomOut) -> W22PanRightZoomOut
            _ -> W22Static
     else if cmaHasZoom motion
     then case cmaZoomDirection motion of
            Just ZoomIn -> W22ZoomIn
            Just ZoomOut -> W22ZoomOut
            Nothing -> W22Static
     else if cmaHasPan motion
     then case cmaPanDirection motion of
            Just PanUp -> W22PanUp
            Just PanDown -> W22PanDown
            Just PanLeft -> W22PanLeft
            Just PanRight -> W22PanRight
            Nothing -> W22Static
     else W22Static

-- | Detect Uni3C trajectory type.
detectUni3CTrajectoryType :: [CameraKeyframe] -> Uni3CTrajType
detectUni3CTrajectoryType kfs =
  let motion = analyzeCameraMotion kfs
  in if cmaHasOrbit motion && cmaOrbitMagnitude motion > 45
     then Uni3COrbit
     else if cmaHasPan motion && cmaHasZoom motion
     then Uni3CCustom
     else if not (cmaHasPan motion) && not (cmaHasZoom motion) && not (cmaHasOrbit motion)
     then Uni3CFree1
     else Uni3CCustom
