{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Camera
Description : 2.5D Camera System Types
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/Camera.lean
-}

module Lattice.Camera
  ( -- * Enumerations
    CameraType(..)
  , AutoOrientMode(..)
  , MeasureFilmSize(..)
  , WireframeVisibility(..)
  , ViewType(..)
  , ViewLayout(..)
  , SpatialInterpolation(..)
  , TemporalInterpolation(..)
    -- * Vectors
  , Vec3(..)
  , Vec2(..)
    -- * DOF Settings
  , DepthOfFieldSettings(..)
  , IrisProperties(..)
  , HighlightProperties(..)
    -- * Camera
  , Camera3D(..)
  , CameraPreset(..)
    -- * Viewport
  , CustomViewState(..)
  , CustomViews(..)
  , ViewportState(..)
  , ViewOptions(..)
    -- * Keyframe
  , CameraKeyframe(..)
  ) where

import GHC.Generics (Generic)
import Data.Vector (Vector)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data CameraType = CTOneNode | CTTwoNode
  deriving stock (Eq, Show, Generic)

data AutoOrientMode = AOMOff | AOMOrientAlongPath | AOMOrientTowardsPOI
  deriving stock (Eq, Show, Generic)

data MeasureFilmSize = MFSHorizontal | MFSVertical | MFSDiagonal
  deriving stock (Eq, Show, Generic)

data WireframeVisibility = WVAlways | WVSelected | WVOff
  deriving stock (Eq, Show, Generic)

data ViewType
  = VTActiveCamera | VTCustom1 | VTCustom2 | VTCustom3
  | VTFront | VTBack | VTLeft | VTRight | VTTop | VTBottom
  deriving stock (Eq, Show, Generic)

data ViewLayout
  = VLOneView | VLTwoViewHorizontal | VLTwoViewVertical | VLFourView
  deriving stock (Eq, Show, Generic)

data SpatialInterpolation
  = SILinear | SIBezier | SIAutoBezier | SIContinuousBezier
  deriving stock (Eq, Show, Generic)

data TemporalInterpolation = TILinear | TIBezier | TIHold
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Vectors
--------------------------------------------------------------------------------

data Vec3 = Vec3
  { v3X :: !FiniteFloat
  , v3Y :: !FiniteFloat
  , v3Z :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

data Vec2 = Vec2
  { v2X :: !FiniteFloat
  , v2Y :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Depth of Field
--------------------------------------------------------------------------------

data DepthOfFieldSettings = DepthOfFieldSettings
  { dofEnabled       :: !Bool
  , dofFocusDistance :: !PositiveFloat   -- Pixels
  , dofAperture      :: !PositiveFloat   -- Pixels (internal)
  , dofFStop         :: !PositiveFloat   -- f-stop (display)
  , dofBlurLevel     :: !UnitFloat       -- 0-1 multiplier
  , dofLockToZoom    :: !Bool
  } deriving stock (Eq, Show, Generic)

data IrisProperties = IrisProperties
  { irisShape            :: !FiniteFloat  -- 0-10 (pentagon to circle)
  , irisRotation         :: !FiniteFloat  -- Degrees
  , irisRoundness        :: !UnitFloat    -- 0-1
  , irisAspectRatio      :: !FiniteFloat  -- 0.5-2
  , irisDiffractionFringe :: !UnitFloat   -- 0-1
  } deriving stock (Eq, Show, Generic)

data HighlightProperties = HighlightProperties
  { hlGain       :: !UnitFloat  -- 0-1
  , hlThreshold  :: !UnitFloat  -- 0-1
  , hlSaturation :: !UnitFloat  -- 0-1
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Camera 3D
--------------------------------------------------------------------------------

data Camera3D = Camera3D
  { cam3dId              :: !NonEmptyString
  , cam3dName            :: !NonEmptyString
  , cam3dCameraType      :: !CameraType
  -- Transform
  , cam3dPosition        :: !Vec3
  , cam3dPointOfInterest :: !Vec3           -- Two-node only
  , cam3dOrientation     :: !Vec3           -- Combined XYZ rotation
  , cam3dXRotation       :: !FiniteFloat    -- Individual rotation
  , cam3dYRotation       :: !FiniteFloat
  , cam3dZRotation       :: !FiniteFloat
  -- Lens settings
  , cam3dZoom            :: !PositiveFloat  -- Pixels (AE internal)
  , cam3dFocalLength     :: !PositiveFloat  -- mm (display)
  , cam3dAngleOfView     :: !PositiveFloat  -- Degrees (computed)
  , cam3dFilmSize        :: !PositiveFloat  -- mm (default 36)
  , cam3dMeasureFilmSize :: !MeasureFilmSize
  -- Depth of field
  , cam3dDepthOfField    :: !DepthOfFieldSettings
  -- Iris
  , cam3dIris            :: !IrisProperties
  -- Highlight
  , cam3dHighlight       :: !HighlightProperties
  -- Auto-orient
  , cam3dAutoOrient      :: !AutoOrientMode
  -- Clipping
  , cam3dNearClip        :: !PositiveFloat
  , cam3dFarClip         :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Camera Preset
--------------------------------------------------------------------------------

data CameraPreset = CameraPreset
  { cpName        :: !NonEmptyString
  , cpFocalLength :: !PositiveFloat  -- mm
  , cpAngleOfView :: !PositiveFloat  -- Degrees
  , cpZoom        :: !PositiveFloat  -- Pixels
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Custom View State
--------------------------------------------------------------------------------

data CustomViewState = CustomViewState
  { cvsOrbitCenter   :: !Vec3
  , cvsOrbitDistance :: !PositiveFloat
  , cvsOrbitPhi      :: !FiniteFloat    -- Vertical angle (0=top, 90=side)
  , cvsOrbitTheta    :: !FiniteFloat    -- Horizontal angle
  , cvsOrthoZoom     :: !PositiveFloat  -- For orthographic views
  , cvsOrthoOffset   :: !Vec2
  } deriving stock (Eq, Show, Generic)

data CustomViews = CustomViews
  { cvCustom1 :: !CustomViewState
  , cvCustom2 :: !CustomViewState
  , cvCustom3 :: !CustomViewState
  } deriving stock (Eq, Show, Generic)

data ViewportState = ViewportState
  { vsLayout          :: !ViewLayout
  , vsViews           :: !(Vector ViewType)  -- Which view in each panel
  , vsCustomViews     :: !CustomViews
  , vsActiveViewIndex :: !Int
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- View Options
--------------------------------------------------------------------------------

data ViewOptions = ViewOptions
  { voCameraWireframes       :: !WireframeVisibility
  , voLightWireframes        :: !WireframeVisibility
  , voShowMotionPaths        :: !Bool
  , voShowLayerPaths         :: !Bool  -- Shape/mask path visibility
  , voShowLayerHandles       :: !Bool
  , voShowSafeZones          :: !Bool
  , voShowGrid               :: !Bool
  , voShowRulers             :: !Bool
  , voShow3DReferenceAxes    :: !Bool
  , voShowCompositionBounds  :: !Bool  -- Canvas as 3D plane
  , voShowFocalPlane         :: !Bool  -- DOF focus indicator
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Camera Keyframe
--------------------------------------------------------------------------------

data CameraKeyframe = CameraKeyframe
  { ckFrame                  :: !FrameNumber
  -- Transform (optional)
  , ckPosition               :: !(Maybe Vec3)
  , ckPointOfInterest        :: !(Maybe Vec3)
  , ckOrientation            :: !(Maybe Vec3)
  , ckXRotation              :: !(Maybe FiniteFloat)
  , ckYRotation              :: !(Maybe FiniteFloat)
  , ckZRotation              :: !(Maybe FiniteFloat)
  -- Lens
  , ckZoom                   :: !(Maybe PositiveFloat)
  , ckFocalLength            :: !(Maybe PositiveFloat)
  , ckFocusDistance          :: !(Maybe PositiveFloat)
  , ckAperture               :: !(Maybe PositiveFloat)
  -- Bezier handles
  , ckInHandle               :: !(Maybe Vec2)
  , ckOutHandle              :: !(Maybe Vec2)
  -- Interpolation
  , ckSpatialInterpolation   :: !(Maybe SpatialInterpolation)
  , ckTemporalInterpolation  :: !(Maybe TemporalInterpolation)
  -- Separate dimensions
  , ckSeparateDimensions     :: !Bool
  } deriving stock (Eq, Show, Generic)
