-- | Lattice.Camera - 2.5D Camera System Types
-- |
-- | Source: lattice-core/lean/Lattice/Camera.lean

module Lattice.Camera
  ( CameraType(..)
  , AutoOrientMode(..)
  , MeasureFilmSize(..)
  , WireframeVisibility(..)
  , ViewType(..)
  , ViewLayout(..)
  , SpatialInterpolation(..)
  , TemporalInterpolation(..)
  , Vec3
  , Vec2
  , DepthOfFieldSettings
  , IrisProperties
  , HighlightProperties
  , Camera3D
  , CameraPreset
  , CustomViewState
  , CustomViews
  , ViewportState
  , ViewOptions
  , CameraKeyframe
  -- Constants
  , cameraPresets
  -- Factories
  , createDefaultCamera
  , defaultDepthOfField
  , defaultIris
  , defaultHighlight
  , defaultCustomViewState
  , defaultViewportState
  , defaultViewOptions
  ) where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data CameraType = CTOneNode | CTTwoNode

derive instance Eq CameraType
derive instance Generic CameraType _
instance Show CameraType where show = genericShow

data AutoOrientMode = AOMOff | AOMOrientAlongPath | AOMOrientTowardsPOI

derive instance Eq AutoOrientMode
derive instance Generic AutoOrientMode _
instance Show AutoOrientMode where show = genericShow

data MeasureFilmSize = MFSHorizontal | MFSVertical | MFSDiagonal

derive instance Eq MeasureFilmSize
derive instance Generic MeasureFilmSize _
instance Show MeasureFilmSize where show = genericShow

data WireframeVisibility = WVAlways | WVSelected | WVOff

derive instance Eq WireframeVisibility
derive instance Generic WireframeVisibility _
instance Show WireframeVisibility where show = genericShow

data ViewType
  = VTActiveCamera | VTCustom1 | VTCustom2 | VTCustom3
  | VTFront | VTBack | VTLeft | VTRight | VTTop | VTBottom

derive instance Eq ViewType
derive instance Generic ViewType _
instance Show ViewType where show = genericShow

data ViewLayout
  = VLOneView | VLTwoViewHorizontal | VLTwoViewVertical | VLFourView

derive instance Eq ViewLayout
derive instance Generic ViewLayout _
instance Show ViewLayout where show = genericShow

data SpatialInterpolation
  = SILinear | SIBezier | SIAutoBezier | SIContinuousBezier

derive instance Eq SpatialInterpolation
derive instance Generic SpatialInterpolation _
instance Show SpatialInterpolation where show = genericShow

data TemporalInterpolation = TILinear | TIBezier | TIHold

derive instance Eq TemporalInterpolation
derive instance Generic TemporalInterpolation _
instance Show TemporalInterpolation where show = genericShow

--------------------------------------------------------------------------------
-- Vectors
--------------------------------------------------------------------------------

type Vec3 =
  { x :: FiniteFloat
  , y :: FiniteFloat
  , z :: FiniteFloat
  }

type Vec2 =
  { x :: FiniteFloat
  , y :: FiniteFloat
  }

--------------------------------------------------------------------------------
-- Depth of Field
--------------------------------------------------------------------------------

type DepthOfFieldSettings =
  { enabled       :: Boolean
  , focusDistance :: PositiveFloat   -- Pixels
  , aperture      :: PositiveFloat   -- Pixels (internal)
  , fStop         :: PositiveFloat   -- f-stop (display)
  , blurLevel     :: UnitFloat       -- 0-1 multiplier
  , lockToZoom    :: Boolean
  }

type IrisProperties =
  { shape            :: FiniteFloat  -- 0-10 (pentagon to circle)
  , rotation         :: FiniteFloat  -- Degrees
  , roundness        :: UnitFloat    -- 0-1
  , aspectRatio      :: FiniteFloat  -- 0.5-2
  , diffractionFringe :: UnitFloat   -- 0-1
  }

type HighlightProperties =
  { gain       :: UnitFloat  -- 0-1
  , threshold  :: UnitFloat  -- 0-1
  , saturation :: UnitFloat  -- 0-1
  }

--------------------------------------------------------------------------------
-- Camera 3D
--------------------------------------------------------------------------------

type Camera3D =
  { id              :: NonEmptyString
  , name            :: NonEmptyString
  , cameraType      :: CameraType
  -- Transform
  , position        :: Vec3
  , pointOfInterest :: Vec3           -- Two-node only
  , orientation     :: Vec3           -- Combined XYZ rotation
  , xRotation       :: FiniteFloat    -- Individual rotation
  , yRotation       :: FiniteFloat
  , zRotation       :: FiniteFloat
  -- Lens settings
  , zoom            :: PositiveFloat  -- Pixels (AE internal)
  , focalLength     :: PositiveFloat  -- mm (display)
  , angleOfView     :: PositiveFloat  -- Degrees (computed)
  , filmSize        :: PositiveFloat  -- mm (default 36)
  , measureFilmSize :: MeasureFilmSize
  -- Depth of field
  , depthOfField    :: DepthOfFieldSettings
  -- Iris
  , iris            :: IrisProperties
  -- Highlight
  , highlight       :: HighlightProperties
  -- Auto-orient
  , autoOrient      :: AutoOrientMode
  -- Clipping
  , nearClip        :: PositiveFloat
  , farClip         :: PositiveFloat
  }

--------------------------------------------------------------------------------
-- Camera Preset
--------------------------------------------------------------------------------

type CameraPreset =
  { name        :: NonEmptyString
  , focalLength :: PositiveFloat  -- mm
  , angleOfView :: PositiveFloat  -- Degrees
  , zoom        :: PositiveFloat  -- Pixels
  }

--------------------------------------------------------------------------------
-- Custom View State
--------------------------------------------------------------------------------

type CustomViewState =
  { orbitCenter   :: Vec3
  , orbitDistance :: PositiveFloat
  , orbitPhi      :: FiniteFloat    -- Vertical angle (0=top, 90=side)
  , orbitTheta    :: FiniteFloat    -- Horizontal angle
  , orthoZoom     :: PositiveFloat  -- For orthographic views
  , orthoOffset   :: Vec2
  }

type CustomViews =
  { custom1 :: CustomViewState
  , custom2 :: CustomViewState
  , custom3 :: CustomViewState
  }

type ViewportState =
  { layout          :: ViewLayout
  , views           :: Array ViewType  -- Which view in each panel
  , customViews     :: CustomViews
  , activeViewIndex :: Int
  }

--------------------------------------------------------------------------------
-- View Options
--------------------------------------------------------------------------------

type ViewOptions =
  { cameraWireframes       :: WireframeVisibility
  , lightWireframes        :: WireframeVisibility
  , showMotionPaths        :: Boolean
  , showLayerPaths         :: Boolean  -- Shape/mask path visibility
  , showLayerHandles       :: Boolean
  , showSafeZones          :: Boolean
  , showGrid               :: Boolean
  , showRulers             :: Boolean
  , show3DReferenceAxes    :: Boolean
  , showCompositionBounds  :: Boolean  -- Canvas as 3D plane
  , showFocalPlane         :: Boolean  -- DOF focus indicator
  }

--------------------------------------------------------------------------------
-- Camera Keyframe
--------------------------------------------------------------------------------

type CameraKeyframe =
  { frame                  :: FrameNumber
  -- Transform (optional)
  , position               :: Maybe Vec3
  , pointOfInterest        :: Maybe Vec3
  , orientation            :: Maybe Vec3
  , xRotation              :: Maybe FiniteFloat
  , yRotation              :: Maybe FiniteFloat
  , zRotation              :: Maybe FiniteFloat
  -- Lens
  , zoom                   :: Maybe PositiveFloat
  , focalLength            :: Maybe PositiveFloat
  , focusDistance          :: Maybe PositiveFloat
  , aperture               :: Maybe PositiveFloat
  -- Bezier handles
  , inHandle               :: Maybe Vec2
  , outHandle              :: Maybe Vec2
  -- Interpolation
  , spatialInterpolation   :: Maybe SpatialInterpolation
  , temporalInterpolation  :: Maybe TemporalInterpolation
  -- Separate dimensions
  , separateDimensions     :: Boolean
  }

--------------------------------------------------------------------------------
-- Camera Presets (standard focal lengths)
--------------------------------------------------------------------------------

-- | Standard camera presets matching industry focal lengths
-- | Note: Uses unsafe constructors internally - values are known-valid constants
cameraPresets :: Array CameraPreset
cameraPresets =
  [ mkPreset "15mm" 15.0 100.4 533.0
  , mkPreset "20mm" 20.0 84.0 711.0
  , mkPreset "24mm" 24.0 73.7 853.0
  , mkPreset "28mm" 28.0 65.5 996.0
  , mkPreset "35mm" 35.0 54.4 1244.0
  , mkPreset "50mm" 50.0 39.6 1778.0
  , mkPreset "80mm" 80.0 25.4 2844.0
  , mkPreset "135mm" 135.0 15.2 4800.0
  ]
  where
    -- Internal helper - values are compile-time constants, always valid
    mkPreset :: String -> Number -> Number -> Number -> CameraPreset
    mkPreset n fl aov z =
      { name: unsafeNonEmptyString n
      , focalLength: unsafePositiveFloat fl
      , angleOfView: unsafePositiveFloat aov
      , zoom: unsafePositiveFloat z
      }
    -- These are safe because we only use them with known-valid constants
    unsafeNonEmptyString :: String -> NonEmptyString
    unsafeNonEmptyString s = case mkNonEmptyString s of
      Just nes -> nes
      Nothing -> unsafeNonEmptyString "error"  -- Never reached for non-empty strings
    unsafePositiveFloat :: Number -> PositiveFloat
    unsafePositiveFloat n = case mkPositiveFloat n of
      Just pf -> pf
      Nothing -> unsafePositiveFloat 1.0  -- Never reached for positive numbers

--------------------------------------------------------------------------------
-- Default Values (Factory Functions)
--------------------------------------------------------------------------------

-- | Default depth of field settings (disabled)
defaultDepthOfField :: DepthOfFieldSettings
defaultDepthOfField =
  { enabled: false
  , focusDistance: pf 1500.0
  , aperture: pf 50.0
  , fStop: pf 2.8
  , blurLevel: uf 1.0
  , lockToZoom: false
  }
  where
    pf n = case mkPositiveFloat n of
      Just v -> v
      Nothing -> PositiveFloat 1.0
    uf n = case mkUnitFloat n of
      Just v -> v
      Nothing -> UnitFloat 0.0

-- | Default iris properties
defaultIris :: IrisProperties
defaultIris =
  { shape: ff 7.0           -- Heptagon
  , rotation: ff 0.0
  , roundness: uf 0.0
  , aspectRatio: ff 1.0
  , diffractionFringe: uf 0.0
  }
  where
    ff n = case mkFiniteFloat n of
      Just v -> v
      Nothing -> FiniteFloat 0.0
    uf n = case mkUnitFloat n of
      Just v -> v
      Nothing -> UnitFloat 0.0

-- | Default highlight properties
defaultHighlight :: HighlightProperties
defaultHighlight =
  { gain: uf 0.0
  , threshold: uf 1.0
  , saturation: uf 1.0
  }
  where
    uf n = case mkUnitFloat n of
      Just v -> v
      Nothing -> UnitFloat 0.0

-- | Default custom view state
defaultCustomViewState :: CustomViewState
defaultCustomViewState =
  { orbitCenter: vec3 0.0 0.0 0.0
  , orbitDistance: pf 2000.0
  , orbitPhi: ff 60.0
  , orbitTheta: ff 45.0
  , orthoZoom: pf 1.0
  , orthoOffset: vec2 0.0 0.0
  }
  where
    ff n = case mkFiniteFloat n of
      Just v -> v
      Nothing -> FiniteFloat 0.0
    pf n = case mkPositiveFloat n of
      Just v -> v
      Nothing -> PositiveFloat 1.0
    vec2 x y = { x: ff x, y: ff y }
    vec3 x y z = { x: ff x, y: ff y, z: ff z }

-- | Default viewport state (single view)
defaultViewportState :: ViewportState
defaultViewportState =
  { layout: VLOneView
  , views: [VTActiveCamera]
  , customViews:
      { custom1: defaultCustomViewState
      , custom2: defaultCustomViewState { orbitPhi = ff 90.0, orbitTheta = ff 0.0 }
      , custom3: defaultCustomViewState { orbitPhi = ff 0.0, orbitTheta = ff 0.0 }
      }
  , activeViewIndex: 0
  }
  where
    ff n = case mkFiniteFloat n of
      Just v -> v
      Nothing -> FiniteFloat 0.0

-- | Default view options
defaultViewOptions :: ViewOptions
defaultViewOptions =
  { cameraWireframes: WVSelected
  , lightWireframes: WVSelected
  , showMotionPaths: true
  , showLayerPaths: true
  , showLayerHandles: true
  , showSafeZones: false
  , showGrid: false
  , showRulers: true
  , show3DReferenceAxes: true
  , showCompositionBounds: true
  , showFocalPlane: false
  }

-- | Create a default camera for a composition with given dimensions
-- | Matches TS createDefaultCamera(compWidth, compHeight)
createDefaultCamera :: NonEmptyString -> Number -> Number -> Camera3D
createDefaultCamera cameraId compWidth compHeight =
  { id: cameraId
  , name: nes "Camera 1"
  , cameraType: CTTwoNode
  , position: vec3 (compWidth / 2.0) (compHeight / 2.0) (-1500.0)
  , pointOfInterest: vec3 (compWidth / 2.0) (compHeight / 2.0) 0.0
  , orientation: vec3 0.0 0.0 0.0
  , xRotation: ff 0.0
  , yRotation: ff 0.0
  , zRotation: ff 0.0
  , zoom: pf 1778.0
  , focalLength: pf 50.0
  , angleOfView: pf 39.6
  , filmSize: pf 36.0
  , measureFilmSize: MFSHorizontal
  , depthOfField: defaultDepthOfField
  , iris: defaultIris
  , highlight: defaultHighlight
  , autoOrient: AOMOff
  , nearClip: pf 1.0
  , farClip: pf 10000.0
  }
  where
    nes s = case mkNonEmptyString s of
      Just v -> v
      Nothing -> NonEmptyString "error"
    ff n = case mkFiniteFloat n of
      Just v -> v
      Nothing -> FiniteFloat 0.0
    pf n = case mkPositiveFloat n of
      Just v -> v
      Nothing -> PositiveFloat 1.0
    vec3 x y z = { x: ff x, y: ff y, z: ff z }
