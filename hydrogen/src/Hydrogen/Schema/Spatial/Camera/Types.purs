-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // spatial // camera // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Extended Camera Types — Cubemap and VR cameras for specialized rendering.
-- |
-- | Supplements the base Camera module with:
-- |
-- | ## CubemapCamera
-- | Renders 6 faces for environment mapping:
-- | - +X, -X, +Y, -Y, +Z, -Z views
-- | - Used for: Reflections, skyboxes, IBL probes
-- |
-- | ## VRCamera (Stereo)
-- | Renders left and right eye views:
-- | - IPD (Inter-Pupillary Distance) controls eye separation
-- | - Used for: VR headsets, stereoscopic rendering
-- |
-- | ## CinematicCamera
-- | Film camera with additional parameters:
-- | - Lens distortion (barrel, pincushion)
-- | - Chromatic aberration
-- | - Vignetting

module Hydrogen.Schema.Spatial.Camera.Types
  ( -- * Cubemap Camera
    CubemapFace(..)
  , CubemapCamera(..)
  , cubemapCamera
  , getFaceCamera
  
  -- * VR/Stereo Camera
  , Eye(..)
  , VRCamera(..)
  , vrCamera
  , getEyeCamera
  
  -- * Cinematic Camera
  , LensDistortion(..)
  , CinematicCamera(..)
  , cinematicCamera
  
  -- * Accessors
  , ipd
  , faceResolution
  , distortionK
  
  -- * Cubemap
  , allFaces
  , faceDirection
  , faceFromIndex
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Spatial.FOV (FOV)
import Hydrogen.Schema.Spatial.FOV as FOV
import Hydrogen.Schema.Spatial.NearClip (NearClip)
import Hydrogen.Schema.Spatial.FarClip (FarClip)
import Hydrogen.Schema.Spatial.FocalLength (FocalLength)
import Hydrogen.Schema.Spatial.SensorWidth (SensorWidth)
import Hydrogen.Schema.Spatial.Exposure (Exposure)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cubemap face
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cubemap face direction
-- |
-- | The 6 faces of a cube, each representing a 90° FOV view.
data CubemapFace
  = PositiveX  -- ^ Right (+X)
  | NegativeX  -- ^ Left (-X)
  | PositiveY  -- ^ Up (+Y)
  | NegativeY  -- ^ Down (-Y)
  | PositiveZ  -- ^ Front (+Z)
  | NegativeZ  -- ^ Back (-Z)

derive instance eqCubemapFace :: Eq CubemapFace
derive instance ordCubemapFace :: Ord CubemapFace

instance showCubemapFace :: Show CubemapFace where
  show PositiveX = "PositiveX"
  show NegativeX = "NegativeX"
  show PositiveY = "PositiveY"
  show NegativeY = "NegativeY"
  show PositiveZ = "PositiveZ"
  show NegativeZ = "NegativeZ"

-- | All 6 cubemap faces in standard order
allFaces :: Array CubemapFace
allFaces = [PositiveX, NegativeX, PositiveY, NegativeY, PositiveZ, NegativeZ]

-- | Get the direction vector for a cubemap face
-- |
-- | Returns the unit direction that this face "looks at".
faceDirection :: CubemapFace -> { x :: Number, y :: Number, z :: Number }
faceDirection PositiveX = { x:  1.0, y:  0.0, z:  0.0 }
faceDirection NegativeX = { x: -1.0, y:  0.0, z:  0.0 }
faceDirection PositiveY = { x:  0.0, y:  1.0, z:  0.0 }
faceDirection NegativeY = { x:  0.0, y: -1.0, z:  0.0 }
faceDirection PositiveZ = { x:  0.0, y:  0.0, z:  1.0 }
faceDirection NegativeZ = { x:  0.0, y:  0.0, z: -1.0 }

-- | Parse face from index
-- |
-- | Standard cubemap face order: +X, -X, +Y, -Y, +Z, -Z
faceFromIndex :: Int -> Maybe CubemapFace
faceFromIndex 0 = Just PositiveX
faceFromIndex 1 = Just NegativeX
faceFromIndex 2 = Just PositiveY
faceFromIndex 3 = Just NegativeY
faceFromIndex 4 = Just PositiveZ
faceFromIndex 5 = Just NegativeZ
faceFromIndex _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // cubemap camera
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera for rendering environment cubemaps
-- |
-- | Renders 6 square views with 90° FOV each, forming a complete
-- | 360° environment capture.
newtype CubemapCamera = CubemapCamera
  { resolution :: Int       -- ^ Face resolution (e.g., 512, 1024)
  , near :: NearClip
  , far :: FarClip
  }

derive instance eqCubemapCamera :: Eq CubemapCamera

instance showCubemapCamera :: Show CubemapCamera where
  show (CubemapCamera c) =
    "CubemapCamera { resolution: " <> show c.resolution <>
    ", near: " <> show c.near <>
    ", far: " <> show c.far <> " }"

-- | Create a cubemap camera
cubemapCamera :: Int -> NearClip -> FarClip -> CubemapCamera
cubemapCamera resolution near far = CubemapCamera { resolution, near, far }

-- | Get face resolution
faceResolution :: CubemapCamera -> Int
faceResolution (CubemapCamera c) = c.resolution

-- | Get camera parameters for a specific face
-- |
-- | Returns the FOV (always 90°) and clipping planes.
-- | Rotation must be applied separately based on face.
getFaceCamera :: CubemapFace -> CubemapCamera -> { fov :: FOV, near :: NearClip, far :: FarClip }
getFaceCamera _ (CubemapCamera c) =
  { fov: FOV.fov 90.0  -- Cubemap faces are always 90° FOV
  , near: c.near
  , far: c.far
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // eye
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stereo eye
data Eye
  = LeftEye
  | RightEye

derive instance eqEye :: Eq Eye
derive instance ordEye :: Ord Eye

instance showEye :: Show Eye where
  show LeftEye = "LeftEye"
  show RightEye = "RightEye"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // vr camera
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stereo camera for VR rendering
-- |
-- | Renders separate left and right eye views with parallax based on IPD.
newtype VRCamera = VRCamera
  { fov :: FOV                    -- ^ Vertical FOV per eye
  , near :: NearClip
  , far :: FarClip
  , ipd :: Number                 -- ^ Inter-pupillary distance in meters
  , eyeToHeadTransform :: Number  -- ^ Additional per-eye transform offset
  }

derive instance eqVRCamera :: Eq VRCamera

instance showVRCamera :: Show VRCamera where
  show (VRCamera c) =
    "VRCamera { fov: " <> show c.fov <>
    ", near: " <> show c.near <>
    ", far: " <> show c.far <>
    ", ipd: " <> show c.ipd <> " }"

-- | Create a VR camera
-- |
-- | Default IPD is 0.064 meters (64mm, average human).
vrCamera :: FOV -> NearClip -> FarClip -> VRCamera
vrCamera fov near far = VRCamera
  { fov
  , near
  , far
  , ipd: 0.064  -- 64mm default IPD
  , eyeToHeadTransform: 0.0
  }

-- | Get IPD (inter-pupillary distance)
ipd :: VRCamera -> Number
ipd (VRCamera c) = c.ipd

-- | Get camera parameters for a specific eye
-- |
-- | Returns offset from center: left eye is -IPD/2, right eye is +IPD/2.
getEyeCamera :: Eye -> VRCamera -> { fov :: FOV, near :: NearClip, far :: FarClip, offset :: Number }
getEyeCamera eye (VRCamera c) =
  let halfIPD = c.ipd / 2.0
      offset = case eye of
        LeftEye -> -halfIPD
        RightEye -> halfIPD
  in { fov: c.fov, near: c.near, far: c.far, offset }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // lens distortion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lens distortion parameters
-- |
-- | Models radial distortion (barrel/pincushion) using Brown-Conrady model:
-- | r' = r * (1 + k1*r² + k2*r⁴ + k3*r⁶)
newtype LensDistortion = LensDistortion
  { k1 :: Number  -- ^ First radial distortion coefficient
  , k2 :: Number  -- ^ Second radial distortion coefficient
  , k3 :: Number  -- ^ Third radial distortion coefficient
  }

derive instance eqLensDistortion :: Eq LensDistortion

instance showLensDistortion :: Show LensDistortion where
  show (LensDistortion d) =
    "LensDistortion { k1: " <> show d.k1 <>
    ", k2: " <> show d.k2 <>
    ", k3: " <> show d.k3 <> " }"

-- | No distortion
noDistortion :: LensDistortion
noDistortion = LensDistortion { k1: 0.0, k2: 0.0, k3: 0.0 }

-- | Get distortion coefficients as array
distortionK :: LensDistortion -> Array Number
distortionK (LensDistortion d) = [d.k1, d.k2, d.k3]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cinematic camera
-- ═════════════════════════════════════════════════════════════════════════════

-- | Film/cinematic camera with lens effects
-- |
-- | Extends physical camera with:
-- | - Lens distortion (barrel/pincushion)
-- | - Chromatic aberration
-- | - Vignetting
-- | - Anamorphic squeeze
newtype CinematicCamera = CinematicCamera
  { focalLength :: FocalLength
  , sensorWidth :: SensorWidth
  , exposure :: Exposure
  , near :: NearClip
  , far :: FarClip
  , focusDistance :: Maybe Number
  , aperture :: Maybe Number       -- f-stop
  , distortion :: LensDistortion
  , chromaticAberration :: Number  -- 0-1 strength
  , vignetting :: Number           -- 0-1 strength
  , anamorphicSqueeze :: Number    -- 1.0 = spherical, 2.0 = 2x anamorphic
  }

derive instance eqCinematicCamera :: Eq CinematicCamera

instance showCinematicCamera :: Show CinematicCamera where
  show (CinematicCamera c) =
    "CinematicCamera { focalLength: " <> show c.focalLength <>
    ", sensorWidth: " <> show c.sensorWidth <>
    ", anamorphic: " <> show c.anamorphicSqueeze <> "x }"

-- | Create a cinematic camera
cinematicCamera :: FocalLength -> SensorWidth -> Exposure -> NearClip -> FarClip -> CinematicCamera
cinematicCamera focalLength sensorWidth exposure near far = CinematicCamera
  { focalLength
  , sensorWidth
  , exposure
  , near
  , far
  , focusDistance: Nothing
  , aperture: Nothing
  , distortion: noDistortion
  , chromaticAberration: 0.0
  , vignetting: 0.0
  , anamorphicSqueeze: 1.0
  }
