-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // motion // camera3d // presets
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera3D Presets: Standard camera lens presets.
-- |
-- | Common focal lengths with pre-calculated zoom and angle of view.

module Hydrogen.Schema.Motion.Camera3D.Presets
  ( -- * Camera Preset
    CameraPreset(..)
  , mkCameraPreset
  
    -- * Standard Presets
  , allCameraPresets
  , preset15mm
  , preset20mm
  , preset24mm
  , preset35mm
  , preset50mm
  , preset80mm
  , preset135mm
  , preset200mm
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded (clampNumber, clampNumberMin)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // camera // preset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera lens preset.
-- |
-- | Common focal lengths with pre-calculated zoom and angle of view.
newtype CameraPreset = CameraPreset
  { name        :: String   -- ^ Preset name (e.g., "50mm")
  , focalLength :: Number   -- ^ Focal length in mm
  , angleOfView :: Number   -- ^ Angle of view in degrees
  , zoom        :: Number   -- ^ Zoom in pixels
  }

derive instance eqCameraPreset :: Eq CameraPreset

instance showCameraPreset :: Show CameraPreset where
  show (CameraPreset p) = "(CameraPreset " <> p.name <> ")"

-- | Create a camera preset with validation.
mkCameraPreset
  :: { name        :: String
     , focalLength :: Number
     , angleOfView :: Number
     , zoom        :: Number
     }
  -> CameraPreset
mkCameraPreset cfg = CameraPreset
  { name: cfg.name
  , focalLength: clampNumberMin 0.1 cfg.focalLength
  , angleOfView: clampNumber 0.1 179.9 cfg.angleOfView
  , zoom: clampNumberMin 0.1 cfg.zoom
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // standard // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | All standard camera presets for enumeration.
allCameraPresets :: Array CameraPreset
allCameraPresets = 
  [ preset15mm
  , preset20mm
  , preset24mm
  , preset35mm
  , preset50mm
  , preset80mm
  , preset135mm
  , preset200mm
  ]

-- | 15mm ultra-wide preset.
preset15mm :: CameraPreset
preset15mm = CameraPreset
  { name: "15mm"
  , focalLength: 15.0
  , angleOfView: 100.4
  , zoom: 240.0
  }

-- | 20mm wide preset.
preset20mm :: CameraPreset
preset20mm = CameraPreset
  { name: "20mm"
  , focalLength: 20.0
  , angleOfView: 84.0
  , zoom: 320.0
  }

-- | 24mm wide preset.
preset24mm :: CameraPreset
preset24mm = CameraPreset
  { name: "24mm"
  , focalLength: 24.0
  , angleOfView: 73.7
  , zoom: 384.0
  }

-- | 35mm standard wide preset.
preset35mm :: CameraPreset
preset35mm = CameraPreset
  { name: "35mm"
  , focalLength: 35.0
  , angleOfView: 54.4
  , zoom: 560.0
  }

-- | 50mm standard preset.
preset50mm :: CameraPreset
preset50mm = CameraPreset
  { name: "50mm"
  , focalLength: 50.0
  , angleOfView: 39.6
  , zoom: 800.0
  }

-- | 80mm portrait preset.
preset80mm :: CameraPreset
preset80mm = CameraPreset
  { name: "80mm"
  , focalLength: 80.0
  , angleOfView: 25.4
  , zoom: 1280.0
  }

-- | 135mm telephoto preset.
preset135mm :: CameraPreset
preset135mm = CameraPreset
  { name: "135mm"
  , focalLength: 135.0
  , angleOfView: 15.2
  , zoom: 2160.0
  }

-- | 200mm telephoto preset.
preset200mm :: CameraPreset
preset200mm = CameraPreset
  { name: "200mm"
  , focalLength: 200.0
  , angleOfView: 10.3
  , zoom: 3200.0
  }
