-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // motion // camera-3d // depth-of-field
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera3D Depth of Field: DOF settings, iris, and highlight properties.
-- |
-- | Controls focus distance, aperture, bokeh shape, and highlight behavior.

module Hydrogen.Schema.Motion.Camera3D.DepthOfField
  ( -- * Depth of Field Settings
    DepthOfFieldSettings(..)
  , mkDepthOfFieldSettings
  , defaultDepthOfFieldSettings
  , dofDisabled
  
    -- * Iris Properties
  , IrisProperties(..)
  , mkIrisProperties
  , defaultIrisProperties
  
    -- * Highlight Properties
  , HighlightProperties(..)
  , mkHighlightProperties
  , defaultHighlightProperties
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded (clampNumber, clampNumberMin)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // depth-of-field // dof
-- ═════════════════════════════════════════════════════════════════════════════

-- | Depth of field settings for camera.
-- |
-- | Controls focus distance, aperture, and blur intensity.
newtype DepthOfFieldSettings = DepthOfFieldSettings
  { enabled       :: Boolean       -- ^ DOF enabled
  , focusDistance :: Number        -- ^ Focus distance in pixels (positive)
  , aperture      :: Number        -- ^ Aperture in pixels (internal, positive)
  , fStop         :: Number        -- ^ f-stop for display (positive)
  , blurLevel     :: Number        -- ^ Blur multiplier 0-1
  , lockToZoom    :: Boolean       -- ^ Lock focus to zoom
  }

derive instance eqDepthOfFieldSettings :: Eq DepthOfFieldSettings

instance showDepthOfFieldSettings :: Show DepthOfFieldSettings where
  show (DepthOfFieldSettings d) =
    "(DOF enabled:" <> show d.enabled
    <> " focus:" <> show d.focusDistance
    <> " f/" <> show d.fStop <> ")"

-- | Create depth of field settings with validation.
mkDepthOfFieldSettings
  :: { enabled       :: Boolean
     , focusDistance :: Number
     , aperture      :: Number
     , fStop         :: Number
     , blurLevel     :: Number
     , lockToZoom    :: Boolean
     }
  -> DepthOfFieldSettings
mkDepthOfFieldSettings cfg = DepthOfFieldSettings
  { enabled: cfg.enabled
  , focusDistance: clampNumberMin 0.1 cfg.focusDistance
  , aperture: clampNumberMin 0.1 cfg.aperture
  , fStop: clampNumberMin 0.1 cfg.fStop
  , blurLevel: clampNumber 0.0 1.0 cfg.blurLevel
  , lockToZoom: cfg.lockToZoom
  }

-- | Default depth of field settings (disabled).
defaultDepthOfFieldSettings :: DepthOfFieldSettings
defaultDepthOfFieldSettings = DepthOfFieldSettings
  { enabled: false
  , focusDistance: 1000.0
  , aperture: 50.0
  , fStop: 5.6
  , blurLevel: 1.0
  , lockToZoom: false
  }

-- | Disabled depth of field.
dofDisabled :: DepthOfFieldSettings
dofDisabled = defaultDepthOfFieldSettings

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // iris // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Iris properties for bokeh simulation.
-- |
-- | Controls the shape and appearance of out-of-focus highlights.
newtype IrisProperties = IrisProperties
  { shape            :: Number  -- ^ 0-10 (pentagon to circle)
  , rotation         :: Number  -- ^ Rotation in degrees
  , roundness        :: Number  -- ^ 0-1 roundness
  , aspectRatio      :: Number  -- ^ 0.5-2 aspect ratio
  , diffractionFringe :: Number -- ^ 0-1 diffraction amount
  }

derive instance eqIrisProperties :: Eq IrisProperties

instance showIrisProperties :: Show IrisProperties where
  show (IrisProperties i) =
    "(Iris shape:" <> show i.shape
    <> " rotation:" <> show i.rotation <> "deg)"

-- | Create iris properties with validation.
mkIrisProperties
  :: { shape            :: Number
     , rotation         :: Number
     , roundness        :: Number
     , aspectRatio      :: Number
     , diffractionFringe :: Number
     }
  -> IrisProperties
mkIrisProperties cfg = IrisProperties
  { shape: clampNumber 0.0 10.0 cfg.shape
  , rotation: cfg.rotation  -- No bounds, can rotate freely
  , roundness: clampNumber 0.0 1.0 cfg.roundness
  , aspectRatio: clampNumber 0.5 2.0 cfg.aspectRatio
  , diffractionFringe: clampNumber 0.0 1.0 cfg.diffractionFringe
  }

-- | Default iris properties.
defaultIrisProperties :: IrisProperties
defaultIrisProperties = IrisProperties
  { shape: 10.0           -- Circular
  , rotation: 0.0
  , roundness: 1.0
  , aspectRatio: 1.0
  , diffractionFringe: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // highlight // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Highlight properties for bokeh.
-- |
-- | Controls the appearance of bright highlights in defocused areas.
newtype HighlightProperties = HighlightProperties
  { gain       :: Number  -- ^ 0-1 highlight gain
  , threshold  :: Number  -- ^ 0-1 threshold
  , saturation :: Number  -- ^ 0-1 color saturation
  }

derive instance eqHighlightProperties :: Eq HighlightProperties

instance showHighlightProperties :: Show HighlightProperties where
  show (HighlightProperties h) =
    "(Highlight gain:" <> show h.gain
    <> " threshold:" <> show h.threshold <> ")"

-- | Create highlight properties with validation.
mkHighlightProperties
  :: { gain       :: Number
     , threshold  :: Number
     , saturation :: Number
     }
  -> HighlightProperties
mkHighlightProperties cfg = HighlightProperties
  { gain: clampNumber 0.0 1.0 cfg.gain
  , threshold: clampNumber 0.0 1.0 cfg.threshold
  , saturation: clampNumber 0.0 1.0 cfg.saturation
  }

-- | Default highlight properties.
defaultHighlightProperties :: HighlightProperties
defaultHighlightProperties = HighlightProperties
  { gain: 0.0
  , threshold: 1.0
  , saturation: 1.0
  }
