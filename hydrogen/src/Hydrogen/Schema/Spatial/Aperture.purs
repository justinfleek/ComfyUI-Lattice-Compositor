-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // spatial // aperture
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Aperture Atom — Camera f-stop value.
-- |
-- | Range: 0.5 to 128 (clamps)
-- | - **f/1.4**: Very wide, shallow depth of field, lots of light
-- | - **f/2.8**: Wide, portraits with bokeh
-- | - **f/5.6**: Medium, general photography
-- | - **f/11**: Narrow, landscapes with deep focus
-- | - **f/22**: Very narrow, maximum depth of field
-- |
-- | Lower f-number = wider aperture = more light = shallower DOF.
-- | Higher f-number = narrower aperture = less light = deeper DOF.

module Hydrogen.Schema.Spatial.Aperture
  ( Aperture
  , aperture
  , unwrapAperture
  , bounds
  
  -- * Common Values
  , f1_4
  , f2
  , f2_8
  , f4
  , f5_6
  , f8
  , f11
  , f16
  , f22
  
  -- * Operations
  , apertureStops
  , apertureToRadius
  ) where

import Prelude

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // aperture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Camera aperture (f-stop)
-- |
-- | Clamped to 0.5-128 range.
newtype Aperture = Aperture Number

derive instance eqAperture :: Eq Aperture
derive instance ordAperture :: Ord Aperture

instance showAperture :: Show Aperture where
  show (Aperture f) = "f/" <> show f

-- | Create an aperture value (clamped to valid range)
aperture :: Number -> Aperture
aperture n = Aperture (Bounded.clampNumber 0.5 128.0 n)

-- | Extract f-stop value
unwrapAperture :: Aperture -> Number
unwrapAperture (Aperture f) = f

-- | Bounds documentation
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.5 128.0 "Aperture"
  "Camera f-stop (0.5-128)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common values
-- ═════════════════════════════════════════════════════════════════════════════

-- | f/1.4 — Very wide aperture
f1_4 :: Aperture
f1_4 = Aperture 1.4

-- | f/2 — Wide aperture
f2 :: Aperture
f2 = Aperture 2.0

-- | f/2.8 — Portrait aperture
f2_8 :: Aperture
f2_8 = Aperture 2.8

-- | f/4 — General wide
f4 :: Aperture
f4 = Aperture 4.0

-- | f/5.6 — General medium
f5_6 :: Aperture
f5_6 = Aperture 5.6

-- | f/8 — Sharp, good DOF
f8 :: Aperture
f8 = Aperture 8.0

-- | f/11 — Landscape
f11 :: Aperture
f11 = Aperture 11.0

-- | f/16 — Deep focus
f16 :: Aperture
f16 = Aperture 16.0

-- | f/22 — Maximum DOF
f22 :: Aperture
f22 = Aperture 22.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate stops difference between two apertures
-- |
-- | Each stop is sqrt(2) ≈ 1.414x change in f-number.
-- | Positive = a2 is smaller (more light).
apertureStops :: Aperture -> Aperture -> Number
apertureStops (Aperture fstop1) (Aperture fstop2) =
  let logBase2 x = Math.log x / Math.log 2.0
  in 2.0 * (logBase2 fstop1 - logBase2 fstop2)

-- | Convert aperture to entrance pupil radius
-- |
-- | Given focal length, returns physical aperture radius.
-- | radius = focalLength / (2 * f-number)
apertureToRadius :: Number -> Aperture -> Number
apertureToRadius focalLength (Aperture f) =
  focalLength / (2.0 * f)
