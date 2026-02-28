-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // elevation // depth-of-field
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Depth of Field atoms — simulated camera focus effects.
-- |
-- | ## Photographic Model
-- |
-- | Depth of field simulates how real cameras focus:
-- |
-- | - **Focal distance**: Distance at which objects are in sharp focus
-- | - **Aperture (f-stop)**: Size of lens opening. Lower = shallower DoF
-- | - **Bokeh radius**: Blur radius for out-of-focus areas
-- |
-- | ## CSS Implementation
-- |
-- | CSS doesn't natively support depth-of-field. These atoms define the
-- | parameters that can be rendered via:
-- |
-- | - CSS `filter: blur()` on individual elements
-- | - WebGL post-processing shaders
-- | - Canvas 2D composition with blur
-- | - SVG filters with `feGaussianBlur`
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Elevation.DepthOfField as DoF
-- |
-- | -- Define focus parameters
-- | config :: DoF.DepthOfFieldConfig
-- | config = DoF.depthOfFieldConfig
-- |   { focalDistance: DoF.focalDistance 500.0
-- |   , aperture: DoF.aperture 2.8
-- |   , bokehRadius: DoF.bokehRadius 8.0
-- |   }
-- |
-- | -- Calculate blur for an element at a given distance
-- | blurAmount = DoF.blurAtDistance config 800.0  -- returns blur radius
-- | ```

module Hydrogen.Schema.Elevation.DepthOfField
  ( -- * Focal Distance (Atom)
    FocalDistance
  , focalDistance
  , getFocalDistance
  , infiniteFocus
  , closeFocus
  
  -- * Aperture (Atom)
  , Aperture
  , aperture
  , getAperture
  , wideAperture
  , narrowAperture
  , standardAperture
  
  -- * Bokeh Radius (Atom)
  , BokehRadius
  , bokehRadius
  , getBokehRadius
  , noBokeh
  , subtleBokeh
  , dramaticBokeh
  
  -- * Depth of Field Config (Molecule)
  , DepthOfFieldConfig
  , depthOfFieldConfig
  , defaultConfig
  , getFocalDistanceFromConfig
  , getApertureFromConfig
  , getBokehRadiusFromConfig
  , withFocalDistance
  , withAperture
  , withBokehRadius
  
  -- * Calculations
  , blurAtDistance
  , isInFocus
  , focusRangeFront
  , focusRangeBack
  , focusRangeWidth
  , isWithinFocusRange
  
  -- * Comparisons
  , compareFocalDistance
  , compareAperture
  , compareBokehRadius
  , shallowerDoF
  , deeperDoF
  
  -- * Operations
  , scaleFocalDistance
  , scaleAperture
  , scaleBokehRadius
  , stopDown
  , stopUp
  
  -- * Predicates
  , hasDepthOfField
  , isShallowDoF
  , isDeepDoF
  , isMacroFocus
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , negate
  , Ordering(LT, GT, EQ)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , (&&)
  , (||)
  , (<>)
  , ($)
  , max
  , min
  )

import Data.Number (abs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // focal distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focal distance in pixels (or arbitrary units).
-- |
-- | Represents the distance from the camera to the focal plane — where
-- | objects appear sharpest. Objects closer or farther will be blurred.
-- |
-- | Values are clamped to >= 0 (negative distance is meaningless).
newtype FocalDistance = FocalDistance Number

derive instance eqFocalDistance :: Eq FocalDistance
derive instance ordFocalDistance :: Ord FocalDistance

instance showFocalDistance :: Show FocalDistance where
  show (FocalDistance n) = "FocalDistance " <> show n

-- | Create a focal distance
-- |
-- | Value clamped to >= 0.
focalDistance :: Number -> FocalDistance
focalDistance n = FocalDistance (clampNonNegative n)

-- | Extract the focal distance value
getFocalDistance :: FocalDistance -> Number
getFocalDistance (FocalDistance n) = n

-- | Infinite focus — everything in focus (no DoF effect)
-- |
-- | Represented by a very large distance where DoF effects are negligible.
infiniteFocus :: FocalDistance
infiniteFocus = FocalDistance 10000.0

-- | Close focus — shallow depth of field
-- |
-- | Focus on nearby elements, dramatic background blur.
closeFocus :: FocalDistance
closeFocus = FocalDistance 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // aperture
-- ═════════════════════════════════════════════════════════════════════════════

-- | Aperture (f-stop) value.
-- |
-- | Controls depth of field shallowness:
-- | - Lower values (f/1.4, f/2.8): Shallow DoF, more blur
-- | - Higher values (f/11, f/16): Deep DoF, more in focus
-- |
-- | Standard f-stop scale: 1.4, 2, 2.8, 4, 5.6, 8, 11, 16, 22
-- |
-- | Values clamped to >= 1.0 (f/1.0 is the physical minimum).
newtype Aperture = Aperture Number

derive instance eqAperture :: Eq Aperture
derive instance ordAperture :: Ord Aperture

instance showAperture :: Show Aperture where
  show (Aperture n) = "f/" <> show n

-- | Create an aperture value
-- |
-- | Value clamped to >= 1.0.
aperture :: Number -> Aperture
aperture n = Aperture (max 1.0 n)

-- | Extract the aperture f-stop value
getAperture :: Aperture -> Number
getAperture (Aperture n) = n

-- | Wide aperture (f/1.4) — very shallow DoF
wideAperture :: Aperture
wideAperture = Aperture 1.4

-- | Narrow aperture (f/16) — deep DoF, most in focus
narrowAperture :: Aperture
narrowAperture = Aperture 16.0

-- | Standard aperture (f/5.6) — balanced DoF
standardAperture :: Aperture
standardAperture = Aperture 5.6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // bokeh radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | Maximum bokeh (blur) radius in pixels.
-- |
-- | This is the maximum blur radius applied to out-of-focus elements.
-- | The actual blur scales with distance from focal plane.
-- |
-- | Values clamped to >= 0.
newtype BokehRadius = BokehRadius Number

derive instance eqBokehRadius :: Eq BokehRadius
derive instance ordBokehRadius :: Ord BokehRadius

instance showBokehRadius :: Show BokehRadius where
  show (BokehRadius n) = "BokehRadius " <> show n

-- | Create a bokeh radius
-- |
-- | Value clamped to >= 0.
bokehRadius :: Number -> BokehRadius
bokehRadius n = BokehRadius (clampNonNegative n)

-- | Extract the bokeh radius value
getBokehRadius :: BokehRadius -> Number
getBokehRadius (BokehRadius n) = n

-- | No bokeh (no DoF blur effect)
noBokeh :: BokehRadius
noBokeh = BokehRadius 0.0

-- | Subtle bokeh (4px max blur)
subtleBokeh :: BokehRadius
subtleBokeh = BokehRadius 4.0

-- | Dramatic bokeh (16px max blur)
dramaticBokeh :: BokehRadius
dramaticBokeh = BokehRadius 16.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // depth of field config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete depth of field configuration.
-- |
-- | Combines focal distance, aperture, and bokeh radius into a single
-- | configuration for calculating element blur based on z-position.
type DepthOfFieldConfig =
  { focalDistance :: FocalDistance
  , aperture :: Aperture
  , bokehRadius :: BokehRadius
  }

-- | Create a depth of field configuration
depthOfFieldConfig :: 
  { focalDistance :: FocalDistance
  , aperture :: Aperture
  , bokehRadius :: BokehRadius
  } -> DepthOfFieldConfig
depthOfFieldConfig = identity

-- | Default configuration: medium focus, standard aperture, subtle bokeh
defaultConfig :: DepthOfFieldConfig
defaultConfig =
  { focalDistance: focalDistance 500.0
  , aperture: standardAperture
  , bokehRadius: subtleBokeh
  }

-- | Get focal distance from config
getFocalDistanceFromConfig :: DepthOfFieldConfig -> FocalDistance
getFocalDistanceFromConfig c = c.focalDistance

-- | Get aperture from config
getApertureFromConfig :: DepthOfFieldConfig -> Aperture
getApertureFromConfig c = c.aperture

-- | Get bokeh radius from config
getBokehRadiusFromConfig :: DepthOfFieldConfig -> BokehRadius
getBokehRadiusFromConfig c = c.bokehRadius

-- | Update focal distance in config
withFocalDistance :: FocalDistance -> DepthOfFieldConfig -> DepthOfFieldConfig
withFocalDistance fd c = c { focalDistance = fd }

-- | Update aperture in config
withAperture :: Aperture -> DepthOfFieldConfig -> DepthOfFieldConfig
withAperture a c = c { aperture = a }

-- | Update bokeh radius in config
withBokehRadius :: BokehRadius -> DepthOfFieldConfig -> DepthOfFieldConfig
withBokehRadius br c = c { bokehRadius = br }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate blur radius for an element at a given distance.
-- |
-- | Blur increases with:
-- | - Distance from focal plane
-- | - Lower aperture values (wider opening)
-- |
-- | Blur decreases with:
-- | - Closer to focal plane
-- | - Higher aperture values (narrower opening)
-- |
-- | Returns a value from 0 (in focus) to bokehRadius (max blur).
blurAtDistance :: DepthOfFieldConfig -> Number -> Number
blurAtDistance config elementDistance =
  let
    FocalDistance focal = config.focalDistance
    Aperture f = config.aperture
    BokehRadius maxBlur = config.bokehRadius
    
    -- Distance from focal plane
    distFromFocal = abs (elementDistance - focal)
    
    -- Simplified circle of confusion calculation
    -- Real formula involves sensor size, focal length, etc.
    -- This is a practical approximation for UI purposes
    -- Lower f-stop = more blur per unit distance
    blurFactor = (1.0 / f) * 0.5
    rawBlur = distFromFocal * blurFactor
  in
    min maxBlur rawBlur

-- | Check if an element at a given distance is in focus.
-- |
-- | "In focus" means blur radius is below a perceptual threshold (0.5px).
isInFocus :: DepthOfFieldConfig -> Number -> Boolean
isInFocus config distance = blurAtDistance config distance < 0.5

-- | Calculate front edge of focus range.
-- |
-- | Returns the nearest distance that is still in focus.
focusRangeFront :: DepthOfFieldConfig -> Number
focusRangeFront config =
  let
    FocalDistance focal = config.focalDistance
    Aperture f = config.aperture
    -- Approximate: higher f-stop = deeper focus range
    range = f * 20.0
  in
    max 0.0 (focal - range)

-- | Calculate back edge of focus range.
-- |
-- | Returns the farthest distance that is still in focus.
focusRangeBack :: DepthOfFieldConfig -> Number
focusRangeBack config =
  let
    FocalDistance focal = config.focalDistance
    Aperture f = config.aperture
    range = f * 20.0
  in
    focal + range

-- | Calculate the total width of the focus range.
-- |
-- | This is the depth of the "in focus" zone.
focusRangeWidth :: DepthOfFieldConfig -> Number
focusRangeWidth config =
  focusRangeBack config - focusRangeFront config

-- | Check if a distance falls within the focus range.
-- |
-- | More efficient than checking blurAtDistance < threshold for
-- | multiple distances against the same config.
isWithinFocusRange :: DepthOfFieldConfig -> Number -> Boolean
isWithinFocusRange config distance =
  distance >= focusRangeFront config && distance <= focusRangeBack config

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // comparisons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare two focal distances.
compareFocalDistance :: FocalDistance -> FocalDistance -> Ordering
compareFocalDistance (FocalDistance a) (FocalDistance b) = compare a b

-- | Compare two apertures.
-- |
-- | Lower f-stop values are "larger" apertures (more light, shallower DoF).
-- | This comparison is by f-number, so f/1.4 < f/2.8 < f/16.
compareAperture :: Aperture -> Aperture -> Ordering
compareAperture (Aperture a) (Aperture b) = compare a b

-- | Compare two bokeh radii.
compareBokehRadius :: BokehRadius -> BokehRadius -> Ordering
compareBokehRadius (BokehRadius a) (BokehRadius b) = compare a b

-- | Determine which of two configs produces shallower depth of field.
-- |
-- | Returns LT if first is shallower, GT if second is shallower, EQ if equal.
-- | Shallower DoF = lower f-stop (wider aperture).
shallowerDoF :: DepthOfFieldConfig -> DepthOfFieldConfig -> Ordering
shallowerDoF a b =
  let
    Aperture fA = a.aperture
    Aperture fB = b.aperture
  in
    -- Lower f-stop = shallower DoF, so we reverse the comparison
    compare fB fA

-- | Determine which of two configs produces deeper depth of field.
-- |
-- | Returns LT if first is deeper, GT if second is deeper, EQ if equal.
deeperDoF :: DepthOfFieldConfig -> DepthOfFieldConfig -> Ordering
deeperDoF a b =
  let
    Aperture fA = a.aperture
    Aperture fB = b.aperture
  in
    compare fA fB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale a focal distance by a factor.
-- |
-- | Useful for responsive adjustments or animation.
scaleFocalDistance :: Number -> FocalDistance -> FocalDistance
scaleFocalDistance factor (FocalDistance d) =
  focalDistance (d * factor)

-- | Scale an aperture by a factor.
-- |
-- | Note: Doubling f-stop halves the light (one stop).
scaleAperture :: Number -> Aperture -> Aperture
scaleAperture factor (Aperture f) =
  aperture (f * factor)

-- | Scale a bokeh radius by a factor.
scaleBokehRadius :: Number -> BokehRadius -> BokehRadius
scaleBokehRadius factor (BokehRadius r) =
  bokehRadius (r * factor)

-- | "Stop down" — increase f-number by one stop (halve the light).
-- |
-- | Standard stops: 1.4 -> 2 -> 2.8 -> 4 -> 5.6 -> 8 -> 11 -> 16 -> 22
-- | This multiplies by approximately 1.414 (sqrt(2)).
stopDown :: Aperture -> Aperture
stopDown (Aperture f) = Aperture (f * 1.414)

-- | "Stop up" — decrease f-number by one stop (double the light).
-- |
-- | This divides by approximately 1.414 (sqrt(2)).
-- | Clamped to minimum f/1.0.
stopUp :: Aperture -> Aperture
stopUp (Aperture f) = aperture (f / 1.414)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if depth of field is enabled (non-zero bokeh radius)
hasDepthOfField :: DepthOfFieldConfig -> Boolean
hasDepthOfField config = 
  let BokehRadius r = config.bokehRadius
  in r > 0.0

-- | Check if DoF is shallow (wide aperture, f/4 or lower)
isShallowDoF :: DepthOfFieldConfig -> Boolean
isShallowDoF config =
  let Aperture f = config.aperture
  in f <= 4.0 && hasDepthOfField config

-- | Check if DoF is deep (narrow aperture, f/11 or higher)
isDeepDoF :: DepthOfFieldConfig -> Boolean
isDeepDoF config =
  let Aperture f = config.aperture
  in f >= 11.0 || (hasDepthOfField config == false)

-- | Check if focus is set for macro/close-up photography.
-- |
-- | Macro focus typically means focal distance under 200 units.
isMacroFocus :: DepthOfFieldConfig -> Boolean
isMacroFocus config =
  let FocalDistance d = config.focalDistance
  in d < 200.0 && d > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identity function
identity :: forall a. a -> a
identity x = x

-- | Clamp to non-negative
clampNonNegative :: Number -> Number
clampNonNegative n = if n < 0.0 then 0.0 else n
