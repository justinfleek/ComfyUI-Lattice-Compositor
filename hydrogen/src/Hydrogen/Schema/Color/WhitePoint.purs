-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // color // white-point
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | WhitePoint — Standard illuminant chromaticity coordinates.
-- |
-- | **WHAT IS A WHITE POINT?**
-- | The white point defines what "white" means in a color space.
-- | Different light sources have different spectral distributions,
-- | making "white" appear differently under each.
-- |
-- | **CIE Standard Illuminants:**
-- | - **D50**: Horizon light (5003K) - print/photography standard
-- | - **D55**: Mid-morning/mid-afternoon daylight (5503K)
-- | - **D65**: Noon daylight (6504K) - sRGB, display standard
-- | - **D75**: North sky daylight (7504K) - blue-ish
-- | - **Illuminant A**: Incandescent tungsten (2856K) - warm/orange
-- | - **Illuminant E**: Equal energy (theoretical reference)
-- | - **Illuminant F2**: Cool white fluorescent
-- | - **Illuminant F11**: Narrow-band fluorescent (office lighting)
-- |
-- | **Why white point matters:**
-- | - Color appearance changes under different illuminants
-- | - ICC profiles must specify white point for color matching
-- | - Chromatic adaptation transforms between white points
-- |
-- | **Chromaticity vs. Tristimulus:**
-- | - Chromaticity (x, y): 2D coordinates on CIE diagram (hue + sat)
-- | - Tristimulus (X, Y, Z): 3D color coordinates (includes luminance)

module Hydrogen.Schema.Color.WhitePoint
  ( -- * Types
    WhitePoint
  , Illuminant(..)
  
  -- * Constructors
  , whitePoint
  , whitePointFromXY
  
  -- * Accessors
  , chromaticityX
  , chromaticityY
  , chromaticityZ
  , toXY
  , toXYZ
  , illuminantName
  , colorTemperature
  
  -- * Standard Illuminants
  , d50
  , d55
  , d65
  , d75
  , illuminantA
  , illuminantE
  , illuminantF2
  , illuminantF11
  
  -- * Illuminant Lookup
  , fromIlluminant
  , toIlluminant
  
  -- * Chromatic Adaptation
  , chromaticAdaptationFactor
  , isWarmerThan
  , isCoolerThan
  
  -- * Comparison
  , isEqual
  , isNotEqual
  , isStandardIlluminant
  
  -- * Interpolation
  , lerp
  , midpoint
  , chromaticDistance
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (/=)
  , (||)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // illuminant enum
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard CIE illuminants
data Illuminant
  = D50         -- ^ Horizon light, 5003K (print standard)
  | D55         -- ^ Mid-morning daylight, 5503K
  | D65         -- ^ Noon daylight, 6504K (display standard)
  | D75         -- ^ North sky, 7504K
  | IllumA      -- ^ Incandescent tungsten, 2856K
  | IllumE      -- ^ Equal energy (theoretical)
  | IllumF2     -- ^ Cool white fluorescent
  | IllumF11    -- ^ Narrow-band fluorescent

derive instance eqIlluminant :: Eq Illuminant
derive instance ordIlluminant :: Ord Illuminant

instance showIlluminant :: Show Illuminant where
  show = case _ of
    D50 -> "D50 (Horizon Light, 5003K)"
    D55 -> "D55 (Mid-morning, 5503K)"
    D65 -> "D65 (Noon Daylight, 6504K)"
    D75 -> "D75 (North Sky, 7504K)"
    IllumA -> "Illuminant A (Tungsten, 2856K)"
    IllumE -> "Illuminant E (Equal Energy)"
    IllumF2 -> "Illuminant F2 (Cool White Fluorescent)"
    IllumF11 -> "Illuminant F11 (Narrow-band Fluorescent)"

-- | Get name of illuminant
illuminantName :: Illuminant -> String
illuminantName = case _ of
  D50 -> "D50"
  D55 -> "D55"
  D65 -> "D65"
  D75 -> "D75"
  IllumA -> "A"
  IllumE -> "E"
  IllumF2 -> "F2"
  IllumF11 -> "F11"

-- | Get correlated color temperature (CCT) in Kelvin
colorTemperature :: Illuminant -> Int
colorTemperature = case _ of
  D50 -> 5003
  D55 -> 5503
  D65 -> 6504
  D75 -> 7504
  IllumA -> 2856
  IllumE -> 5454  -- Theoretical
  IllumF2 -> 4230
  IllumF11 -> 4000

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // white point
-- ═════════════════════════════════════════════════════════════════════════════

-- | White point defined by CIE chromaticity coordinates
-- |
-- | x + y + z = 1.0 (z is derived from x and y)
newtype WhitePoint = WhitePoint
  { x :: Number        -- ^ CIE x chromaticity (0.0-1.0)
  , y :: Number        -- ^ CIE y chromaticity (0.0-1.0)
  , illuminant :: Maybe Illuminant  -- ^ Standard illuminant if known
  }

derive instance eqWhitePoint :: Eq WhitePoint
derive instance ordWhitePoint :: Ord WhitePoint

instance showWhitePoint :: Show WhitePoint where
  show (WhitePoint wp) = case wp.illuminant of
    Just illum -> show illum
    Nothing -> "WhitePoint(x=" <> show wp.x <> ", y=" <> show wp.y <> ")"

-- | Create white point from chromaticity coordinates
whitePoint :: Number -> Number -> WhitePoint
whitePoint x y = WhitePoint
  { x: clamp01 x
  , y: clamp01 y
  , illuminant: Nothing
  }

-- | Create white point from x, y coordinates
whitePointFromXY :: { x :: Number, y :: Number } -> WhitePoint
whitePointFromXY coords = whitePoint coords.x coords.y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get x chromaticity
chromaticityX :: WhitePoint -> Number
chromaticityX (WhitePoint wp) = wp.x

-- | Get y chromaticity
chromaticityY :: WhitePoint -> Number
chromaticityY (WhitePoint wp) = wp.y

-- | Get z chromaticity (derived: z = 1 - x - y)
chromaticityZ :: WhitePoint -> Number
chromaticityZ (WhitePoint wp) = 1.0 - wp.x - wp.y

-- | Get chromaticity as xy pair
toXY :: WhitePoint -> { x :: Number, y :: Number }
toXY (WhitePoint wp) = { x: wp.x, y: wp.y }

-- | Convert to tristimulus XYZ (normalized so Y = 1)
-- |
-- | X = x/y, Y = 1, Z = (1-x-y)/y
toXYZ :: WhitePoint -> { x :: Number, y :: Number, z :: Number }
toXYZ (WhitePoint wp) =
  if wp.y == 0.0
    then { x: 0.0, y: 1.0, z: 0.0 }  -- Prevent divide by zero
    else { x: wp.x / wp.y
         , y: 1.0
         , z: (1.0 - wp.x - wp.y) / wp.y
         }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // standard illuminants
-- ═════════════════════════════════════════════════════════════════════════════

-- | D50 - Horizon light (print/photography standard)
-- |
-- | Color temperature: 5003K
-- | Used by: ICC profiles, ProPhoto RGB, printing workflows
d50 :: WhitePoint
d50 = WhitePoint
  { x: 0.34567
  , y: 0.35850
  , illuminant: Just D50
  }

-- | D55 - Mid-morning/mid-afternoon daylight
-- |
-- | Color temperature: 5503K
d55 :: WhitePoint
d55 = WhitePoint
  { x: 0.33242
  , y: 0.34743
  , illuminant: Just D55
  }

-- | D65 - Noon daylight (display standard)
-- |
-- | Color temperature: 6504K
-- | Used by: sRGB, Display P3, Rec.709, Rec.2020
d65 :: WhitePoint
d65 = WhitePoint
  { x: 0.31271
  , y: 0.32902
  , illuminant: Just D65
  }

-- | D75 - North sky daylight
-- |
-- | Color temperature: 7504K
-- | Bluish white, used in some photography contexts
d75 :: WhitePoint
d75 = WhitePoint
  { x: 0.29902
  , y: 0.31485
  , illuminant: Just D75
  }

-- | Illuminant A - Incandescent tungsten
-- |
-- | Color temperature: 2856K
-- | Warm/orange white, used for color rendering tests
illuminantA :: WhitePoint
illuminantA = WhitePoint
  { x: 0.44757
  , y: 0.40745
  , illuminant: Just IllumA
  }

-- | Illuminant E - Equal energy (theoretical reference)
-- |
-- | All wavelengths have equal power
-- | Theoretical reference, not physically achievable
illuminantE :: WhitePoint
illuminantE = WhitePoint
  { x: 0.33333
  , y: 0.33333
  , illuminant: Just IllumE
  }

-- | Illuminant F2 - Cool white fluorescent
-- |
-- | Common office/commercial lighting
illuminantF2 :: WhitePoint
illuminantF2 = WhitePoint
  { x: 0.37208
  , y: 0.37529
  , illuminant: Just IllumF2
  }

-- | Illuminant F11 - Narrow-band fluorescent
-- |
-- | Energy-efficient office lighting
illuminantF11 :: WhitePoint
illuminantF11 = WhitePoint
  { x: 0.38052
  , y: 0.37713
  , illuminant: Just IllumF11
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // illuminant lookup
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get white point for a standard illuminant
fromIlluminant :: Illuminant -> WhitePoint
fromIlluminant = case _ of
  D50 -> d50
  D55 -> d55
  D65 -> d65
  D75 -> d75
  IllumA -> illuminantA
  IllumE -> illuminantE
  IllumF2 -> illuminantF2
  IllumF11 -> illuminantF11

-- | Try to identify a white point as a standard illuminant
-- |
-- | Returns Just Illuminant if chromaticity matches (within tolerance)
toIlluminant :: WhitePoint -> Maybe Illuminant
toIlluminant (WhitePoint wp) =
  if matchesWP wp d50 then Just D50
  else if matchesWP wp d55 then Just D55
  else if matchesWP wp d65 then Just D65
  else if matchesWP wp d75 then Just D75
  else if matchesWP wp illuminantA then Just IllumA
  else if matchesWP wp illuminantE then Just IllumE
  else if matchesWP wp illuminantF2 then Just IllumF2
  else if matchesWP wp illuminantF11 then Just IllumF11
  else Nothing
  where
  tolerance = 0.0001
  matchesWP rec (WhitePoint ref) =
    absNum (rec.x - ref.x) < tolerance &&
    absNum (rec.y - ref.y) < tolerance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // chromatic adaptation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate a simple chromatic adaptation factor between white points
-- |
-- | Returns the ratio of chromaticity values (simplified Bradford-style).
-- | For full chromatic adaptation, use XYZ-based Bradford or CAT02.
chromaticAdaptationFactor :: WhitePoint -> WhitePoint -> { xFactor :: Number, yFactor :: Number }
chromaticAdaptationFactor (WhitePoint src) (WhitePoint dst) =
  { xFactor: if src.x == 0.0 then 1.0 else dst.x / src.x
  , yFactor: if src.y == 0.0 then 1.0 else dst.y / src.y
  }

-- | Check if first white point is warmer (lower CCT) than second
isWarmerThan :: WhitePoint -> WhitePoint -> Boolean
isWarmerThan a b =
  -- Warmer = higher x chromaticity (more red)
  chromaticityX a > chromaticityX b

-- | Check if first white point is cooler (higher CCT) than second
isCoolerThan :: WhitePoint -> WhitePoint -> Boolean
isCoolerThan a b =
  chromaticityX a < chromaticityX b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two white points are equal
isEqual :: WhitePoint -> WhitePoint -> Boolean
isEqual (WhitePoint a) (WhitePoint b) =
  a.x == b.x && a.y == b.y

-- | Check if two white points are not equal
isNotEqual :: WhitePoint -> WhitePoint -> Boolean
isNotEqual (WhitePoint a) (WhitePoint b) =
  a.x /= b.x || a.y /= b.y

-- | Check if white point is a standard illuminant
-- | Returns true if the white point matches any known standard illuminant
isStandardIlluminant :: WhitePoint -> Boolean
isStandardIlluminant wp = isValidChromaticity wp && hasKnownIlluminant wp
  where
  -- Validate chromaticity coordinates are in valid range
  isValidChromaticity :: WhitePoint -> Boolean
  isValidChromaticity w = 
    let x = chromaticityX w
        y = chromaticityY w
    in x >= 0.0 && x <= 1.0 && y >= 0.0 && y <= 1.0
  
  -- Check if white point matches a known illuminant
  hasKnownIlluminant :: WhitePoint -> Boolean
  hasKnownIlluminant w = case toIlluminant w of
    Just _ -> true
    Nothing -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two white points
-- |
-- | `lerp wp1 wp2 0.0` returns wp1
-- | `lerp wp1 wp2 1.0` returns wp2
-- | `lerp wp1 wp2 0.5` returns midpoint
-- |
-- | Useful for smooth transitions between lighting conditions
lerp :: WhitePoint -> WhitePoint -> Number -> WhitePoint
lerp (WhitePoint a) (WhitePoint b) t =
  let t' = clamp01 t
      oneMinusT = 1.0 - t'
  in WhitePoint
    { x: a.x * oneMinusT + b.x * t'
    , y: a.y * oneMinusT + b.y * t'
    , illuminant: Nothing  -- Interpolated points aren't standard illuminants
    }

-- | Calculate the midpoint between two white points
-- |
-- | Equivalent to `lerp wp1 wp2 0.5`
midpoint :: WhitePoint -> WhitePoint -> WhitePoint
midpoint (WhitePoint a) (WhitePoint b) =
  WhitePoint
    { x: (a.x + b.x) * 0.5
    , y: (a.y + b.y) * 0.5
    , illuminant: Nothing
    }

-- | Calculate Euclidean distance between chromaticity coordinates
-- |
-- | Useful for determining how "different" two white points are.
-- | Note: This is geometric distance in xy space, not perceptual distance.
-- | For perceptual difference, use CIELAB ΔE calculations.
chromaticDistance :: WhitePoint -> WhitePoint -> Number
chromaticDistance (WhitePoint a) (WhitePoint b) =
  let dx = a.x - b.x
      dy = a.y - b.y
  in sqrt (dx * dx + dy * dy)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Absolute value for Number
absNum :: Number -> Number
absNum n
  | n < 0.0 = 0.0 - n
  | otherwise = n
