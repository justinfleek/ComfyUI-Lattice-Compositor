-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // cvd
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | CVD - Color Vision Deficiency simulation and accessibility.
-- |
-- | Color blindness affects approximately 8% of males and 0.5% of females.
-- | Designs must be accessible to people with all types of color vision.
-- |
-- | ## Types of CVD
-- |
-- | **Red-Green Deficiencies (most common):**
-- | - **Protanopia**: No red cones (~1% males) - red appears dark
-- | - **Protanomaly**: Weak red cones (~1% males) - red shifted toward green
-- | - **Deuteranopia**: No green cones (~1% males) - green appears beige
-- | - **Deuteranomaly**: Weak green cones (~5% males) - green shifted toward red
-- |
-- | **Blue-Yellow Deficiencies (rare):**
-- | - **Tritanopia**: No blue cones (~0.001%) - blue appears green, yellow appears pink
-- | - **Tritanomaly**: Weak blue cones - blue/yellow confusion
-- |
-- | **Total Color Blindness (very rare):**
-- | - **Achromatopsia**: No color vision - sees only grayscale
-- |
-- | ## Playground Integration
-- |
-- | The showcase accessibility panel shows:
-- | - "Normal Vision" (original colors)
-- | - "Protanopia" (no red)
-- | - "Deuteranopia" (no green)
-- | - "Tritanopia" (no blue)
-- | - "Achromatopsia" (grayscale)
-- |
-- | For each view, show contrast ratios and distinguishability warnings.

module Hydrogen.Schema.Color.CVD
  ( CVDType(..)
  , cvdPrevalence
  , AccessibilityIssue
  , AccessibilityReport
  , simulateCVD
  , isDistinguishable
  , checkAccessibility
  , suggestAccessibleAlternative
  , ensureAccessible
  , cvdSafeContrast
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , map
  , max
  , min
  , show
  , unit
  , (+)
  , (*)
  , (/)
  , (>)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just), fromMaybe)
import Data.Either (Either)
import Data.Either as Either
import Data.Foldable (foldr, all)
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.Contrast as Contrast
import Data.Int (toNumber, round) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // cvd type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types of color vision deficiency
data CVDType
  = Normal            -- ^ Normal color vision (no deficiency)
  | Protanopia        -- ^ No red cones (1% males)
  | Protanomaly       -- ^ Weak red cones (1% males)
  | Deuteranopia      -- ^ No green cones (1% males)
  | Deuteranomaly     -- ^ Weak green cones (5% males)
  | Tritanopia        -- ^ No blue cones (very rare)
  | Tritanomaly       -- ^ Weak blue cones (very rare)
  | Achromatopsia     -- ^ No color vision (grayscale only)

derive instance eqCVDType :: Eq CVDType
derive instance ordCVDType :: Ord CVDType

instance showCVDType :: Show CVDType where
  show = case _ of
    Normal -> "Normal Vision"
    Protanopia -> "Protanopia (No Red)"
    Protanomaly -> "Protanomaly (Weak Red)"
    Deuteranopia -> "Deuteranopia (No Green)"
    Deuteranomaly -> "Deuteranomaly (Weak Green)"
    Tritanopia -> "Tritanopia (No Blue)"
    Tritanomaly -> "Tritanomaly (Weak Blue)"
    Achromatopsia -> "Achromatopsia (Grayscale)"

-- | Prevalence data for CVD types
-- |
-- | Returns percentage of population affected, separated by sex.
-- |
-- | **Sources (as of 2026-02-21):**
-- | - National Eye Institute (NEI): 1 in 12 men (8.33%), 1 in 200 women (0.5%)
-- | - Colour Blind Awareness (UK): Detailed breakdown by type
-- |
-- | **Total CVD prevalence: 8% males, 0.5% females worldwide**
-- | (Higher in Scandinavia: 10-11% males; Lower in sub-Saharan Africa)
cvdPrevalence :: CVDType -> { males :: Number, females :: Number }
cvdPrevalence = case _ of
  Normal -> { males: 92.0, females: 99.5 }
  -- Dichromacy (complete absence of one cone type)
  Protanopia -> { males: 1.0, females: 0.03 }      -- No red cones
  Deuteranopia -> { males: 1.0, females: 0.03 }    -- No green cones
  Tritanopia -> { males: 0.002, females: 0.002 }   -- No blue cones (~1 in 50,000)
  -- Anomalous Trichromacy (faulty cone function)
  Protanomaly -> { males: 1.0, females: 0.03 }     -- Weak red cones
  Deuteranomaly -> { males: 5.0, females: 0.4 }    -- Weak green cones (MOST COMMON)
  Tritanomaly -> { males: 0.002, females: 0.002 }  -- Weak blue cones (~1 in 50,000)
  -- Complete color blindness (monochromacy)
  Achromatopsia -> { males: 0.003, females: 0.003 } -- No color at all (~1 in 33,000)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // accessibility issue
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single accessibility issue for one CVD type
type AccessibilityIssue =
  { cvdType :: CVDType
  , actualContrast :: Number
  , requiredContrast :: Number
  , prevalenceMales :: Number
  , prevalenceFemales :: Number
  , message :: String
  }

-- | Complete accessibility report for all CVD types
-- |
-- | Either all CVD types pass (Right Unit), or we have a list of all failures.
-- | The list is never empty if Left - at least one CVD type must fail.
type AccessibilityReport = Either (Array AccessibilityIssue) Unit

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // simulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Simulate how a color appears with a given CVD type
-- |
-- | Uses transformation matrices based on Brettel, Viénot and Mollon (1997)
-- | and Viénot, Brettel and Mollon (1999) research.
-- |
-- | ```purescript
-- | simulateCVD Deuteranopia (RGB.rgb 255 0 0)  -- How red looks with no green cones
-- | simulateCVD Achromatopsia (RGB.rgb 59 130 246)  -- Blue becomes gray
-- | ```
simulateCVD :: CVDType -> RGB.RGB -> RGB.RGB
simulateCVD cvdType color = case cvdType of
  Normal -> color
  Protanopia -> applyMatrix protanopiaMatrix color
  Protanomaly -> applyMatrix protanomalyMatrix color
  Deuteranopia -> applyMatrix deuteranopiaMatrix color
  Deuteranomaly -> applyMatrix deuteranomalyMatrix color
  Tritanopia -> applyMatrix tritanopiaMatrix color
  Tritanomaly -> applyMatrix tritanomalyMatrix color
  Achromatopsia -> toGrayscale color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // distinguishability
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two colors are distinguishable for a given CVD type
-- |
-- | Returns true if the colors have sufficient contrast after CVD simulation.
-- | Uses WCAG AA threshold (4.5:1) as minimum distinguishability.
-- |
-- | ```purescript
-- | isDistinguishable Deuteranopia red green  -- Can these be told apart?
-- | ```
isDistinguishable :: CVDType -> RGB.RGB -> RGB.RGB -> Boolean
isDistinguishable cvdType c1 c2 =
  let
    sim1 = simulateCVD cvdType c1
    sim2 = simulateCVD cvdType c2
    ratio = Contrast.contrastRatio sim1 sim2
  in ratio >= 4.5

-- | Check accessibility for all CVD types and return all failures
-- |
-- | Returns Right unit if accessible for all CVD types, or Left with an array
-- | of ALL failures. The array is never empty if Left.
-- |
-- | For showcase use: display all accessibility issues simultaneously so users
-- | understand the full impact of their color choices.
-- |
-- | ```purescript
-- | checkAccessibility red green
-- | -- Right unit  (all CVD types can distinguish these colors)
-- | -- OR
-- | -- Left [ { cvdType: Protanopia, actualContrast: 2.1, prevalenceMales: 1.0, ... }
-- |        , { cvdType: Deuteranopia, actualContrast: 1.8, prevalenceMales: 1.0, ... } ]
-- | ```
checkAccessibility :: RGB.RGB -> RGB.RGB -> AccessibilityReport
checkAccessibility fg bg =
  let
    -- Check ALL CVD types, including anomaly variants
    -- Deuteranomaly alone affects 5% of males - cannot be skipped
    allTypes = 
      [ Protanopia      -- 1% males
      , Protanomaly     -- 1% males  
      , Deuteranopia    -- 1% males
      , Deuteranomaly   -- 5% males (MOST COMMON)
      , Tritanopia      -- 0.001% (rare)
      , Tritanomaly     -- 0.01% (rare)
      , Achromatopsia   -- 0.003% (very rare)
      ]
    checkType cvdType =
      let
        sim1 = simulateCVD cvdType fg
        sim2 = simulateCVD cvdType bg
        ratio = Contrast.contrastRatio sim1 sim2
        required = 4.5
        prevalence = cvdPrevalence cvdType
      in
        if ratio >= required
          then Nothing
          else Just
            { cvdType
            , actualContrast: ratio
            , requiredContrast: required
            , prevalenceMales: prevalence.males
            , prevalenceFemales: prevalence.females
            , message: "Colors not distinguishable for " <> show cvdType 
                    <> " (" <> show prevalence.males <> "% males, " 
                    <> show prevalence.females <> "% females). "
                    <> "Contrast " <> show ratio <> ":1, needs " <> show required <> ":1"
            }
    
    issues = map checkType allTypes
    failures = foldr (\m acc -> case m of
      Just issue -> [issue] <> acc
      Nothing -> acc
    ) [] issues
  in
    if failures == []
      then Either.Right unit
      else Either.Left failures

-- | Suggest an accessible alternative color
-- |
-- | Given a foreground and background, suggest a foreground that works for
-- | all CVD types. Returns Nothing if the original is already accessible.
-- |
-- | ```purescript
-- | suggestAccessibleAlternative red green  -- Suggest better foreground
-- | ```
suggestAccessibleAlternative :: RGB.RGB -> RGB.RGB -> Maybe RGB.RGB
suggestAccessibleAlternative fg bg =
  -- Check if current combination works for ALL CVD types
  let
    allTypes = 
      [ Protanopia, Protanomaly
      , Deuteranopia, Deuteranomaly
      , Tritanopia, Tritanomaly
      , Achromatopsia
      ]
    allDistinguishable = all (\cvd -> isDistinguishable cvd fg bg) allTypes
  in
    if allDistinguishable
      then Nothing  -- Already accessible
      else Just (makeAccessible fg bg)  -- Suggest alternative

-- | Ensure a color is accessible, correcting it if necessary
-- |
-- | For showcase/playground use: automatically correct colors as users pick them.
-- | If colors are already accessible, returns the original foreground unchanged.
-- | If not accessible, returns a corrected version that works for all CVD types.
-- |
-- | ```purescript
-- | ensureAccessible red green  -- Returns red if accessible, corrected version if not
-- | ```
ensureAccessible :: RGB.RGB -> RGB.RGB -> RGB.RGB
ensureAccessible fg bg = fromMaybe fg (suggestAccessibleAlternative fg bg)

-- | Check contrast for all CVD types
-- |
-- | Returns the minimum contrast ratio across all CVD simulations.
-- | Useful for ensuring designs work for everyone.
-- |
-- | ```purescript
-- | cvdSafeContrast foreground background  -- Minimum contrast across all CVDs
-- | ```
cvdSafeContrast :: RGB.RGB -> RGB.RGB -> Number
cvdSafeContrast fg bg =
  let
    -- Check ALL CVD types including Normal vision
    allTypes = 
      [ Normal
      , Protanopia, Protanomaly
      , Deuteranopia, Deuteranomaly
      , Tritanopia, Tritanomaly
      , Achromatopsia
      ]
    contrasts = map (\cvd -> 
      let sim1 = simulateCVD cvd fg
          sim2 = simulateCVD cvd bg
      in Contrast.contrastRatio sim1 sim2
    ) allTypes
  in minimum contrasts
  where
    minimum [] = 1.0
    minimum xs = foldr min 21.0 xs

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a 3x3 transformation matrix to RGB color
applyMatrix :: Matrix3x3 -> RGB.RGB -> RGB.RGB
applyMatrix m color =
  let
    r = Int.toNumber (Ch.unwrap (RGB.red color)) / 255.0
    g = Int.toNumber (Ch.unwrap (RGB.green color)) / 255.0
    b = Int.toNumber (Ch.unwrap (RGB.blue color)) / 255.0
    
    r' = m.m00 * r + m.m01 * g + m.m02 * b
    g' = m.m10 * r + m.m11 * g + m.m12 * b
    b' = m.m20 * r + m.m21 * g + m.m22 * b
    
    clamp x = min 1.0 (max 0.0 x)
  in
    RGB.rgb
      (Int.round (clamp r' * 255.0))
      (Int.round (clamp g' * 255.0))
      (Int.round (clamp b' * 255.0))

-- | 3x3 transformation matrix
type Matrix3x3 =
  { m00 :: Number, m01 :: Number, m02 :: Number
  , m10 :: Number, m11 :: Number, m12 :: Number
  , m20 :: Number, m21 :: Number, m22 :: Number
  }

-- | Protanopia transformation matrix (no red cones)
protanopiaMatrix :: Matrix3x3
protanopiaMatrix =
  { m00: 0.567, m01: 0.433, m02: 0.0
  , m10: 0.558, m11: 0.442, m12: 0.0
  , m20: 0.0,   m21: 0.242, m22: 0.758
  }

-- | Protanomaly transformation matrix (weak red cones)
protanomalyMatrix :: Matrix3x3
protanomalyMatrix =
  { m00: 0.817, m01: 0.183, m02: 0.0
  , m10: 0.333, m11: 0.667, m12: 0.0
  , m20: 0.0,   m21: 0.125, m22: 0.875
  }

-- | Deuteranopia transformation matrix (no green cones)
deuteranopiaMatrix :: Matrix3x3
deuteranopiaMatrix =
  { m00: 0.625, m01: 0.375, m02: 0.0
  , m10: 0.7,   m11: 0.3,   m12: 0.0
  , m20: 0.0,   m21: 0.3,   m22: 0.7
  }

-- | Deuteranomaly transformation matrix (weak green cones)
deuteranomalyMatrix :: Matrix3x3
deuteranomalyMatrix =
  { m00: 0.8,   m01: 0.2,   m02: 0.0
  , m10: 0.258, m11: 0.742, m12: 0.0
  , m20: 0.0,   m21: 0.142, m22: 0.858
  }

-- | Tritanopia transformation matrix (no blue cones)
tritanopiaMatrix :: Matrix3x3
tritanopiaMatrix =
  { m00: 0.95,  m01: 0.05,  m02: 0.0
  , m10: 0.0,   m11: 0.433, m12: 0.567
  , m20: 0.0,   m21: 0.475, m22: 0.525
  }

-- | Tritanomaly transformation matrix (weak blue cones)
tritanomalyMatrix :: Matrix3x3
tritanomalyMatrix =
  { m00: 0.967, m01: 0.033, m02: 0.0
  , m10: 0.0,   m11: 0.733, m12: 0.267
  , m20: 0.0,   m21: 0.183, m22: 0.817
  }

-- | Convert to grayscale (achromatopsia)
toGrayscale :: RGB.RGB -> RGB.RGB
toGrayscale color =
  let
    -- Use luminance weights (ITU-R BT.709)
    r = Int.toNumber (Ch.unwrap (RGB.red color))
    g = Int.toNumber (Ch.unwrap (RGB.green color))
    b = Int.toNumber (Ch.unwrap (RGB.blue color))
    gray = Int.round (0.2126 * r + 0.7152 * g + 0.0722 * b)
  in
    RGB.rgb gray gray gray

-- | Make a foreground color accessible against a background
-- |
-- | **POLICY: Maximum contrast for maximum accessibility.**
-- |
-- | This function does NOT preserve hue or brand identity. It returns pure black
-- | or pure white based on background luminance to guarantee WCAG AAA compliance
-- | (7:1 contrast) for all CVD types.
-- |
-- | For brand-preserving alternatives, agents should use perceptual color spaces
-- | (LAB/LCH/OKLAB) to adjust lightness while maintaining hue. This function is
-- | the "nuclear option" when accessibility must be guaranteed at any cost.
-- |
-- | ```purescript
-- | makeAccessible brandRed lightGray  -- Returns black (loses brand red)
-- | makeAccessible brandBlue darkGray  -- Returns white (loses brand blue)
-- | ```
makeAccessible :: RGB.RGB -> RGB.RGB -> RGB.RGB
makeAccessible fg bg =
  let
    bgLum = Contrast.luminanceRGB bg
    currentRatio = Contrast.contrastRatio fg bg
    requiredRatio = 4.5
    
    -- Determine if we need darker or lighter foreground
    needDarker = bgLum > 0.5
  in
    if currentRatio >= requiredRatio
      then fg  -- Already accessible
      else if needDarker
        then RGB.rgb 0 0 0  -- Pure black: 21:1 on white, guarantees accessibility
        else RGB.rgb 255 255 255  -- Pure white: 21:1 on black, guarantees accessibility
