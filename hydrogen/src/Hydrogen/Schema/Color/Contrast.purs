-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // color // contrast
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color contrast and accessibility.
-- |
-- | WCAG (Web Content Accessibility Guidelines) contrast requirements:
-- | - **AA Large**: 3:1 minimum for large text (18pt+ or 14pt bold)
-- | - **AA**: 4.5:1 minimum for normal text
-- | - **AAA**: 7:1 minimum for enhanced accessibility
-- |
-- | This module provides accurate contrast calculation per WCAG 2.1 spec.

module Hydrogen.Schema.Color.Contrast
  ( -- * WCAG Levels
    WCAGLevel(..)
  
  -- * Contrast Calculation
  , Contrast
  , contrastRatio
  , contrastBetween
  
  -- * Accessibility Checks
  , meetsWCAG
  , suggestForeground
  
  -- * Luminance
  , luminanceRGB
  , relativeLuminance
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (+)
  , (*)
  , (/)
  , (>)
  , (>=)
  , (<=)
  )

import Data.Int (toNumber)
import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Ch

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // wcag levels
-- ═════════════════════════════════════════════════════════════════════════════

-- | WCAG contrast levels
data WCAGLevel
  = WCAGFail             -- ^ Below 3:1
  | WCAGAA_Large         -- ^ 3:1+ (large text)
  | WCAGAA               -- ^ 4.5:1+ (normal text)
  | WCAGAAA_Large        -- ^ 4.5:1+ (large text enhanced)
  | WCAGAAA              -- ^ 7:1+ (enhanced)

derive instance eqWCAGLevel :: Eq WCAGLevel
derive instance ordWCAGLevel :: Ord WCAGLevel

instance showWCAGLevel :: Show WCAGLevel where
  show = case _ of
    WCAGFail -> "Fail"
    WCAGAA_Large -> "AA (Large Text)"
    WCAGAA -> "AA"
    WCAGAAA_Large -> "AAA (Large Text)"
    WCAGAAA -> "AAA"

-- | Minimum contrast ratios for each level
minContrastFor :: WCAGLevel -> Number
minContrastFor = case _ of
  WCAGFail -> 1.0
  WCAGAA_Large -> 3.0
  WCAGAA -> 4.5
  WCAGAAA_Large -> 4.5
  WCAGAAA -> 7.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // contrast calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contrast information between two colors
type Contrast =
  { ratio :: Number
  , level :: WCAGLevel
  }

-- | Calculate WCAG contrast ratio between two colors
-- |
-- | Returns a value between 1:1 (identical) and 21:1 (black/white)
contrastRatio :: RGB.RGB -> RGB.RGB -> Number
contrastRatio c1 c2 =
  let
    l1 = luminanceRGB c1
    l2 = luminanceRGB c2
    lighter = Math.max l1 l2
    darker = Math.min l1 l2
  in (lighter + 0.05) / (darker + 0.05)

-- | Get full contrast information between two colors
contrastBetween :: RGB.RGB -> RGB.RGB -> Contrast
contrastBetween c1 c2 =
  let 
    ratio = contrastRatio c1 c2
    level = 
      if ratio >= 7.0 then WCAGAAA
      else if ratio >= 4.5 then WCAGAA
      else if ratio >= 3.0 then WCAGAA_Large
      else WCAGFail
  in { ratio, level }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // accessibility checks
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if contrast meets a WCAG level
meetsWCAG :: WCAGLevel -> RGB.RGB -> RGB.RGB -> Boolean
meetsWCAG level c1 c2 = contrastRatio c1 c2 >= minContrastFor level

-- | Suggest black or white foreground for best contrast
suggestForeground :: RGB.RGB -> RGB.RGB
suggestForeground background =
  let
    l = luminanceRGB background
  in if l > 0.179 then RGB.rgb 0 0 0 else RGB.rgb 255 255 255

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // luminance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Relative luminance per WCAG 2.1 specification
-- |
-- | Returns a value between 0 (darkest black) and 1 (lightest white)
luminanceRGB :: RGB.RGB -> Number
luminanceRGB color =
  let 
    r = Ch.unwrap (RGB.red color)
    g = Ch.unwrap (RGB.green color)
    b = Ch.unwrap (RGB.blue color)
    toLinear c = 
      let c' = toNumber c / 255.0
      in if c' <= 0.03928 
         then c' / 12.92 
         else Math.pow ((c' + 0.055) / 1.055) 2.4
  in 0.2126 * toLinear r + 0.7152 * toLinear g + 0.0722 * toLinear b

-- | Alias for luminanceRGB (WCAG terminology)
relativeLuminance :: RGB.RGB -> Number
relativeLuminance = luminanceRGB
