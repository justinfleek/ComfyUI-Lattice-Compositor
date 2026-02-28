-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // typography // optical-size
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OpticalSize - variable font optical size axis.
-- |
-- | Controls automatic adjustments for rendering at different sizes.
-- | At small sizes: thicker strokes, open counters, wider spacing.
-- | At large sizes: finer details, tighter spacing, higher contrast.
-- |
-- | ## CSS Mapping
-- | Maps to `font-optical-sizing` (auto/none) and the 'opsz' variation axis.
-- |
-- | ## Variable Font Axis
-- | The 'opsz' axis in OpenType variable fonts. Value typically matches
-- | the font size in points, but can be set independently for creative effect.
-- |
-- | ## History
-- | Traditional metal type had different designs cut for each size.
-- | 6pt Garamond looked different from 72pt Garamond. Optical sizing
-- | brings this craft back to digital typography.

module Hydrogen.Schema.Typography.OpticalSize
  ( -- * Type
    OpticalSize(..)
    
  -- * Constructors
  , opticalSize
  , auto
  
  -- * Predefined Values
  , caption
  , body
  , subheading
  , heading
  , display
  , poster
  
  -- * Accessors
  , unwrap
  , toLegacyCSSValue
  , toVariationValue
  
  -- * Operations
  , clamp
  , matchFontSize
  
  -- * Bounds
  , bounds
  ) where

import Prelude

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | OpticalSize represents the optical sizing axis value.
-- | Stored as tenths of a point for precision (e.g., 120 = 12.0pt).
-- | Range is typically 6pt to 144pt, but variable fonts may differ.
newtype OpticalSize = OpticalSize Int

derive instance eqOpticalSize :: Eq OpticalSize
derive instance ordOpticalSize :: Ord OpticalSize

instance showOpticalSize :: Show OpticalSize where
  show os = show (toPoints os) <> "pt"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create OpticalSize from points (clamped to 6-144pt range)
opticalSize :: Number -> OpticalSize
opticalSize pt
  | pt < 6.0 = OpticalSize 60
  | pt > 144.0 = OpticalSize 1440
  | otherwise = OpticalSize (Int.round (pt * 10.0))

-- | Auto optical sizing (matches font size) - represented as 0
-- | When rendered, this uses CSS font-optical-sizing: auto
auto :: OpticalSize
auto = OpticalSize 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predefined
-- ═════════════════════════════════════════════════════════════════════════════

-- | Caption size (8pt) - maximum legibility at small sizes
caption :: OpticalSize
caption = OpticalSize 80

-- | Body text size (12pt) - standard reading size
body :: OpticalSize
body = OpticalSize 120

-- | Subheading size (18pt)
subheading :: OpticalSize
subheading = OpticalSize 180

-- | Heading size (24pt)
heading :: OpticalSize
heading = OpticalSize 240

-- | Display size (48pt) - refined details
display :: OpticalSize
display = OpticalSize 480

-- | Poster size (72pt+) - maximum refinement
poster :: OpticalSize
poster = OpticalSize 720

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw tenths-of-point value
unwrap :: OpticalSize -> Int
unwrap (OpticalSize n) = n

-- | Convert to points
toPoints :: OpticalSize -> Number
toPoints (OpticalSize n) = Int.toNumber n / 10.0

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS value string
toLegacyCSSValue :: OpticalSize -> String
toLegacyCSSValue (OpticalSize 0) = "auto"
toLegacyCSSValue os = show (toPoints os)

-- | Convert to variation axis value (for font-variation-settings)
toVariationValue :: OpticalSize -> String
toVariationValue (OpticalSize 0) = "\"opsz\" auto"
toVariationValue os = "\"opsz\" " <> show (toPoints os)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp optical size to valid range (6-144pt)
clamp :: OpticalSize -> OpticalSize
clamp (OpticalSize n)
  | n == 0 = OpticalSize 0  -- preserve auto
  | n < 60 = OpticalSize 60
  | n > 1440 = OpticalSize 1440
  | otherwise = OpticalSize n

-- | Create OpticalSize that matches a font size in pixels
-- | Assumes 96 PPI (CSS reference pixel)
matchFontSize :: Number -> OpticalSize
matchFontSize pixels =
  let points = pixels * 72.0 / 96.0
  in opticalSize points

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds documentation for OpticalSize
-- |
-- | Stored as tenths of a point internally.
-- | Min: 60 (6pt)
-- | Max: 1440 (144pt)
-- | Special: 0 represents "auto"
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 1440 "opticalSize" "Optical size axis (0=auto, or 60-1440 tenths of pt)"
