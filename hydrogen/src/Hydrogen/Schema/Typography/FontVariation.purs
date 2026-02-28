-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // typography // font-variation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FontVariation - OpenType variable font axis settings.
-- |
-- | Variable fonts contain multiple styles along continuous axes.
-- | This module provides type-safe access to standard and custom axes.
-- |
-- | ## Registered Axes (4-letter lowercase tags)
-- | - wght: Weight (same as CSS font-weight)
-- | - wdth: Width (same as CSS font-stretch)
-- | - slnt: Slant (oblique angle in degrees)
-- | - ital: Italic (0 = upright, 1 = italic)
-- | - opsz: Optical size (matches font size in points)
-- |
-- | ## Custom Axes (4-letter uppercase tags)
-- | - GRAD: Grade (weight without metric change)
-- | - CASL: Casual (0 = formal, 1 = casual)
-- | - CRSV: Cursive (0 = upright, 1 = cursive)
-- | - MONO: Monospace (0 = proportional, 1 = monospace)
-- | - FILL: Fill (0 = outline, 1 = filled)
-- | - SOFT: Softness (corner rounding)
-- | - WONK: Wonky (0 = normalized, 1 = wonky)
-- |
-- | ## CSS Mapping
-- | Maps to `font-variation-settings` property.

module Hydrogen.Schema.Typography.FontVariation
  ( -- * Types
    VariationAxis(..)
  , AxisValue(..)
  , FontVariation(..)
  
  -- * Axis Constructors
  , weight
  , width
  , slant
  , italic
  , opticalSize
  , grade
  , casual
  , cursive
  , monospace
  , fill
  , softness
  , wonky
  , customAxis
  
  -- * FontVariation Constructors
  , fontVariation
  , single
  , empty
  
  -- * Operations
  , addAxis
  , setAxis
  , removeAxis
  , getAxis
  , merge
  
  -- * CSS Output
  , toLegacyCSSValue
  , toStyleAttribute
  ) where

import Prelude

import Data.Array (filter, snoc, find, uncons) as Array
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A variation axis identified by its 4-character tag
newtype VariationAxis = VariationAxis String

derive instance eqVariationAxis :: Eq VariationAxis
derive instance ordVariationAxis :: Ord VariationAxis

instance showVariationAxis :: Show VariationAxis where
  show (VariationAxis tag) = "\"" <> tag <> "\""

-- | An axis value (Number for continuous axes)
newtype AxisValue = AxisValue Number

derive instance eqAxisValue :: Eq AxisValue
derive instance ordAxisValue :: Ord AxisValue

instance showAxisValue :: Show AxisValue where
  show (AxisValue n) = show n

-- | A collection of variation axis settings
newtype FontVariation = FontVariation (Array { axis :: VariationAxis, value :: AxisValue })

derive instance eqFontVariation :: Eq FontVariation

instance showFontVariation :: Show FontVariation where
  show fv = "FontVariation " <> toLegacyCSSValue fv

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // axis constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Weight axis (wght)
weight :: Number -> { axis :: VariationAxis, value :: AxisValue }
weight n = { axis: VariationAxis "wght", value: AxisValue n }

-- | Width axis (wdth)
width :: Number -> { axis :: VariationAxis, value :: AxisValue }
width n = { axis: VariationAxis "wdth", value: AxisValue n }

-- | Slant axis (slnt) - oblique angle in degrees
slant :: Number -> { axis :: VariationAxis, value :: AxisValue }
slant n = { axis: VariationAxis "slnt", value: AxisValue n }

-- | Italic axis (ital) - 0 or 1
italic :: Number -> { axis :: VariationAxis, value :: AxisValue }
italic n = { axis: VariationAxis "ital", value: AxisValue n }

-- | Optical size axis (opsz)
opticalSize :: Number -> { axis :: VariationAxis, value :: AxisValue }
opticalSize n = { axis: VariationAxis "opsz", value: AxisValue n }

-- | Grade axis (GRAD)
grade :: Number -> { axis :: VariationAxis, value :: AxisValue }
grade n = { axis: VariationAxis "GRAD", value: AxisValue n }

-- | Casual axis (CASL)
casual :: Number -> { axis :: VariationAxis, value :: AxisValue }
casual n = { axis: VariationAxis "CASL", value: AxisValue n }

-- | Cursive axis (CRSV)
cursive :: Number -> { axis :: VariationAxis, value :: AxisValue }
cursive n = { axis: VariationAxis "CRSV", value: AxisValue n }

-- | Monospace axis (MONO)
monospace :: Number -> { axis :: VariationAxis, value :: AxisValue }
monospace n = { axis: VariationAxis "MONO", value: AxisValue n }

-- | Fill axis (FILL)
fill :: Number -> { axis :: VariationAxis, value :: AxisValue }
fill n = { axis: VariationAxis "FILL", value: AxisValue n }

-- | Softness axis (SOFT)
softness :: Number -> { axis :: VariationAxis, value :: AxisValue }
softness n = { axis: VariationAxis "SOFT", value: AxisValue n }

-- | Wonky axis (WONK)
wonky :: Number -> { axis :: VariationAxis, value :: AxisValue }
wonky n = { axis: VariationAxis "WONK", value: AxisValue n }

-- | Custom axis with arbitrary 4-character tag
customAxis :: String -> Number -> { axis :: VariationAxis, value :: AxisValue }
customAxis tag n = { axis: VariationAxis tag, value: AxisValue n }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create FontVariation from array of axis settings
fontVariation :: Array { axis :: VariationAxis, value :: AxisValue } -> FontVariation
fontVariation = FontVariation

-- | Create FontVariation with a single axis
single :: { axis :: VariationAxis, value :: AxisValue } -> FontVariation
single setting = FontVariation [setting]

-- | Empty FontVariation (no axis settings)
empty :: FontVariation
empty = FontVariation []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add an axis setting (appends, may duplicate)
addAxis :: { axis :: VariationAxis, value :: AxisValue } -> FontVariation -> FontVariation
addAxis setting (FontVariation arr) = FontVariation (Array.snoc arr setting)

-- | Set an axis value (replaces if exists, adds if not)
setAxis :: { axis :: VariationAxis, value :: AxisValue } -> FontVariation -> FontVariation
setAxis setting (FontVariation arr) =
  let 
    filtered = Array.filter (\s -> s.axis /= setting.axis) arr
  in FontVariation (Array.snoc filtered setting)

-- | Remove an axis by tag
removeAxis :: VariationAxis -> FontVariation -> FontVariation
removeAxis axis (FontVariation arr) =
  FontVariation (Array.filter (\s -> s.axis /= axis) arr)

-- | Get an axis value if present
getAxis :: VariationAxis -> FontVariation -> Maybe AxisValue
getAxis axis (FontVariation arr) =
  map _.value (Array.find (\s -> s.axis == axis) arr)

-- | Merge two FontVariations (second overwrites first for same axes)
merge :: FontVariation -> FontVariation -> FontVariation
merge (FontVariation a) (FontVariation b) =
  let
    aFiltered = Array.filter (\s -> not (hasAxis s.axis b)) a
  in FontVariation (aFiltered <> b)
  where
  hasAxis :: VariationAxis -> Array { axis :: VariationAxis, value :: AxisValue } -> Boolean
  hasAxis ax arr = case Array.find (\s -> s.axis == ax) arr of
    Just _ -> true
    Nothing -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS font-variation-settings value
toLegacyCSSValue :: FontVariation -> String
toLegacyCSSValue (FontVariation []) = "normal"
toLegacyCSSValue (FontVariation arr) =
  joinWith ", " (map formatSetting arr)
  where
  formatSetting :: { axis :: VariationAxis, value :: AxisValue } -> String
  formatSetting { axis: VariationAxis tag, value: AxisValue n } =
    "\"" <> tag <> "\" " <> show n
  
  joinWith :: String -> Array String -> String
  joinWith _ [] = ""
  joinWith sep xs = case Array.uncons xs of
    Nothing -> ""
    Just { head: first, tail: rest } -> 
      foldl (\acc x -> acc <> sep <> x) first rest

-- | Convert to CSS style attribute string
toStyleAttribute :: FontVariation -> String
toStyleAttribute fv = "font-variation-settings: " <> toLegacyCSSValue fv <> ";"
