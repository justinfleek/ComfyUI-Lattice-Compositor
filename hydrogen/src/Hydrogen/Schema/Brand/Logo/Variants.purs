-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // brand // logo // variants
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo Color Variants: Approved color treatments for logo usage.
-- |
-- | FullColor: Primary brand colors
-- | BlackWhite: Monochrome for limited contexts
-- | Reversed: Light logo on dark backgrounds
-- | SingleColor: One-color version (often for printing)

module Hydrogen.Schema.Brand.Logo.Variants
  ( -- * Color Variant
    ColorVariant(..)
  , allColorVariants
  , variantToString
  , variantFromString
  
    -- * Variant Set
  , VariantSet
  , mkVariantSet
  , hasVariant
  , variantSetToArray
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (>)
  , compare
  , show
  )

import Data.Array (elem, nub, length)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color variant atom.
-- |
-- | The approved color treatments for logo usage.
data ColorVariant
  = FullColor    -- Primary brand colors
  | BlackWhite   -- Monochrome for limited contexts
  | Reversed     -- Light logo on dark backgrounds
  | SingleColor  -- One-color version (often for printing)

derive instance eqColorVariant :: Eq ColorVariant

instance ordColorVariant :: Ord ColorVariant where
  compare v1 v2 = compare (variantToInt v1) (variantToInt v2)
    where
      variantToInt :: ColorVariant -> Int
      variantToInt FullColor = 0
      variantToInt BlackWhite = 1
      variantToInt Reversed = 2
      variantToInt SingleColor = 3

instance showColorVariant :: Show ColorVariant where
  show = variantToString

-- | All color variants for enumeration.
allColorVariants :: Array ColorVariant
allColorVariants = [FullColor, BlackWhite, Reversed, SingleColor]

-- | Convert variant to string.
variantToString :: ColorVariant -> String
variantToString FullColor = "full-color"
variantToString BlackWhite = "black-white"
variantToString Reversed = "reversed"
variantToString SingleColor = "single-color"

-- | Parse variant from string.
variantFromString :: String -> Maybe ColorVariant
variantFromString s = case String.toLower s of
  "full-color" -> Just FullColor
  "fullcolor" -> Just FullColor
  "black-white" -> Just BlackWhite
  "blackwhite" -> Just BlackWhite
  "bw" -> Just BlackWhite
  "reversed" -> Just Reversed
  "single-color" -> Just SingleColor
  "singlecolor" -> Just SingleColor
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // variant set
-- ═════════════════════════════════════════════════════════════════════════════

-- | Variant set molecule.
-- |
-- | A non-empty set of approved color variants.
-- | Invariant: At least one variant must exist.
type VariantSet =
  { variants :: Array ColorVariant
  }

-- | Create a variant set (deduplicates, ensures non-empty).
mkVariantSet :: Array ColorVariant -> Maybe VariantSet
mkVariantSet vs =
  let deduped = nub vs
  in if length deduped > 0
     then Just { variants: deduped }
     else Nothing

-- | Check if a variant is in the set.
hasVariant :: ColorVariant -> VariantSet -> Boolean
hasVariant v vs = elem v vs.variants

-- | Get variants as array.
variantSetToArray :: VariantSet -> Array ColorVariant
variantSetToArray vs = vs.variants
