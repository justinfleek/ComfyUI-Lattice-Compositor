-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // brand // logo // errors
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo Errors (§14): The "Do Not" constraints.
-- |
-- | From SMART Brand Ingestion Framework §14:
-- |   - ContrastError: Dark on dark, light on light
-- |   - ColorError: Off-brand colors, color modifications
-- |   - DistortionError: Squash, stretch, skew, crop
-- |   - LayoutError: Altered relationships, opacity issues
-- |   - ClearSpaceError: Encroachment on required spacing
-- |
-- | These are MORE VALUABLE than positive guidance for AI enforcement.

module Hydrogen.Schema.Brand.Logo.Errors
  ( -- * Error Category
    ErrorCategory(..)
  , allErrorCategories
  , categoryToString
  
    -- * Logo Error
  , LogoError
  , mkLogoError
  , errorCategory
  , errorDescription
  , showLogoError
  
    -- * Logo Error Set
  , LogoErrorSet
  , mkLogoErrorSet
  , addError
  , errorsByCategory
  , allErrors
  , hasErrorInCategory
  , showLogoErrorSet
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>)
  , (<=)
  , (&&)
  , (<>)
  , compare
  , map
  , show
  )

import Data.Array (nub, length, filter, (:))
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String
import Data.Foldable (intercalate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // error category
-- ═════════════════════════════════════════════════════════════════════════════

-- | Error category atom.
-- |
-- | Categories of logo misuse from SMART framework §14.
-- | These are the "Do Not" constraints — critical for AI enforcement.
data ErrorCategory
  = ContrastError     -- Dark on dark, light on light
  | ColorError        -- Off-brand colors, color modifications
  | DistortionError   -- Squash, stretch, skew, crop
  | LayoutError       -- Altered relationships, opacity issues
  | ClearSpaceError   -- Encroachment on required spacing

derive instance eqErrorCategory :: Eq ErrorCategory

instance ordErrorCategory :: Ord ErrorCategory where
  compare c1 c2 = compare (categoryToInt c1) (categoryToInt c2)
    where
      categoryToInt :: ErrorCategory -> Int
      categoryToInt ContrastError = 0
      categoryToInt ColorError = 1
      categoryToInt DistortionError = 2
      categoryToInt LayoutError = 3
      categoryToInt ClearSpaceError = 4

instance showErrorCategory :: Show ErrorCategory where
  show = categoryToString

-- | All error categories for enumeration.
allErrorCategories :: Array ErrorCategory
allErrorCategories = 
  [ ContrastError
  , ColorError
  , DistortionError
  , LayoutError
  , ClearSpaceError
  ]

-- | Convert category to string.
categoryToString :: ErrorCategory -> String
categoryToString ContrastError = "contrast-error"
categoryToString ColorError = "color-error"
categoryToString DistortionError = "distortion-error"
categoryToString LayoutError = "layout-error"
categoryToString ClearSpaceError = "clear-space-error"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // logo error
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logo error atom.
-- |
-- | A specific prohibited usage pattern.
-- | These are MORE VALUABLE than positive guidance for AI enforcement.
type LogoError =
  { category :: ErrorCategory
  , description :: String
  }

-- | Create a logo error.
-- |
-- | Description bounded: 1-500 characters.
mkLogoError :: ErrorCategory -> String -> Maybe LogoError
mkLogoError cat desc =
  let trimmed = String.trim desc
      len = String.length trimmed
  in if len > 0 && len <= 500
     then Just { category: cat, description: trimmed }
     else Nothing

-- | Get error category.
errorCategory :: LogoError -> ErrorCategory
errorCategory e = e.category

-- | Get error description.
errorDescription :: LogoError -> String
errorDescription e = e.description

-- | Show error (debug format).
showLogoError :: LogoError -> String
showLogoError e =
  "LogoError { category: " <> categoryToString e.category <>
  ", description: \"" <> e.description <> "\" }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // logo error set
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logo error set compound.
-- |
-- | Collection of all prohibited logo usages.
type LogoErrorSet =
  { errors :: Array LogoError
  }

-- | Create an error set.
mkLogoErrorSet :: Array LogoError -> LogoErrorSet
mkLogoErrorSet es = { errors: es }

-- | Add an error to the set.
addError :: LogoError -> LogoErrorSet -> LogoErrorSet
addError e set = { errors: e : set.errors }

-- | Get errors by category.
errorsByCategory :: ErrorCategory -> LogoErrorSet -> Array LogoError
errorsByCategory cat set = filter (\e -> e.category == cat) set.errors

-- | Get all errors.
allErrors :: LogoErrorSet -> Array LogoError
allErrors set = set.errors

-- | Check if the set has errors in a category.
hasErrorInCategory :: ErrorCategory -> LogoErrorSet -> Boolean
hasErrorInCategory cat set = length (errorsByCategory cat set) > 0

-- | Show error set (debug format).
showLogoErrorSet :: LogoErrorSet -> String
showLogoErrorSet set =
  "LogoErrorSet { count: " <> show (length set.errors) <> 
  ", categories: [" <> 
  intercalate ", " (map categoryToString (categoriesPresent set)) <> 
  "] }"
  where
    categoriesPresent :: LogoErrorSet -> Array ErrorCategory
    categoriesPresent s = nub (map (\e -> e.category) s.errors)
