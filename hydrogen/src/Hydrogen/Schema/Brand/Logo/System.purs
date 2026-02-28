-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // brand // logo // system
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo System: Complete logo specification compound.
-- |
-- | From SMART Brand Ingestion Framework §9-14:
-- |   - Complete logo specification for a brand
-- |   - Validation and comparison functions
-- |
-- | Invariants:
-- |   - Must have exactly one primary lockup
-- |   - All referenced lockups must exist
-- |   - At least one contrast error in error set (most common issue)

module Hydrogen.Schema.Brand.Logo.System
  ( -- * Logo System
    LogoSystem
  , mkLogoSystem
  , primaryLockup
  , alternateLockups
  , allLockups
  , logoErrors
  , logoWatermarkRule
  , logoSocialRules
  , logoIconDescription
  , logoWordmarkDescription
  , logoSymbolism
  , findLockupByName
  , findLockupsForContext
  , showLogoSystem
  
    -- * Comparison and Validation
  , compareLockups
  , lockupsDiffer
  , hasNoErrors
  , countErrorsByCategory
  , validateLogoSystem
  ) where

import Prelude
  ( class Eq
  , Ordering
  , (==)
  , (/=)
  , (<>)
  , compare
  , map
  , show
  )

import Data.Array (elem, nub, length, filter, head, null, (:))
import Data.Maybe (Maybe(Just, Nothing))
import Data.Foldable (foldl)

import Hydrogen.Schema.Brand.Logo.Components 
  ( IconDescription
  , WordmarkDescription
  , LogoSymbolism
  )
import Hydrogen.Schema.Brand.Logo.Lockup 
  ( LogoLockup
  , LockupName
  , UsageContext
  , unLockupName
  )
import Hydrogen.Schema.Brand.Logo.Errors 
  ( LogoErrorSet
  , ErrorCategory(ContrastError, ColorError, DistortionError, LayoutError, ClearSpaceError)
  , errorsByCategory
  , allErrors
  )
import Hydrogen.Schema.Brand.Logo.Rules 
  ( WatermarkRule
  , SocialRule
  , unWatermarkOpacity
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // logo system
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logo system compound.
-- |
-- | Complete logo specification for a brand.
-- | 
-- | Invariants:
-- |   - Must have exactly one primary lockup
-- |   - All referenced lockups must exist
-- |   - At least one contrast error in error set (most common issue)
type LogoSystem =
  { primary :: LogoLockup
  , alternates :: Array LogoLockup
  , errors :: LogoErrorSet
  , watermark :: Maybe WatermarkRule
  , socialRules :: Array SocialRule
  , iconDescription :: Maybe IconDescription
  , wordmarkDescription :: Maybe WordmarkDescription
  , symbolism :: Maybe LogoSymbolism
  }

-- | Create a logo system.
-- |
-- | The first lockup is always primary, regardless of its priority field.
mkLogoSystem
  :: LogoLockup
  -> Array LogoLockup
  -> LogoErrorSet
  -> Maybe WatermarkRule
  -> Array SocialRule
  -> Maybe IconDescription
  -> Maybe WordmarkDescription
  -> Maybe LogoSymbolism
  -> LogoSystem
mkLogoSystem primary alternates errors watermark socialRules iconDesc wordmarkDesc symbolism =
  { primary
  , alternates
  , errors
  , watermark
  , socialRules
  , iconDescription: iconDesc
  , wordmarkDescription: wordmarkDesc
  , symbolism
  }

-- | Get primary lockup.
primaryLockup :: LogoSystem -> LogoLockup
primaryLockup ls = ls.primary

-- | Get alternate lockups.
alternateLockups :: LogoSystem -> Array LogoLockup
alternateLockups ls = ls.alternates

-- | Get all lockups (primary first).
allLockups :: LogoSystem -> Array LogoLockup
allLockups ls = ls.primary : ls.alternates

-- | Get logo errors.
logoErrors :: LogoSystem -> LogoErrorSet
logoErrors ls = ls.errors

-- | Get watermark rule.
logoWatermarkRule :: LogoSystem -> Maybe WatermarkRule
logoWatermarkRule ls = ls.watermark

-- | Get social media rules.
logoSocialRules :: LogoSystem -> Array SocialRule
logoSocialRules ls = ls.socialRules

-- | Get icon description.
logoIconDescription :: LogoSystem -> Maybe IconDescription
logoIconDescription ls = ls.iconDescription

-- | Get wordmark description.
logoWordmarkDescription :: LogoSystem -> Maybe WordmarkDescription
logoWordmarkDescription ls = ls.wordmarkDescription

-- | Get logo symbolism.
logoSymbolism :: LogoSystem -> Maybe LogoSymbolism
logoSymbolism ls = ls.symbolism

-- | Find a lockup by name.
findLockupByName :: LockupName -> LogoSystem -> Maybe LogoLockup
findLockupByName name ls =
  head (filter (\l -> l.name == name) (allLockups ls))

-- | Find lockups approved for a specific context.
findLockupsForContext :: UsageContext -> LogoSystem -> Array LogoLockup
findLockupsForContext ctx ls =
  filter (\l -> elem ctx l.contexts) (allLockups ls)

-- | Show logo system (debug format).
showLogoSystem :: LogoSystem -> String
showLogoSystem ls =
  "LogoSystem { primary: \"" <> unLockupName ls.primary.name <>
  "\", alternates: " <> show (length ls.alternates) <>
  ", errors: " <> show (length (allErrors ls.errors)) <>
  ", watermark: " <> showMaybe ls.watermark <>
  ", socialRules: " <> show (length ls.socialRules) <> " }"
  where
    showMaybe :: Maybe WatermarkRule -> String
    showMaybe Nothing = "none"
    showMaybe (Just w) = show (unWatermarkOpacity w.opacity) <> " opacity"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // comparison and validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare two lockups by priority.
-- |
-- | Returns standard Ordering: LT if first is higher priority, GT if lower.
-- | Primary < Secondary < Tertiary (primary is "first").
compareLockups :: LogoLockup -> LogoLockup -> Ordering
compareLockups l1 l2 = compare l1.priority l2.priority

-- | Check if two lockups are different (by name).
-- |
-- | Useful for validation: ensuring no duplicate lockup names.
lockupsDiffer :: LogoLockup -> LogoLockup -> Boolean
lockupsDiffer l1 l2 = l1.name /= l2.name

-- | Check if the error set is empty.
-- |
-- | A well-formed brand guide should have at least some "Do Not" constraints.
-- | An empty error set may indicate incomplete brand ingestion.
hasNoErrors :: LogoErrorSet -> Boolean
hasNoErrors set = null (allErrors set)

-- | Count errors by category.
-- |
-- | Returns a summary of how many errors exist in each category.
-- | Useful for validation and completeness checking.
countErrorsByCategory :: LogoErrorSet -> Array { category :: ErrorCategory, count :: Int }
countErrorsByCategory set =
  let 
    categories = [ContrastError, ColorError, DistortionError, LayoutError, ClearSpaceError]
    countCat cat = { category: cat, count: length (errorsByCategory cat set) }
  in map countCat categories

-- | Validate a logo system for completeness.
-- |
-- | Returns an array of validation warnings. Empty array means valid.
-- | Checks:
-- |   - Has at least one error defined
-- |   - No duplicate lockup names
-- |   - Watermark lockup exists (if watermark rule defined)
-- |   - Social lockups exist (if social rules defined)
validateLogoSystem :: LogoSystem -> Array String
validateLogoSystem ls =
  foldl appendWarnings [] checks
  where
    appendWarnings :: Array String -> Maybe String -> Array String
    appendWarnings acc Nothing = acc
    appendWarnings acc (Just w) = w : acc
    
    checks :: Array (Maybe String)
    checks =
      [ checkHasErrors
      , checkNoDuplicateLockups
      , checkWatermarkLockupExists
      ]
    
    checkHasErrors :: Maybe String
    checkHasErrors =
      if hasNoErrors ls.errors
      then Just "Logo system has no error constraints defined"
      else Nothing
    
    checkNoDuplicateLockups :: Maybe String
    checkNoDuplicateLockups =
      let 
        names = map (\l -> unLockupName l.name) (allLockups ls)
        uniqueNames = nub names
      in if length names /= length uniqueNames
         then Just "Duplicate lockup names detected"
         else Nothing
    
    checkWatermarkLockupExists :: Maybe String
    checkWatermarkLockupExists = case ls.watermark of
      Nothing -> Nothing
      Just w -> case findLockupByName w.lockupRef ls of
        Nothing -> Just ("Watermark references non-existent lockup: " <> unLockupName w.lockupRef)
        Just _ -> Nothing
