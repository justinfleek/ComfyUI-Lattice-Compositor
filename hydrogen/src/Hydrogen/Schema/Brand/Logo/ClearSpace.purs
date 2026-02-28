-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brand // logo // clear-space
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Clear Space Rules (§11): Minimum clearance around the logo.
-- |
-- | From SMART Brand Ingestion Framework §11:
-- |   - Multiplier: How many times the reference element to use
-- |   - Reference: The element used as measurement basis (e.g., "height of N")

module Hydrogen.Schema.Brand.Logo.ClearSpace
  ( -- * Clear Space Multiplier
    ClearSpaceMultiplier
  , mkClearSpaceMultiplier
  , unClearSpaceMultiplier
  
    -- * Clear Space Reference
  , ClearSpaceReference
  , mkClearSpaceReference
  , unClearSpaceReference
  
    -- * Clear Space Rule
  , ClearSpaceRule
  , mkClearSpaceRule
  , clearSpaceMultiplier
  , clearSpaceReference
  , showClearSpaceRule
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (>)
  , (<=)
  , (&&)
  , (<>)
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // clear space multiplier
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clear space multiplier atom.
-- |
-- | The multiplier applied to a reference element to calculate clear space.
-- | Bounded: 0.1 to 10.0 (must be positive, reasonable range).
-- |
-- | Example: 2.0 means "twice the height of the reference element"
newtype ClearSpaceMultiplier = ClearSpaceMultiplier Number

derive instance eqClearSpaceMultiplier :: Eq ClearSpaceMultiplier
derive instance ordClearSpaceMultiplier :: Ord ClearSpaceMultiplier

instance showClearSpaceMultiplier :: Show ClearSpaceMultiplier where
  show (ClearSpaceMultiplier m) = "ClearSpaceMultiplier(" <> show m <> ")"

-- | Smart constructor for clear space multiplier.
-- |
-- | Returns Nothing if <= 0 or > 10.
mkClearSpaceMultiplier :: Number -> Maybe ClearSpaceMultiplier
mkClearSpaceMultiplier n =
  if n > 0.0 && n <= 10.0
  then Just (ClearSpaceMultiplier n)
  else Nothing

-- | Unwrap multiplier.
unClearSpaceMultiplier :: ClearSpaceMultiplier -> Number
unClearSpaceMultiplier (ClearSpaceMultiplier m) = m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // clear space reference
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clear space reference atom.
-- |
-- | The element used as the measurement basis for clear space.
-- | Examples: "height of letter N", "icon width", "x-height"
-- | Bounded: 1-100 characters.
newtype ClearSpaceReference = ClearSpaceReference String

derive instance eqClearSpaceReference :: Eq ClearSpaceReference
derive instance ordClearSpaceReference :: Ord ClearSpaceReference

instance showClearSpaceReference :: Show ClearSpaceReference where
  show (ClearSpaceReference r) = "ClearSpaceReference(" <> r <> ")"

-- | Smart constructor for clear space reference.
mkClearSpaceReference :: String -> Maybe ClearSpaceReference
mkClearSpaceReference s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 100
     then Just (ClearSpaceReference trimmed)
     else Nothing

-- | Unwrap reference.
unClearSpaceReference :: ClearSpaceReference -> String
unClearSpaceReference (ClearSpaceReference r) = r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // clear space rule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clear space rule molecule.
-- |
-- | Defines the minimum clearance around the logo.
-- | Composed of a multiplier and a reference element.
type ClearSpaceRule =
  { multiplier :: ClearSpaceMultiplier
  , reference :: ClearSpaceReference
  }

-- | Create a clear space rule.
mkClearSpaceRule :: ClearSpaceMultiplier -> ClearSpaceReference -> ClearSpaceRule
mkClearSpaceRule m r =
  { multiplier: m
  , reference: r
  }

-- | Get the multiplier from a rule.
clearSpaceMultiplier :: ClearSpaceRule -> ClearSpaceMultiplier
clearSpaceMultiplier rule = rule.multiplier

-- | Get the reference from a rule.
clearSpaceReference :: ClearSpaceRule -> ClearSpaceReference
clearSpaceReference rule = rule.reference

-- | Show clear space rule (debug format).
showClearSpaceRule :: ClearSpaceRule -> String
showClearSpaceRule rule =
  "ClearSpaceRule { multiplier: " <> 
  show (unClearSpaceMultiplier rule.multiplier) <> 
  ", reference: \"" <> unClearSpaceReference rule.reference <> "\" }"
