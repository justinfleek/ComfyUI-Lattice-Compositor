-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // brand // tagline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Brand taglines: Verbal signatures of the brand.
-- |
-- | From SMART Brand Ingestion Framework:
-- |   - Taglines distill Brand Promise, Mission, and Values into compact messages
-- |   - Primary tagline: Single most important, LOCKED COPY
-- |   - Secondary taglines: Alternatives for different contexts, LOCKED COPY
-- |   - NEVER rewrite, reword, or edit taglines
-- |
-- | PURE DATA: Taglines are immutable atoms.

module Hydrogen.Schema.Brand.Tagline
  ( -- * Tagline Atom
    Tagline
  , mkTagline
  , unTagline
  
  -- * Tagline Set
  , TaglineSet
  , mkTaglineSet
  , primaryTagline
  , secondaryTaglines
  , allTaglines
  
  -- * Usage Rules
  , TaglineUsageRule(..)
  , defaultUsageRules
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (>)
  , (<=)
  , (&&)
  , (<>)
  , compare
  , show
  , map
  )

import Data.Array ((:))
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (length, trim) as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // tagline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tagline atom.
-- |
-- | A compact, repeatable message that functions as the verbal signature.
-- | LOCKED COPY — must never be rewritten, reworded, or edited in any way.
-- |
-- | Bounded: 1-150 characters.
newtype Tagline = Tagline String

derive instance eqTagline :: Eq Tagline
derive instance ordTagline :: Ord Tagline

instance showTagline :: Show Tagline where
  show (Tagline t) = "Tagline(\"" <> t <> "\")"

-- | Smart constructor with validation.
-- |
-- | Returns Nothing if empty or exceeds 150 characters.
mkTagline :: String -> Maybe Tagline
mkTagline s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 150
     then Just (Tagline trimmed)
     else Nothing

-- | Unwrap tagline.
-- |
-- | Note: The returned string should be used verbatim.
-- | Do not modify, paraphrase, or "improve" taglines.
unTagline :: Tagline -> String
unTagline (Tagline t) = t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // tagline set
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tagline set molecule.
-- |
-- | Composed of a primary tagline and optional secondary taglines.
-- | Primary is required; secondary is for alternative contexts.
type TaglineSet =
  { primary :: Tagline
  , secondary :: Array Tagline
  }

-- | Create a tagline set with primary only.
mkTaglineSet :: Tagline -> TaglineSet
mkTaglineSet primary =
  { primary
  , secondary: []
  }

-- | Get the primary tagline.
primaryTagline :: TaglineSet -> Tagline
primaryTagline ts = ts.primary

-- | Get secondary taglines.
secondaryTaglines :: TaglineSet -> Array Tagline
secondaryTaglines ts = ts.secondary

-- | Get all taglines (primary first).
allTaglines :: TaglineSet -> Array Tagline
allTaglines ts = ts.primary : ts.secondary

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // usage rules
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tagline usage rules.
-- |
-- | From SMART framework:
-- |   - May be used alongside any approved logo iteration
-- |   - Should NOT be combined with campaign-specific phrases
-- |   - Must NEVER be rewritten in any way
data TaglineUsageRule
  = CanUseWithLogo           -- May accompany logo
  | CanUseStandalone         -- May be used as standalone marketing
  | NeverCombineWithCampaign -- Don't mix with campaign phrases
  | NeverRewrite             -- Immutable, verbatim use only

derive instance eqTaglineUsageRule :: Eq TaglineUsageRule

instance showTaglineUsageRule :: Show TaglineUsageRule where
  show CanUseWithLogo = "can-use-with-logo"
  show CanUseStandalone = "can-use-standalone"
  show NeverCombineWithCampaign = "never-combine-with-campaign"
  show NeverRewrite = "never-rewrite"

-- | Default usage rules (all standard constraints).
defaultUsageRules :: Array TaglineUsageRule
defaultUsageRules =
  [ CanUseWithLogo
  , CanUseStandalone
  , NeverCombineWithCampaign
  , NeverRewrite
  ]
