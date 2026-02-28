-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // accessibility
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ARIA Live Regions — Dynamic content announcements
-- |
-- | Live regions allow assistive technology to announce dynamic content
-- | changes without requiring the user to navigate to that content.
-- |
-- | ## Critical for
-- | - Notification systems (toasts, alerts)
-- | - Form validation messages
-- | - Loading states
-- | - Chat applications
-- | - Real-time data (stock tickers, sports scores)
-- |
-- | ## Reference
-- | https://www.w3.org/TR/wai-aria-1.2/#aria-live
module Hydrogen.Schema.Accessibility.LiveRegion
  ( -- * Politeness Levels
    Politeness(..)
  , politenessToString
    -- * Live Region Properties
  , AriaLive(..)
  , AriaAtomic(..)
  , AriaRelevant(..)
  , Relevance(..)
    -- * Live Region Molecule
  , LiveRegionConfig(..)
  , defaultLiveRegion
  , assertive
  , polite
  , statusRegion
  , alertRegion
  , logRegion
  ) where

import Prelude

import Data.Array (intercalate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // politeness levels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Politeness level for live region announcements.
-- |
-- | - Off: No announcements (default)
-- | - Polite: Announce after current speech finishes
-- | - Assertive: Interrupt immediately (use sparingly!)
data Politeness
  = Off
  | Polite
  | Assertive

derive instance eqPoliteness :: Eq Politeness

instance showPoliteness :: Show Politeness where
  show = politenessToString

-- | Convert politeness to aria-live value.
politenessToString :: Politeness -> String
politenessToString Off = "off"
politenessToString Polite = "polite"
politenessToString Assertive = "assertive"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // live region properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | aria-live: Politeness setting for the region.
newtype AriaLive = AriaLive Politeness

derive instance eqAriaLive :: Eq AriaLive

instance showAriaLive :: Show AriaLive where
  show (AriaLive p) = politenessToString p

-- | aria-atomic: Whether to present the region as a whole.
-- |
-- | - true: Announce entire region on any change
-- | - false: Announce only changed nodes (default)
newtype AriaAtomic = AriaAtomic Boolean

derive instance eqAriaAtomic :: Eq AriaAtomic

instance showAriaAtomic :: Show AriaAtomic where
  show (AriaAtomic true) = "true"
  show (AriaAtomic false) = "false"

-- | Types of changes to announce.
data Relevance
  = RelevanceAdditions   -- New nodes added
  | RelevanceRemovals    -- Nodes removed
  | RelevanceText        -- Text content changed
  | RelevanceAll         -- All changes (additions, removals, text)

derive instance eqRelevance :: Eq Relevance

instance showRelevance :: Show Relevance where
  show RelevanceAdditions = "additions"
  show RelevanceRemovals = "removals"
  show RelevanceText = "text"
  show RelevanceAll = "all"

-- | aria-relevant: Which types of changes to announce.
newtype AriaRelevant = AriaRelevant (Array Relevance)

derive instance eqAriaRelevant :: Eq AriaRelevant

instance showAriaRelevant :: Show AriaRelevant where
  show (AriaRelevant rs) = intercalate " " (map show rs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // live region molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for a live region.
-- |
-- | Combines aria-live, aria-atomic, and aria-relevant into a cohesive unit.
type LiveRegionConfig =
  { live :: Politeness
  , atomic :: Boolean
  , relevant :: Array Relevance
  }

-- | Default live region: polite, not atomic, additions + text.
defaultLiveRegion :: LiveRegionConfig
defaultLiveRegion =
  { live: Polite
  , atomic: false
  , relevant: [ RelevanceAdditions, RelevanceText ]
  }

-- | Assertive live region for urgent messages.
assertive :: LiveRegionConfig
assertive = defaultLiveRegion { live = Assertive }

-- | Polite live region (alias for default).
polite :: LiveRegionConfig
polite = defaultLiveRegion

-- | Status region preset: polite, atomic, additions + text.
-- |
-- | Use for status messages that replace each other.
statusRegion :: LiveRegionConfig
statusRegion =
  { live: Polite
  , atomic: true
  , relevant: [ RelevanceAdditions, RelevanceText ]
  }

-- | Alert region preset: assertive, atomic, all changes.
-- |
-- | Use for critical alerts requiring immediate attention.
alertRegion :: LiveRegionConfig
alertRegion =
  { live: Assertive
  , atomic: true
  , relevant: [ RelevanceAll ]
  }

-- | Log region preset: polite, not atomic, additions only.
-- |
-- | Use for chat logs, activity feeds, console output.
logRegion :: LiveRegionConfig
logRegion =
  { live: Polite
  , atomic: false
  , relevant: [ RelevanceAdditions ]
  }
