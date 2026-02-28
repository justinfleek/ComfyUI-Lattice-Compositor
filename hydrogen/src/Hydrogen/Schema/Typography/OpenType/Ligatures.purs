-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                  // hydrogen // schema // typography // opentype // ligatures
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Ligatures - OpenType ligature features for typographic refinement.
-- |
-- | Ligatures are single glyphs that replace sequences of characters for
-- | improved aesthetics or readability. OpenType defines several categories:
-- |
-- | ## Common Ligatures (liga)
-- | Standard ligatures enabled by default: fi, fl, ff, ffi, ffl
-- | These prevent collisions between letters with overhanging parts.
-- |
-- | ## Discretionary Ligatures (dlig)
-- | Decorative ligatures for special effects: ct, st, Th
-- | Use sparingly for display text; disabled by default.
-- |
-- | ## Contextual Ligatures (clig)
-- | Ligatures that depend on surrounding context.
-- | Common in script and Arabic typefaces.
-- |
-- | ## Historical Ligatures (hlig)
-- | Archaic ligatures for period typography: ſt (long s + t)
-- | Use for historical documents or vintage aesthetics.
-- |
-- | ## CSS Mapping
-- |
-- | Maps to `font-variant-ligatures` and `font-feature-settings`.

module Hydrogen.Schema.Typography.OpenType.Ligatures
  ( -- * Types
    LigatureSet(..)
  , Ligatures(..)
  
  -- * Constructors
  , none
  , normal
  , all
  , common
  , discretionary
  , contextual
  , historical
  , custom
  
  -- * Modifiers
  , withCommon
  , withDiscretionary
  , withContextual
  , withHistorical
  , withoutCommon
  
  -- * Predicates
  , hasCommon
  , hasDiscretionary
  , hasContextual
  , hasHistorical
  , isNone
  , isAll
  
  -- * CSS Output
  , toLegacyCss
  , toFontFeatureSettings
  ) where

import Prelude

import Data.Array (intercalate)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // ligature set
-- ═════════════════════════════════════════════════════════════════════════════

-- | Individual ligature feature toggle
-- |
-- | Each set can be enabled or disabled independently.
data LigatureSet
  = LigatureOn   -- ^ Feature enabled
  | LigatureOff  -- ^ Feature disabled

derive instance eqLigatureSet :: Eq LigatureSet
derive instance ordLigatureSet :: Ord LigatureSet

instance showLigatureSet :: Show LigatureSet where
  show LigatureOn = "LigatureOn"
  show LigatureOff = "LigatureOff"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // ligatures
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete ligature configuration
-- |
-- | Controls all four ligature categories independently.
newtype Ligatures = Ligatures
  { common :: LigatureSet        -- ^ fi, fl, ff, ffi, ffl (liga)
  , discretionary :: LigatureSet -- ^ ct, st, decorative (dlig)
  , contextual :: LigatureSet    -- ^ context-dependent (clig)
  , historical :: LigatureSet    -- ^ archaic forms (hlig)
  }

derive instance eqLigatures :: Eq Ligatures

instance showLigatures :: Show Ligatures where
  show (Ligatures l) =
    "Ligatures { common: " <> show l.common <>
    ", discretionary: " <> show l.discretionary <>
    ", contextual: " <> show l.contextual <>
    ", historical: " <> show l.historical <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | No ligatures (all disabled)
-- |
-- | Use when ligatures interfere with readability or design intent.
-- | Common in monospace code fonts or when letter spacing is critical.
none :: Ligatures
none = Ligatures
  { common: LigatureOff
  , discretionary: LigatureOff
  , contextual: LigatureOff
  , historical: LigatureOff
  }

-- | Normal ligatures (browser default)
-- |
-- | Common and contextual ligatures enabled.
-- | This is the standard setting for body text.
normal :: Ligatures
normal = Ligatures
  { common: LigatureOn
  , discretionary: LigatureOff
  , contextual: LigatureOn
  , historical: LigatureOff
  }

-- | All ligatures enabled
-- |
-- | Use for display text or decorative typography.
-- | May be too ornate for body text.
all :: Ligatures
all = Ligatures
  { common: LigatureOn
  , discretionary: LigatureOn
  , contextual: LigatureOn
  , historical: LigatureOn
  }

-- | Only common ligatures
common :: Ligatures
common = Ligatures
  { common: LigatureOn
  , discretionary: LigatureOff
  , contextual: LigatureOff
  , historical: LigatureOff
  }

-- | Only discretionary ligatures
-- |
-- | Note: Common ligatures are typically still desired with discretionary.
discretionary :: Ligatures
discretionary = Ligatures
  { common: LigatureOn
  , discretionary: LigatureOn
  , contextual: LigatureOff
  , historical: LigatureOff
  }

-- | Only contextual ligatures
contextual :: Ligatures
contextual = Ligatures
  { common: LigatureOff
  , discretionary: LigatureOff
  , contextual: LigatureOn
  , historical: LigatureOff
  }

-- | Only historical ligatures
-- |
-- | Note: Usually combined with common ligatures for period typography.
historical :: Ligatures
historical = Ligatures
  { common: LigatureOn
  , discretionary: LigatureOff
  , contextual: LigatureOff
  , historical: LigatureOn
  }

-- | Custom ligature configuration
custom 
  :: { common :: Boolean
     , discretionary :: Boolean
     , contextual :: Boolean
     , historical :: Boolean
     }
  -> Ligatures
custom cfg = Ligatures
  { common: if cfg.common then LigatureOn else LigatureOff
  , discretionary: if cfg.discretionary then LigatureOn else LigatureOff
  , contextual: if cfg.contextual then LigatureOn else LigatureOff
  , historical: if cfg.historical then LigatureOn else LigatureOff
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Enable common ligatures
withCommon :: Ligatures -> Ligatures
withCommon (Ligatures l) = Ligatures l { common = LigatureOn }

-- | Enable discretionary ligatures
withDiscretionary :: Ligatures -> Ligatures
withDiscretionary (Ligatures l) = Ligatures l { discretionary = LigatureOn }

-- | Enable contextual ligatures
withContextual :: Ligatures -> Ligatures
withContextual (Ligatures l) = Ligatures l { contextual = LigatureOn }

-- | Enable historical ligatures
withHistorical :: Ligatures -> Ligatures
withHistorical (Ligatures l) = Ligatures l { historical = LigatureOn }

-- | Disable common ligatures
-- |
-- | Use for monospace code fonts or when letter spacing must be preserved.
withoutCommon :: Ligatures -> Ligatures
withoutCommon (Ligatures l) = Ligatures l { common = LigatureOff }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Are common ligatures enabled?
hasCommon :: Ligatures -> Boolean
hasCommon (Ligatures { common: LigatureOn }) = true
hasCommon _ = false

-- | Are discretionary ligatures enabled?
hasDiscretionary :: Ligatures -> Boolean
hasDiscretionary (Ligatures { discretionary: LigatureOn }) = true
hasDiscretionary _ = false

-- | Are contextual ligatures enabled?
hasContextual :: Ligatures -> Boolean
hasContextual (Ligatures { contextual: LigatureOn }) = true
hasContextual _ = false

-- | Are historical ligatures enabled?
hasHistorical :: Ligatures -> Boolean
hasHistorical (Ligatures { historical: LigatureOn }) = true
hasHistorical _ = false

-- | Are all ligatures disabled?
isNone :: Ligatures -> Boolean
isNone l = not (hasCommon l) && not (hasDiscretionary l) && 
           not (hasContextual l) && not (hasHistorical l)

-- | Are all ligatures enabled?
isAll :: Ligatures -> Boolean
isAll l = hasCommon l && hasDiscretionary l && 
          hasContextual l && hasHistorical l

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary — pure string generation.
-- | Convert to CSS font-variant-ligatures value
toLegacyCss :: Ligatures -> String
toLegacyCss l
  | isNone l = "font-variant-ligatures: none;"
  | isAll l = "font-variant-ligatures: common-ligatures discretionary-ligatures contextual historical-ligatures;"
  | otherwise = "font-variant-ligatures: " <> buildValue l <> ";"
  where
  buildValue :: Ligatures -> String
  buildValue (Ligatures lig) =
    let 
      parts = 
        (if lig.common == LigatureOn then ["common-ligatures"] else ["no-common-ligatures"]) <>
        (if lig.discretionary == LigatureOn then ["discretionary-ligatures"] else []) <>
        (if lig.contextual == LigatureOn then ["contextual"] else []) <>
        (if lig.historical == LigatureOn then ["historical-ligatures"] else [])
    in joinParts parts

  joinParts :: Array String -> String
  joinParts [] = "normal"
  joinParts xs = intercalate " " xs

-- | Convert to font-feature-settings value
-- |
-- | More explicit control using OpenType feature tags.
toFontFeatureSettings :: Ligatures -> String
toFontFeatureSettings (Ligatures l) =
  "font-feature-settings: " <>
  "\"liga\" " <> toggleToString l.common <> ", " <>
  "\"dlig\" " <> toggleToString l.discretionary <> ", " <>
  "\"clig\" " <> toggleToString l.contextual <> ", " <>
  "\"hlig\" " <> toggleToString l.historical <> ";"
  where
  toggleToString :: LigatureSet -> String
  toggleToString LigatureOn = "1"
  toggleToString LigatureOff = "0"
