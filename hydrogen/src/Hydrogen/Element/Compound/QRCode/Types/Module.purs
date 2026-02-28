-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // element // qrcode // types // module
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | QR Module Types — Individual cells in a QR code matrix.
-- |
-- | ## Module States
-- |
-- | - Dark: Renders as foreground color (typically black)
-- | - Light: Renders as background color (typically white)
-- | - Reserved: Placeholder during construction (not final)
-- |
-- | ## Module Types
-- |
-- | Different semantic types render differently in artistic styles:
-- | - DataModule: Data or error correction
-- | - FinderModule: Finder patterns (corners)
-- | - TimingModule: Timing patterns (alternating)
-- | - AlignmentModule: Alignment patterns (Version 2+)
-- | - FormatModule: Format information
-- | - VersionModule: Version information (Version 7+)
-- | - QuietModule: Quiet zone (white border)
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Show)

module Hydrogen.Element.Compound.QRCode.Types.Module
  ( -- * Module Type
    ModuleType(DataModule, FinderModule, TimingModule, AlignmentModule, FormatModule, VersionModule, QuietModule)
  
  -- * Module
  , Module(Dark, Light, Reserved)
  , isDark
  , isLight
  , isReserved
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // module type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Module type for semantic categorization.
-- |
-- | Different module types render differently in artistic styles.
data ModuleType
  = DataModule       -- ^ Data or error correction
  | FinderModule     -- ^ Finder patterns (corners)
  | TimingModule     -- ^ Timing patterns (alternating)
  | AlignmentModule  -- ^ Alignment patterns (Version 2+)
  | FormatModule     -- ^ Format information
  | VersionModule    -- ^ Version information (Version 7+)
  | QuietModule      -- ^ Quiet zone (white border)

derive instance eqModuleType :: Eq ModuleType

instance showModuleType :: Show ModuleType where
  show DataModule = "Data"
  show FinderModule = "Finder"
  show TimingModule = "Timing"
  show AlignmentModule = "Alignment"
  show FormatModule = "Format"
  show VersionModule = "Version"
  show QuietModule = "Quiet"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // module
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single module (cell) in the QR code.
-- |
-- | - Dark: renders as foreground color (typically black)
-- | - Light: renders as background color (typically white)
-- | - Reserved: placeholder during construction (not final)
data Module
  = Dark ModuleType   -- ^ Foreground module with semantic type
  | Light ModuleType  -- ^ Background module with semantic type
  | Reserved          -- ^ Placeholder (used during matrix construction)

derive instance eqModule :: Eq Module

instance showModule :: Show Module where
  show (Dark t) = "Dark(" <> show t <> ")"
  show (Light t) = "Light(" <> show t <> ")"
  show Reserved = "Reserved"

-- | Check if module is dark
isDark :: Module -> Boolean
isDark (Dark _) = true
isDark _ = false

-- | Check if module is light
isLight :: Module -> Boolean
isLight (Light _) = true
isLight _ = false

-- | Check if module is reserved (placeholder)
isReserved :: Module -> Boolean
isReserved Reserved = true
isReserved _ = false
