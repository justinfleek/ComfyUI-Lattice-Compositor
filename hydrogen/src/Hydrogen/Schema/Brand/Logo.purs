-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // schema // brand // logo
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo System: Complete logo specification for brand identity.
-- |
-- | From SMART Brand Ingestion Framework §9-14:
-- |   §9:  Logo components, integrity
-- |   §10: Logo lockups (arrangements, variants)
-- |   §11: Logo clear space (minimum clearance)
-- |   §12: Logo minimum sizing (print/digital bounds)
-- |   §13: Logo usage rules (placement, watermarks, social, app icons)
-- |   §14: Logo common errors (the "Do Not" list)
-- |
-- | This is the leader module that re-exports all Logo submodules.
-- |
-- | ## Submodules
-- |
-- | - Logo.Components: LogoComponent, IconDescription, WordmarkDescription, LogoSymbolism
-- | - Logo.Orientation: Orientation (Horizontal, Vertical, Square)
-- | - Logo.Variants: ColorVariant, VariantSet
-- | - Logo.ClearSpace: ClearSpaceMultiplier, ClearSpaceReference, ClearSpaceRule
-- | - Logo.Sizing: PrintSize, DigitalSize, SizeConstraint
-- | - Logo.Lockup: LockupName, LockupPriority, UsageContext, BackgroundColor, LogoLockup
-- | - Logo.Errors: ErrorCategory, LogoError, LogoErrorSet
-- | - Logo.Rules: WatermarkOpacity, WatermarkRule, SocialPlatform, SocialRule
-- | - Logo.System: LogoSystem, validation functions
-- |
-- | STATUS: PROVING (Lean4 proofs in progress)
-- |
-- | Invariants:
-- |   lockup_has_variants: Every lockup has >= 1 color variant
-- |   clear_space_positive: Clear space multiplier > 0
-- |   size_positive: All minimum sizes > 0
-- |   primary_lockup_exists: Logo system has exactly one primary lockup
-- |   error_categories_complete: All error types covered
-- |
-- | PURE DATA: Logos are pure data describing visual identity constraints.
-- | Rendering happens at target boundaries.

module Hydrogen.Schema.Brand.Logo
  ( -- * Re-exports from Components
    module Components
  
    -- * Re-exports from Orientation
  , module Orientation
  
    -- * Re-exports from Variants
  , module Variants
  
    -- * Re-exports from ClearSpace
  , module ClearSpace
  
    -- * Re-exports from Sizing
  , module Sizing
  
    -- * Re-exports from Lockup
  , module Lockup
  
    -- * Re-exports from Errors
  , module Errors
  
    -- * Re-exports from Rules
  , module Rules
  
    -- * Re-exports from System
  , module System
  ) where

import Hydrogen.Schema.Brand.Logo.Components
  ( LogoComponent(Icon, Wordmark)
  , allLogoComponents
  , componentToString
  , componentFromString
  , IconDescription
  , mkIconDescription
  , unIconDescription
  , WordmarkDescription
  , mkWordmarkDescription
  , unWordmarkDescription
  , LogoSymbolism
  , mkLogoSymbolism
  , unLogoSymbolism
  ) as Components

import Hydrogen.Schema.Brand.Logo.Orientation
  ( Orientation(Horizontal, Vertical, Square)
  , allOrientations
  , orientationToString
  , orientationFromString
  ) as Orientation

import Hydrogen.Schema.Brand.Logo.Variants
  ( ColorVariant(FullColor, BlackWhite, Reversed, SingleColor)
  , allColorVariants
  , variantToString
  , variantFromString
  , VariantSet
  , mkVariantSet
  , hasVariant
  , variantSetToArray
  ) as Variants

import Hydrogen.Schema.Brand.Logo.ClearSpace
  ( ClearSpaceMultiplier
  , mkClearSpaceMultiplier
  , unClearSpaceMultiplier
  , ClearSpaceReference
  , mkClearSpaceReference
  , unClearSpaceReference
  , ClearSpaceRule
  , mkClearSpaceRule
  , clearSpaceMultiplier
  , clearSpaceReference
  , showClearSpaceRule
  ) as ClearSpace

import Hydrogen.Schema.Brand.Logo.Sizing
  ( PrintSize
  , mkPrintSize
  , unPrintSize
  , DigitalSize
  , mkDigitalSize
  , unDigitalSize
  , SizeConstraint
  , mkSizeConstraint
  , printMinimum
  , digitalMinimum
  , showSizeConstraint
  ) as Sizing

import Hydrogen.Schema.Brand.Logo.Lockup
  ( LockupName
  , mkLockupName
  , unLockupName
  , LockupPriority(Primary, Secondary, Tertiary)
  , allLockupPriorities
  , priorityToString
  , UsageContext(Letterhead, BusinessCard, EmailSignature, SocialProfile, WebsiteHeader, AppIcon, Favicon, Merchandise, PrintAdvertising, DigitalAdvertising, Presentation, Video)
  , allUsageContexts
  , contextToString
  , BackgroundColor
  , mkBackgroundColor
  , unBackgroundColor
  , LogoLockup
  , mkLogoLockup
  , lockupName
  , lockupComponents
  , lockupOrientation
  , lockupPriority
  , lockupVariants
  , lockupContexts
  , lockupApprovedBackgrounds
  , lockupClearSpace
  , lockupMinSize
  , showLogoLockup
  ) as Lockup

import Hydrogen.Schema.Brand.Logo.Errors
  ( ErrorCategory(ContrastError, ColorError, DistortionError, LayoutError, ClearSpaceError)
  , allErrorCategories
  , categoryToString
  , LogoError
  , mkLogoError
  , errorCategory
  , errorDescription
  , showLogoError
  , LogoErrorSet
  , mkLogoErrorSet
  , addError
  , errorsByCategory
  , allErrors
  , hasErrorInCategory
  , showLogoErrorSet
  ) as Errors

import Hydrogen.Schema.Brand.Logo.Rules
  ( WatermarkOpacity
  , mkWatermarkOpacity
  , unWatermarkOpacity
  , WatermarkRule
  , mkWatermarkRule
  , watermarkOpacity
  , watermarkLockup
  , showWatermarkRule
  , SocialPlatform(Twitter, LinkedIn, Facebook, Instagram, YouTube, TikTok, Discord, Slack)
  , allSocialPlatforms
  , platformToString
  , SocialRule
  , mkSocialRule
  , socialPlatform
  , socialLockup
  , showSocialRule
  ) as Rules

import Hydrogen.Schema.Brand.Logo.System
  ( LogoSystem
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
  , compareLockups
  , lockupsDiffer
  , hasNoErrors
  , countErrorsByCategory
  , validateLogoSystem
  ) as System
