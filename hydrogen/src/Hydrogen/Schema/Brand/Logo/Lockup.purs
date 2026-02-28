-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // brand // logo // lockup
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo Lockups (§10): Approved logo arrangements.
-- |
-- | From SMART Brand Ingestion Framework §10:
-- |   - LockupName: Descriptive label for a logo arrangement
-- |   - LockupPriority: Hierarchical importance (Primary, Secondary, Tertiary)
-- |   - UsageContext: Where a lockup is approved for use
-- |   - BackgroundColor: Approved background colors for logo placement
-- |   - LogoLockup: Complete specification for one logo arrangement

module Hydrogen.Schema.Brand.Logo.Lockup
  ( -- * Lockup Name
    LockupName
  , mkLockupName
  , unLockupName
  
    -- * Lockup Priority
  , LockupPriority(..)
  , allLockupPriorities
  , priorityToString
  
    -- * Usage Context
  , UsageContext(..)
  , allUsageContexts
  , contextToString
  
    -- * Background Color
  , BackgroundColor
  , mkBackgroundColor
  , unBackgroundColor
  
    -- * Logo Lockup
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
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (>)
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  , compare
  , map
  , show
  )

import Data.Array (nub, length)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String
import Data.Foldable (intercalate)

import Hydrogen.Schema.Brand.Logo.Components (LogoComponent)
import Hydrogen.Schema.Brand.Logo.Orientation (Orientation, orientationToString)
import Hydrogen.Schema.Brand.Logo.Variants (VariantSet, variantSetToArray, variantToString)
import Hydrogen.Schema.Brand.Logo.ClearSpace (ClearSpaceRule)
import Hydrogen.Schema.Brand.Logo.Sizing (SizeConstraint)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // lockup name
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lockup name atom.
-- |
-- | A descriptive label for a logo arrangement.
-- | Examples: "Primary", "Horizontal", "Icon Solo", "Favicon"
-- | Bounded: 1-50 characters.
newtype LockupName = LockupName String

derive instance eqLockupName :: Eq LockupName
derive instance ordLockupName :: Ord LockupName

instance showLockupName :: Show LockupName where
  show (LockupName n) = "LockupName(" <> n <> ")"

-- | Smart constructor for lockup name.
mkLockupName :: String -> Maybe LockupName
mkLockupName s =
  let trimmed = String.trim s
      len = String.length trimmed
  in if len > 0 && len <= 50
     then Just (LockupName trimmed)
     else Nothing

-- | Unwrap lockup name.
unLockupName :: LockupName -> String
unLockupName (LockupName n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // lockup priority
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lockup priority atom.
-- |
-- | The hierarchical importance of a lockup.
data LockupPriority
  = Primary     -- First choice, mandatory for brand introduction
  | Secondary   -- Alternative for specific contexts
  | Tertiary    -- Fallback for constrained spaces

derive instance eqLockupPriority :: Eq LockupPriority

instance ordLockupPriority :: Ord LockupPriority where
  compare p1 p2 = compare (priorityToInt p1) (priorityToInt p2)
    where
      priorityToInt :: LockupPriority -> Int
      priorityToInt Primary = 0
      priorityToInt Secondary = 1
      priorityToInt Tertiary = 2

instance showLockupPriority :: Show LockupPriority where
  show = priorityToString

-- | All lockup priorities for enumeration.
allLockupPriorities :: Array LockupPriority
allLockupPriorities = [Primary, Secondary, Tertiary]

-- | Convert priority to string.
priorityToString :: LockupPriority -> String
priorityToString Primary = "primary"
priorityToString Secondary = "secondary"
priorityToString Tertiary = "tertiary"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // usage context
-- ═════════════════════════════════════════════════════════════════════════════

-- | Usage context atom.
-- |
-- | Where a lockup is approved for use.
data UsageContext
  = Letterhead
  | BusinessCard
  | EmailSignature
  | SocialProfile
  | WebsiteHeader
  | AppIcon
  | Favicon
  | Merchandise
  | PrintAdvertising
  | DigitalAdvertising
  | Presentation
  | Video

derive instance eqUsageContext :: Eq UsageContext

instance ordUsageContext :: Ord UsageContext where
  compare c1 c2 = compare (contextToInt c1) (contextToInt c2)
    where
      contextToInt :: UsageContext -> Int
      contextToInt Letterhead = 0
      contextToInt BusinessCard = 1
      contextToInt EmailSignature = 2
      contextToInt SocialProfile = 3
      contextToInt WebsiteHeader = 4
      contextToInt AppIcon = 5
      contextToInt Favicon = 6
      contextToInt Merchandise = 7
      contextToInt PrintAdvertising = 8
      contextToInt DigitalAdvertising = 9
      contextToInt Presentation = 10
      contextToInt Video = 11

instance showUsageContext :: Show UsageContext where
  show = contextToString

-- | All usage contexts for enumeration.
allUsageContexts :: Array UsageContext
allUsageContexts = 
  [ Letterhead
  , BusinessCard
  , EmailSignature
  , SocialProfile
  , WebsiteHeader
  , AppIcon
  , Favicon
  , Merchandise
  , PrintAdvertising
  , DigitalAdvertising
  , Presentation
  , Video
  ]

-- | Convert context to string.
contextToString :: UsageContext -> String
contextToString Letterhead = "letterhead"
contextToString BusinessCard = "business-card"
contextToString EmailSignature = "email-signature"
contextToString SocialProfile = "social-profile"
contextToString WebsiteHeader = "website-header"
contextToString AppIcon = "app-icon"
contextToString Favicon = "favicon"
contextToString Merchandise = "merchandise"
contextToString PrintAdvertising = "print-advertising"
contextToString DigitalAdvertising = "digital-advertising"
contextToString Presentation = "presentation"
contextToString Video = "video"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // background color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Background color atom.
-- |
-- | An approved background color for logo placement.
-- | Stored as hex color string (e.g., "#FFFFFF", "#1A1A1A").
-- | Bounded: 4-9 characters (supports #RGB, #RRGGBB, #RRGGBBAA).
newtype BackgroundColor = BackgroundColor String

derive instance eqBackgroundColor :: Eq BackgroundColor
derive instance ordBackgroundColor :: Ord BackgroundColor

instance showBackgroundColor :: Show BackgroundColor where
  show (BackgroundColor c) = "BackgroundColor(" <> c <> ")"

-- | Smart constructor for background color.
mkBackgroundColor :: String -> Maybe BackgroundColor
mkBackgroundColor s =
  let trimmed = String.toUpper (String.trim s)
      len = String.length trimmed
  in if len >= 4 && len <= 9 && String.take 1 trimmed == "#"
     then Just (BackgroundColor trimmed)
     else Nothing

-- | Unwrap background color.
unBackgroundColor :: BackgroundColor -> String
unBackgroundColor (BackgroundColor c) = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // logo lockup
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logo lockup molecule.
-- |
-- | A complete specification for one logo arrangement.
-- | Invariant: Must have at least one color variant.
type LogoLockup =
  { name :: LockupName
  , components :: Array LogoComponent
  , orientation :: Orientation
  , priority :: LockupPriority
  , variants :: VariantSet
  , contexts :: Array UsageContext
  , approvedBackgrounds :: Array BackgroundColor
  , clearSpace :: ClearSpaceRule
  , minSize :: SizeConstraint
  }

-- | Create a logo lockup.
-- |
-- | Returns Nothing if variants is empty (invariant violation).
mkLogoLockup
  :: LockupName
  -> Array LogoComponent
  -> Orientation
  -> LockupPriority
  -> VariantSet
  -> Array UsageContext
  -> Array BackgroundColor
  -> ClearSpaceRule
  -> SizeConstraint
  -> LogoLockup
mkLogoLockup name components orientation priority variants contexts backgrounds clearSpace minSize =
  { name
  , components: nub components
  , orientation
  , priority
  , variants
  , contexts: nub contexts
  , approvedBackgrounds: nub backgrounds
  , clearSpace
  , minSize
  }

-- | Get lockup name.
lockupName :: LogoLockup -> LockupName
lockupName l = l.name

-- | Get lockup components.
lockupComponents :: LogoLockup -> Array LogoComponent
lockupComponents l = l.components

-- | Get lockup orientation.
lockupOrientation :: LogoLockup -> Orientation
lockupOrientation l = l.orientation

-- | Get lockup priority.
lockupPriority :: LogoLockup -> LockupPriority
lockupPriority l = l.priority

-- | Get lockup variants.
lockupVariants :: LogoLockup -> VariantSet
lockupVariants l = l.variants

-- | Get lockup usage contexts.
lockupContexts :: LogoLockup -> Array UsageContext
lockupContexts l = l.contexts

-- | Get approved backgrounds.
lockupApprovedBackgrounds :: LogoLockup -> Array BackgroundColor
lockupApprovedBackgrounds l = l.approvedBackgrounds

-- | Get clear space rule.
lockupClearSpace :: LogoLockup -> ClearSpaceRule
lockupClearSpace l = l.clearSpace

-- | Get minimum size constraint.
lockupMinSize :: LogoLockup -> SizeConstraint
lockupMinSize l = l.minSize

-- | Show lockup (debug format).
showLogoLockup :: LogoLockup -> String
showLogoLockup l =
  "LogoLockup { name: \"" <> unLockupName l.name <> 
  "\", priority: " <> priorityToString l.priority <>
  ", orientation: " <> orientationToString l.orientation <>
  ", variants: [" <> intercalate ", " (map variantToString (variantSetToArray l.variants)) <> 
  "], contexts: " <> show (length l.contexts) <> " }"
