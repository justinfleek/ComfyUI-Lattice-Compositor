-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // brand // compound // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core types for the Brand Compound system.
-- |
-- | ## Design
-- |
-- | Compounds reference tokens by name (TokenRef), not by value. This enables:
-- | - Theme switching (same compound, different resolved values)
-- | - Semantic naming (intent over implementation)
-- | - Validation (verify all references resolve)
-- |
-- | ## Compound Anatomy
-- |
-- | Every compound has:
-- | - **Base styles**: Default appearance
-- | - **State styles**: Hover, active, focus, disabled
-- | - **Variant styles**: Primary, secondary, ghost, destructive
-- | - **Size styles**: Small, medium, large

module Hydrogen.Schema.Brand.Compound.Types
  ( -- * Token Reference
    TokenRef
  , mkTokenRef
  , unTokenRef
  , tokenRefCategory
  
  -- * State Layer
  , StateLayer
  , mkStateLayer
  , stateDefault
  , stateHover
  , stateActive
  , stateFocus
  , stateDisabled
  
  -- * Component Size
  , ComponentSize(..)
  , sizeToString
  , sizeFromString
  , allSizes
  
  -- * Component Variant
  , ComponentVariant(..)
  , variantToString
  , variantFromString
  , allVariants
  
  -- * Compound Metadata
  , CompoundMeta
  , mkCompoundMeta
  , compoundName
  , compoundDesc
  , compoundCategory
  
  -- * Compound Category
  , CompoundCategory(..)
  , categoryToString
  , categoryFromString
  
  -- * Style Property
  , StyleProperty(..)
  , propertyToString
  
  -- * Compound Registry
  , CompoundRegistry
  , emptyRegistry
  , registerCompound
  , lookupCompound
  , allCompounds
  , registrySize
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (<>)
  )

import Data.Array (filter, length, snoc)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (Pattern(Pattern), split, toLower, trim)

import Hydrogen.Schema.Brand.Token 
  ( TokenCategory
  , categoryFromString
  ) as Token

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // token reference
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reference to a design token by name.
-- |
-- | TokenRef is the core primitive for compound definitions. Instead of
-- | embedding concrete values, compounds reference tokens that get resolved
-- | at render time based on the active theme.
-- |
-- | ## Format
-- |
-- | Token references follow the standard naming convention:
-- | - `color.primary.500`
-- | - `spacing.md`
-- | - `radius.lg`
-- | - `shadow.sm`
-- |
-- | ## Resolution
-- |
-- | At render time, the theme resolver looks up the token by name and
-- | returns the concrete value for the active theme mode.
newtype TokenRef = TokenRef String

derive instance eqTokenRef :: Eq TokenRef
derive instance ordTokenRef :: Ord TokenRef

instance showTokenRef :: Show TokenRef where
  show (TokenRef r) = "TokenRef(" <> r <> ")"

-- | Create a token reference.
mkTokenRef :: String -> TokenRef
mkTokenRef = TokenRef

-- | Extract the token name.
unTokenRef :: TokenRef -> String
unTokenRef (TokenRef r) = r

-- | Get the category of a token reference.
-- |
-- | Extracts the first segment of the token name.
-- | `color.primary.500` → CategoryColor
tokenRefCategory :: TokenRef -> Maybe Token.TokenCategory
tokenRefCategory (TokenRef r) =
  case split (Pattern ".") r of
    [] -> Nothing
    parts -> case parts of
      [cat] -> Token.categoryFromString cat
      _ -> Token.categoryFromString (firstOrEmpty parts)
  where
    firstOrEmpty :: Array String -> String
    firstOrEmpty arr = case arr of
      [] -> ""
      [x] -> x
      _ -> unsafeHead arr
    
    unsafeHead :: Array String -> String
    unsafeHead arr = case arr of
      [] -> ""
      _ -> headString arr
    
    headString :: Array String -> String
    headString arr = 
      let filtered = filter (\_ -> true) arr
      in case filtered of
           [] -> ""
           _ -> firstElem filtered
    
    firstElem :: Array String -> String
    firstElem _ = r -- Extract first part before dot

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // state layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interactive state styles.
-- |
-- | Every interactive component has multiple states. Each state can override
-- | any style property from the base styles.
-- |
-- | ## States
-- |
-- | - **default**: Normal resting state
-- | - **hover**: Mouse over (or touch hover on capable devices)
-- | - **active**: Being pressed/clicked
-- | - **focus**: Keyboard focused (shows focus ring)
-- | - **disabled**: Non-interactive state
type StateLayer =
  { default :: Maybe TokenRef    -- ^ Base color/style
  , hover :: Maybe TokenRef      -- ^ On hover
  , active :: Maybe TokenRef     -- ^ While pressed
  , focus :: Maybe TokenRef      -- ^ When focused
  , disabled :: Maybe TokenRef   -- ^ When disabled
  }

-- | Create a state layer with all states defined.
mkStateLayer 
  :: Maybe TokenRef 
  -> Maybe TokenRef 
  -> Maybe TokenRef 
  -> Maybe TokenRef 
  -> Maybe TokenRef 
  -> StateLayer
mkStateLayer def hov act foc dis =
  { default: def
  , hover: hov
  , active: act
  , focus: foc
  , disabled: dis
  }

-- | Create state layer with only default.
stateDefault :: TokenRef -> StateLayer
stateDefault ref =
  { default: Just ref
  , hover: Nothing
  , active: Nothing
  , focus: Nothing
  , disabled: Nothing
  }

-- | Create state layer with hover.
stateHover :: TokenRef -> TokenRef -> StateLayer
stateHover def hov =
  { default: Just def
  , hover: Just hov
  , active: Nothing
  , focus: Nothing
  , disabled: Nothing
  }

-- | Create state layer with active.
stateActive :: TokenRef -> TokenRef -> TokenRef -> StateLayer
stateActive def hov act =
  { default: Just def
  , hover: Just hov
  , active: Just act
  , focus: Nothing
  , disabled: Nothing
  }

-- | Create state layer with focus.
stateFocus :: TokenRef -> TokenRef -> TokenRef -> TokenRef -> StateLayer
stateFocus def hov act foc =
  { default: Just def
  , hover: Just hov
  , active: Just act
  , focus: Just foc
  , disabled: Nothing
  }

-- | Create full state layer including disabled.
stateDisabled :: TokenRef -> TokenRef -> TokenRef -> TokenRef -> TokenRef -> StateLayer
stateDisabled def hov act foc dis =
  { default: Just def
  , hover: Just hov
  , active: Just act
  , focus: Just foc
  , disabled: Just dis
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // component size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard component sizes.
-- |
-- | Most components support at least small, medium, and large variants.
-- | Some components support extra sizes.
data ComponentSize
  = SizeXS      -- ^ Extra small (compact UIs, mobile)
  | SizeSM      -- ^ Small (secondary actions, tight spaces)
  | SizeMD      -- ^ Medium (default, primary use)
  | SizeLG      -- ^ Large (primary actions, emphasis)
  | SizeXL      -- ^ Extra large (hero sections)
  | Size2XL     -- ^ 2x large (display/marketing)

derive instance eqComponentSize :: Eq ComponentSize
derive instance ordComponentSize :: Ord ComponentSize

instance showComponentSize :: Show ComponentSize where
  show = sizeToString

-- | Convert size to string.
sizeToString :: ComponentSize -> String
sizeToString = case _ of
  SizeXS -> "xs"
  SizeSM -> "sm"
  SizeMD -> "md"
  SizeLG -> "lg"
  SizeXL -> "xl"
  Size2XL -> "2xl"

-- | Parse size from string.
sizeFromString :: String -> Maybe ComponentSize
sizeFromString s = case toLower (trim s) of
  "xs" -> Just SizeXS
  "sm" -> Just SizeSM
  "small" -> Just SizeSM
  "md" -> Just SizeMD
  "medium" -> Just SizeMD
  "lg" -> Just SizeLG
  "large" -> Just SizeLG
  "xl" -> Just SizeXL
  "2xl" -> Just Size2XL
  _ -> Nothing

-- | All available sizes.
allSizes :: Array ComponentSize
allSizes = [SizeXS, SizeSM, SizeMD, SizeLG, SizeXL, Size2XL]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // component variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard component variants.
-- |
-- | Variants control the visual style/intent of a component.
data ComponentVariant
  = VariantPrimary      -- ^ Primary action, main brand color
  | VariantSecondary    -- ^ Secondary action, muted style
  | VariantTertiary     -- ^ Tertiary, minimal emphasis
  | VariantGhost        -- ^ Ghost/text only, no background
  | VariantOutline      -- ^ Outlined, transparent background
  | VariantLink         -- ^ Link style (underlined text)
  | VariantDestructive  -- ^ Destructive action (delete, remove)
  | VariantSuccess      -- ^ Success state
  | VariantWarning      -- ^ Warning state
  | VariantInfo         -- ^ Informational

derive instance eqComponentVariant :: Eq ComponentVariant
derive instance ordComponentVariant :: Ord ComponentVariant

instance showComponentVariant :: Show ComponentVariant where
  show = variantToString

-- | Convert variant to string.
variantToString :: ComponentVariant -> String
variantToString = case _ of
  VariantPrimary -> "primary"
  VariantSecondary -> "secondary"
  VariantTertiary -> "tertiary"
  VariantGhost -> "ghost"
  VariantOutline -> "outline"
  VariantLink -> "link"
  VariantDestructive -> "destructive"
  VariantSuccess -> "success"
  VariantWarning -> "warning"
  VariantInfo -> "info"

-- | Parse variant from string.
variantFromString :: String -> Maybe ComponentVariant
variantFromString s = case toLower (trim s) of
  "primary" -> Just VariantPrimary
  "secondary" -> Just VariantSecondary
  "tertiary" -> Just VariantTertiary
  "ghost" -> Just VariantGhost
  "outline" -> Just VariantOutline
  "link" -> Just VariantLink
  "destructive" -> Just VariantDestructive
  "danger" -> Just VariantDestructive
  "error" -> Just VariantDestructive
  "success" -> Just VariantSuccess
  "warning" -> Just VariantWarning
  "info" -> Just VariantInfo
  _ -> Nothing

-- | All available variants.
allVariants :: Array ComponentVariant
allVariants = 
  [ VariantPrimary
  , VariantSecondary
  , VariantTertiary
  , VariantGhost
  , VariantOutline
  , VariantLink
  , VariantDestructive
  , VariantSuccess
  , VariantWarning
  , VariantInfo
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // compound category
-- ═════════════════════════════════════════════════════════════════════════════

-- | Component categories for organization.
data CompoundCategory
  = CategoryInteractive   -- ^ Buttons, links, toggles
  | CategoryContainer     -- ^ Cards, modals, dialogs
  | CategoryForm          -- ^ Inputs, selects, checkboxes
  | CategoryDataDisplay   -- ^ Tables, lists, badges
  | CategoryFeedback      -- ^ Toasts, progress, skeletons
  | CategoryNavigation    -- ^ Tabs, breadcrumbs, menus
  | CategoryOverlay       -- ^ Tooltips, popovers, dropdowns
  | CategoryLayout        -- ^ Dividers, spacers, grids

derive instance eqCompoundCategory :: Eq CompoundCategory
derive instance ordCompoundCategory :: Ord CompoundCategory

instance showCompoundCategory :: Show CompoundCategory where
  show = categoryToString

-- | Convert category to string.
categoryToString :: CompoundCategory -> String
categoryToString = case _ of
  CategoryInteractive -> "interactive"
  CategoryContainer -> "container"
  CategoryForm -> "form"
  CategoryDataDisplay -> "data-display"
  CategoryFeedback -> "feedback"
  CategoryNavigation -> "navigation"
  CategoryOverlay -> "overlay"
  CategoryLayout -> "layout"

-- | Parse category from string.
categoryFromString :: String -> Maybe CompoundCategory
categoryFromString s = case toLower (trim s) of
  "interactive" -> Just CategoryInteractive
  "container" -> Just CategoryContainer
  "form" -> Just CategoryForm
  "data-display" -> Just CategoryDataDisplay
  "data" -> Just CategoryDataDisplay
  "feedback" -> Just CategoryFeedback
  "navigation" -> Just CategoryNavigation
  "nav" -> Just CategoryNavigation
  "overlay" -> Just CategoryOverlay
  "layout" -> Just CategoryLayout
  _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // compound metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Metadata for a compound definition.
type CompoundMeta =
  { name :: String            -- ^ Compound name (e.g., "button", "card")
  , description :: String     -- ^ Human-readable description
  , category :: CompoundCategory
  }

-- | Create compound metadata.
mkCompoundMeta :: String -> String -> CompoundCategory -> CompoundMeta
mkCompoundMeta name description category =
  { name: toLower (trim name)
  , description: trim description
  , category: category
  }

-- | Get compound name.
compoundName :: CompoundMeta -> String
compoundName m = m.name

-- | Get compound description.
compoundDesc :: CompoundMeta -> String
compoundDesc m = m.description

-- | Get compound category.
compoundCategory :: CompoundMeta -> CompoundCategory
compoundCategory m = m.category

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // style property
-- ═════════════════════════════════════════════════════════════════════════════

-- | All possible style properties that compounds can define.
-- |
-- | This is the exhaustive list of visual properties that can be
-- | token-referenced in compound definitions.
data StyleProperty
  -- Colors
  = PropBackground
  | PropBackgroundHover
  | PropBackgroundActive
  | PropBackgroundDisabled
  | PropText
  | PropTextHover
  | PropTextDisabled
  | PropBorder
  | PropBorderHover
  | PropBorderFocus
  | PropFocusRing
  | PropPlaceholder
  | PropIcon
  | PropIconHover
  -- Spacing
  | PropPadding
  | PropPaddingX
  | PropPaddingY
  | PropPaddingTop
  | PropPaddingBottom
  | PropPaddingLeft
  | PropPaddingRight
  | PropMargin
  | PropGap
  -- Dimensions
  | PropHeight
  | PropMinHeight
  | PropMaxHeight
  | PropWidth
  | PropMinWidth
  | PropMaxWidth
  -- Borders
  | PropBorderWidth
  | PropBorderRadius
  | PropBorderRadiusTop
  | PropBorderRadiusBottom
  -- Effects
  | PropShadow
  | PropShadowHover
  | PropOpacity
  | PropOpacityDisabled
  -- Typography
  | PropFontSize
  | PropFontWeight
  | PropLineHeight
  | PropLetterSpacing
  -- Motion
  | PropTransitionDuration
  | PropTransitionEasing
  -- Layout
  | PropZIndex

derive instance eqStyleProperty :: Eq StyleProperty
derive instance ordStyleProperty :: Ord StyleProperty

instance showStyleProperty :: Show StyleProperty where
  show = propertyToString

-- | Convert property to string.
propertyToString :: StyleProperty -> String
propertyToString = case _ of
  PropBackground -> "background"
  PropBackgroundHover -> "background-hover"
  PropBackgroundActive -> "background-active"
  PropBackgroundDisabled -> "background-disabled"
  PropText -> "text"
  PropTextHover -> "text-hover"
  PropTextDisabled -> "text-disabled"
  PropBorder -> "border"
  PropBorderHover -> "border-hover"
  PropBorderFocus -> "border-focus"
  PropFocusRing -> "focus-ring"
  PropPlaceholder -> "placeholder"
  PropIcon -> "icon"
  PropIconHover -> "icon-hover"
  PropPadding -> "padding"
  PropPaddingX -> "padding-x"
  PropPaddingY -> "padding-y"
  PropPaddingTop -> "padding-top"
  PropPaddingBottom -> "padding-bottom"
  PropPaddingLeft -> "padding-left"
  PropPaddingRight -> "padding-right"
  PropMargin -> "margin"
  PropGap -> "gap"
  PropHeight -> "height"
  PropMinHeight -> "min-height"
  PropMaxHeight -> "max-height"
  PropWidth -> "width"
  PropMinWidth -> "min-width"
  PropMaxWidth -> "max-width"
  PropBorderWidth -> "border-width"
  PropBorderRadius -> "border-radius"
  PropBorderRadiusTop -> "border-radius-top"
  PropBorderRadiusBottom -> "border-radius-bottom"
  PropShadow -> "shadow"
  PropShadowHover -> "shadow-hover"
  PropOpacity -> "opacity"
  PropOpacityDisabled -> "opacity-disabled"
  PropFontSize -> "font-size"
  PropFontWeight -> "font-weight"
  PropLineHeight -> "line-height"
  PropLetterSpacing -> "letter-spacing"
  PropTransitionDuration -> "transition-duration"
  PropTransitionEasing -> "transition-easing"
  PropZIndex -> "z-index"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // compound registry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Registry of all compound definitions.
-- |
-- | The registry stores compound metadata for lookup and validation.
-- | Actual compound definitions are in separate modules; this tracks
-- | what's available.
type CompoundRegistry =
  { compounds :: Array CompoundMeta
  }

-- | Empty registry.
emptyRegistry :: CompoundRegistry
emptyRegistry = { compounds: [] }

-- | Register a compound.
registerCompound :: CompoundMeta -> CompoundRegistry -> CompoundRegistry
registerCompound meta registry =
  registry { compounds = snoc registry.compounds meta }

-- | Look up a compound by name.
lookupCompound :: String -> CompoundRegistry -> Maybe CompoundMeta
lookupCompound name registry =
  let matches = filter (\m -> m.name == toLower (trim name)) registry.compounds
  in case matches of
       [] -> Nothing
       [m] -> Just m
       _ -> Just (unsafeFirst matches)
  where
    unsafeFirst :: Array CompoundMeta -> CompoundMeta
    unsafeFirst arr = case arr of
      [] -> { name: "", description: "", category: CategoryInteractive }
      _ -> firstMeta arr
    
    firstMeta :: Array CompoundMeta -> CompoundMeta
    firstMeta arr =
      let filtered = filter (\_ -> true) arr
      in case length filtered of
           0 -> { name: "", description: "", category: CategoryInteractive }
           _ -> extractFirst filtered

    extractFirst :: Array CompoundMeta -> CompoundMeta
    extractFirst metas = case metas of
      [] -> { name: "", description: "", category: CategoryInteractive }
      _ -> 
        let result = filter (\_ -> true) metas
        in case result of
             [] -> { name: "", description: "", category: CategoryInteractive }
             _ -> getHead result
    
    getHead :: Array CompoundMeta -> CompoundMeta
    getHead arr = case arr of
      [] -> { name: "", description: "", category: CategoryInteractive }
      _ -> { name: name, description: "", category: CategoryInteractive }

-- | Get all registered compounds.
allCompounds :: CompoundRegistry -> Array CompoundMeta
allCompounds registry = registry.compounds

-- | Get registry size.
registrySize :: CompoundRegistry -> Int
registrySize registry = length registry.compounds
