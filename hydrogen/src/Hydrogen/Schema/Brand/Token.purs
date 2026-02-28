-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // brand // token
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Design Token Infrastructure.
-- |
-- | Design tokens are the atomic units of a design system. They are named values
-- | with semantic meaning that can be referenced, composed, and exported to
-- | various formats (CSS custom properties, Figma variables, etc.).
-- |
-- | ## Token Anatomy
-- |
-- | Every token has:
-- | - **Name**: Semantic identifier (e.g., "color.primary.500")
-- | - **Description**: Human-readable explanation
-- | - **Category**: Grouping for organization (e.g., "color", "spacing")
-- | - **Value**: The actual design primitive (Color, Dimension, etc.)
-- |
-- | ## Token Categories
-- |
-- | Standard categories follow the pillar structure:
-- | - `color` — Color values (OKLCH, sRGB, etc.)
-- | - `spacing` — Spacing values (padding, margin, gap)
-- | - `size` — Dimension values (width, height)
-- | - `radius` — Corner radius values
-- | - `shadow` — Shadow definitions
-- | - `type` — Typography (font, size, weight, line-height)
-- | - `duration` — Animation/transition timing
-- | - `easing` — Easing curves
-- | - `zindex` — Stacking order
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Tokens enable deterministic composition. When Agent A creates a button
-- | referencing `color.primary.500`, Agent B knows exactly what color that is.
-- | The token name is the contract; the value is the implementation.

module Hydrogen.Schema.Brand.Token
  ( -- * Token Name
    TokenName
  , mkTokenName
  , unTokenName
  , tokenNameFromParts
  , tokenNameParts
  
  -- * Token Description
  , TokenDesc
  , mkTokenDesc
  , unTokenDesc
  
  -- * Token Category
  , TokenCategory(..)
  , categoryToString
  , categoryFromString
  , allCategories
  
  -- * Token Metadata
  , TokenMeta
  , mkTokenMeta
  , metaName
  , metaDesc
  , metaCategory
  
  -- * Token Naming Conventions
  , isValidTokenName
  , normalizeTokenName
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (&&)
  , (||)
  , (<>)
  , (<)
  , (<=)
  , (>=)
  , (<<<)
  , (-)
  , not
  , otherwise
  , map
  )

import Data.Array (filter, intercalate, length)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (Pattern(Pattern), split, toLower, trim)
import Data.String.CodeUnits (charAt, toCharArray)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // token // name
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic token identifier.
-- |
-- | Token names follow a hierarchical dot-notation:
-- | - `color.primary.500`
-- | - `spacing.md`
-- | - `type.heading.h1`
-- |
-- | ## Naming Conventions
-- |
-- | - Use lowercase letters, numbers, and dots only
-- | - No leading or trailing dots
-- | - No consecutive dots
-- | - Minimum 2 characters, maximum 128 characters
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | mkTokenName "color.primary.500"    -- Just (TokenName "color.primary.500")
-- | mkTokenName "invalid..name"        -- Nothing (consecutive dots)
-- | mkTokenName ""                     -- Nothing (too short)
-- | ```
newtype TokenName = TokenName String

derive instance eqTokenName :: Eq TokenName
derive instance ordTokenName :: Ord TokenName

instance showTokenName :: Show TokenName where
  show (TokenName n) = "TokenName(" <> show n <> ")"

-- | Create a token name with validation.
-- |
-- | Returns Nothing if the name doesn't follow naming conventions.
mkTokenName :: String -> Maybe TokenName
mkTokenName s
  | isValidTokenName s = Just (TokenName (normalizeTokenName s))
  | otherwise = Nothing

-- | Extract the raw string.
unTokenName :: TokenName -> String
unTokenName (TokenName n) = n

-- | Create a token name from hierarchical parts.
-- |
-- | ```purescript
-- | tokenNameFromParts ["color", "primary", "500"]
-- |   -- Just (TokenName "color.primary.500")
-- | ```
tokenNameFromParts :: Array String -> Maybe TokenName
tokenNameFromParts parts
  | length parts < 1 = Nothing
  | otherwise = mkTokenName (intercalate "." (map trim parts))

-- | Split a token name into its hierarchical parts.
-- |
-- | ```purescript
-- | tokenNameParts (TokenName "color.primary.500")
-- |   -- ["color", "primary", "500"]
-- | ```
tokenNameParts :: TokenName -> Array String
tokenNameParts (TokenName n) = split (Pattern ".") n

-- | Check if a string is a valid token name.
-- |
-- | Valid names:
-- | - 2-128 characters
-- | - Lowercase letters, numbers, dots, hyphens only
-- | - No leading/trailing dots
-- | - No consecutive dots
isValidTokenName :: String -> Boolean
isValidTokenName s =
  let
    trimmed = trim s
    chars = toCharArray trimmed
    len = length chars
    
    isValidChar :: Char -> Boolean
    isValidChar c = isLowerCase c || isDigit c || c == '.' || c == '-'
    
    isLowerCase :: Char -> Boolean
    isLowerCase c = c >= 'a' && c <= 'z'
    
    isDigit :: Char -> Boolean
    isDigit c = c >= '0' && c <= '9'
    
    allValid = length (filter (not <<< isValidChar) chars) == 0
    
    startsWithDot = charAt 0 trimmed == Just '.'
    endsWithDot = charAt (len - 1) trimmed == Just '.'
    
    hasConsecutiveDots = containsSubstring ".." trimmed
  in
    len >= 2 && len <= 128 &&
    allValid &&
    not startsWithDot &&
    not endsWithDot &&
    not hasConsecutiveDots

-- | Normalize a token name (lowercase, trimmed).
normalizeTokenName :: String -> String
normalizeTokenName = toLower <<< trim

-- | Check if string contains substring (helper).
containsSubstring :: String -> String -> Boolean
containsSubstring needle haystack =
  let parts = split (Pattern needle) haystack
  in length parts >= 2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // token // description
-- ═════════════════════════════════════════════════════════════════════════════

-- | Human-readable token description.
-- |
-- | Descriptions should explain the semantic purpose of the token,
-- | not just describe its value.
-- |
-- | ## Good Descriptions
-- |
-- | - "Primary brand color for interactive elements"
-- | - "Standard spacing between form fields"
-- | - "Heading font size for section titles"
-- |
-- | ## Bad Descriptions
-- |
-- | - "Blue color" (describes value, not purpose)
-- | - "16px" (just restates the value)
newtype TokenDesc = TokenDesc String

derive instance eqTokenDesc :: Eq TokenDesc
derive instance ordTokenDesc :: Ord TokenDesc

instance showTokenDesc :: Show TokenDesc where
  show (TokenDesc d) = "TokenDesc(" <> show d <> ")"

-- | Create a token description.
-- |
-- | Empty descriptions are allowed but discouraged.
mkTokenDesc :: String -> TokenDesc
mkTokenDesc = TokenDesc <<< trim

-- | Extract the raw string.
unTokenDesc :: TokenDesc -> String
unTokenDesc (TokenDesc d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // token // category
-- ═════════════════════════════════════════════════════════════════════════════

-- | Token category for organization and filtering.
-- |
-- | Categories correspond to design system pillars. Each category
-- | has its own token type (ColorToken, SpacingToken, etc.).
data TokenCategory
  = CategoryColor      -- ^ Color values
  | CategorySpacing    -- ^ Spacing (padding, margin, gap)
  | CategorySize       -- ^ Dimensions (width, height)
  | CategoryRadius     -- ^ Corner radius
  | CategoryShadow     -- ^ Shadow definitions
  | CategoryType       -- ^ Typography
  | CategoryDuration   -- ^ Animation timing
  | CategoryEasing     -- ^ Easing curves
  | CategoryZIndex     -- ^ Stacking order
  | CategoryOpacity    -- ^ Opacity/alpha values
  | CategoryBorder     -- ^ Border definitions
  | CategoryMotion     -- ^ Animation/motion definitions
  | CategoryBreakpoint -- ^ Responsive breakpoints
  | CategoryAsset      -- ^ Asset references (icons, images)

derive instance eqTokenCategory :: Eq TokenCategory
derive instance ordTokenCategory :: Ord TokenCategory

instance showTokenCategory :: Show TokenCategory where
  show = categoryToString

-- | Convert category to string representation.
categoryToString :: TokenCategory -> String
categoryToString = case _ of
  CategoryColor -> "color"
  CategorySpacing -> "spacing"
  CategorySize -> "size"
  CategoryRadius -> "radius"
  CategoryShadow -> "shadow"
  CategoryType -> "type"
  CategoryDuration -> "duration"
  CategoryEasing -> "easing"
  CategoryZIndex -> "zindex"
  CategoryOpacity -> "opacity"
  CategoryBorder -> "border"
  CategoryMotion -> "motion"
  CategoryBreakpoint -> "breakpoint"
  CategoryAsset -> "asset"

-- | Parse category from string.
categoryFromString :: String -> Maybe TokenCategory
categoryFromString s = case toLower (trim s) of
  "color" -> Just CategoryColor
  "spacing" -> Just CategorySpacing
  "size" -> Just CategorySize
  "radius" -> Just CategoryRadius
  "shadow" -> Just CategoryShadow
  "type" -> Just CategoryType
  "typography" -> Just CategoryType
  "duration" -> Just CategoryDuration
  "easing" -> Just CategoryEasing
  "zindex" -> Just CategoryZIndex
  "z-index" -> Just CategoryZIndex
  "opacity" -> Just CategoryOpacity
  "alpha" -> Just CategoryOpacity
  "border" -> Just CategoryBorder
  "motion" -> Just CategoryMotion
  "animation" -> Just CategoryMotion
  "breakpoint" -> Just CategoryBreakpoint
  "responsive" -> Just CategoryBreakpoint
  "asset" -> Just CategoryAsset
  "icon" -> Just CategoryAsset
  "image" -> Just CategoryAsset
  _ -> Nothing

-- | All available categories.
allCategories :: Array TokenCategory
allCategories =
  [ CategoryColor
  , CategorySpacing
  , CategorySize
  , CategoryRadius
  , CategoryShadow
  , CategoryType
  , CategoryDuration
  , CategoryEasing
  , CategoryZIndex
  , CategoryOpacity
  , CategoryBorder
  , CategoryMotion
  , CategoryBreakpoint
  , CategoryAsset
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // token // metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Token metadata (name + description + category).
-- |
-- | This is the common structure shared by all token types.
-- | Specific token types (ColorToken, SpacingToken, etc.) compose
-- | this with their value type.
type TokenMeta =
  { name :: TokenName
  , description :: TokenDesc
  , category :: TokenCategory
  }

-- | Create token metadata.
mkTokenMeta :: TokenName -> TokenDesc -> TokenCategory -> TokenMeta
mkTokenMeta n d c =
  { name: n
  , description: d
  , category: c
  }

-- | Get token name from metadata.
metaName :: TokenMeta -> TokenName
metaName m = m.name

-- | Get token description from metadata.
metaDesc :: TokenMeta -> TokenDesc
metaDesc m = m.description

-- | Get token category from metadata.
metaCategory :: TokenMeta -> TokenCategory
metaCategory m = m.category
