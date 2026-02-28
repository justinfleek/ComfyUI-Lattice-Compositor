-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // brand // token // color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color Token molecule.
-- |
-- | A ColorToken binds a semantic name to a color value. This enables
-- | agents to reference colors by meaning rather than value.
-- |
-- | ## Structure
-- |
-- | ```
-- | ColorToken = TokenMeta + OKLCH + ColorRole
-- | ```
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | primaryToken :: ColorToken
-- | primaryToken = mkColorToken
-- |   (TokenName "color.primary.500")
-- |   (TokenDesc "Primary brand color for interactive elements")
-- |   (oklch 0.65 0.24 240.0)  -- Vivid blue
-- |   RolePrimary
-- | ```
-- |
-- | ## Color Roles
-- |
-- | Colors have semantic roles that define their purpose:
-- | - **Primary**: Main brand color, interactive elements
-- | - **Secondary**: Supporting brand color
-- | - **Accent**: Highlights, calls to action
-- | - **Neutral**: Grays for text, borders, backgrounds
-- | - **Success/Warning/Error/Info**: Semantic feedback colors
-- |
-- | ## At Billion-Agent Scale
-- |
-- | When agents compose UI, they reference `color.primary.500` rather than
-- | a specific OKLCH value. The token system resolves references at render
-- | time, enabling theme switching, dark mode, and brand customization
-- | without changing component code.

module Hydrogen.Schema.Brand.Token.Color
  ( -- * ColorToken Type
    ColorToken
  , mkColorToken
  , mkColorTokenSimple
  
  -- * Accessors
  , colorTokenName
  , colorTokenDesc
  , colorTokenValue
  , colorTokenRole
  , colorTokenMeta
  
  -- * Color Roles
  , ColorRole(..)
  , roleToString
  , roleFromString
  , allRoles
  
  -- * Color Shade
  , ColorShade(..)
  , shadeToInt
  , shadeFromInt
  , allShades
  
  -- * Predefined Role Colors
  , isPrimary
  , isSecondary
  , isAccent
  , isNeutral
  , isSemantic
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (||)
  , (<>)
  , (<<<)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower, trim)

import Hydrogen.Schema.Brand.Token
  ( TokenName
  , TokenDesc
  , TokenCategory(CategoryColor)
  , TokenMeta
  , mkTokenMeta
  , mkTokenDesc
  , unTokenName
  )

import Hydrogen.Schema.Color.OKLCH (OKLCH)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color // role
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic role of a color in the design system.
-- |
-- | Roles define how a color is used, not what it looks like.
-- | A Primary color might be blue in one brand and green in another,
-- | but both serve the same semantic purpose.
data ColorRole
  = RolePrimary        -- ^ Main brand color
  | RoleSecondary      -- ^ Supporting brand color
  | RoleTertiary       -- ^ Third-tier brand color
  | RoleAccent         -- ^ Highlight, call to action
  | RoleNeutral        -- ^ Grays, text, borders
  | RoleBackground     -- ^ Page/surface backgrounds
  | RoleSurface        -- ^ Card/container backgrounds
  | RoleSuccess        -- ^ Positive feedback
  | RoleWarning        -- ^ Caution feedback
  | RoleError          -- ^ Negative feedback
  | RoleInfo           -- ^ Informational feedback
  | RoleOnPrimary      -- ^ Text/icons on primary
  | RoleOnSecondary    -- ^ Text/icons on secondary
  | RoleOnBackground   -- ^ Text on background
  | RoleOnSurface      -- ^ Text on surface
  | RoleOutline        -- ^ Borders, dividers
  | RoleScrim          -- ^ Modal overlays

derive instance eqColorRole :: Eq ColorRole
derive instance ordColorRole :: Ord ColorRole

instance showColorRole :: Show ColorRole where
  show = roleToString

-- | Convert role to string representation.
roleToString :: ColorRole -> String
roleToString = case _ of
  RolePrimary -> "primary"
  RoleSecondary -> "secondary"
  RoleTertiary -> "tertiary"
  RoleAccent -> "accent"
  RoleNeutral -> "neutral"
  RoleBackground -> "background"
  RoleSurface -> "surface"
  RoleSuccess -> "success"
  RoleWarning -> "warning"
  RoleError -> "error"
  RoleInfo -> "info"
  RoleOnPrimary -> "on-primary"
  RoleOnSecondary -> "on-secondary"
  RoleOnBackground -> "on-background"
  RoleOnSurface -> "on-surface"
  RoleOutline -> "outline"
  RoleScrim -> "scrim"

-- | Parse role from string.
roleFromString :: String -> Maybe ColorRole
roleFromString s = case toLower (trim s) of
  "primary" -> Just RolePrimary
  "secondary" -> Just RoleSecondary
  "tertiary" -> Just RoleTertiary
  "accent" -> Just RoleAccent
  "neutral" -> Just RoleNeutral
  "background" -> Just RoleBackground
  "bg" -> Just RoleBackground
  "surface" -> Just RoleSurface
  "success" -> Just RoleSuccess
  "warning" -> Just RoleWarning
  "error" -> Just RoleError
  "danger" -> Just RoleError
  "info" -> Just RoleInfo
  "on-primary" -> Just RoleOnPrimary
  "onprimary" -> Just RoleOnPrimary
  "on-secondary" -> Just RoleOnSecondary
  "onsecondary" -> Just RoleOnSecondary
  "on-background" -> Just RoleOnBackground
  "onbackground" -> Just RoleOnBackground
  "on-surface" -> Just RoleOnSurface
  "onsurface" -> Just RoleOnSurface
  "outline" -> Just RoleOutline
  "border" -> Just RoleOutline
  "scrim" -> Just RoleScrim
  "overlay" -> Just RoleScrim
  _ -> Nothing

-- | All available color roles.
allRoles :: Array ColorRole
allRoles =
  [ RolePrimary
  , RoleSecondary
  , RoleTertiary
  , RoleAccent
  , RoleNeutral
  , RoleBackground
  , RoleSurface
  , RoleSuccess
  , RoleWarning
  , RoleError
  , RoleInfo
  , RoleOnPrimary
  , RoleOnSecondary
  , RoleOnBackground
  , RoleOnSurface
  , RoleOutline
  , RoleScrim
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color // shade
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shade level within a color scale.
-- |
-- | Standard shade scale from 50 (lightest) to 950 (darkest).
-- | This follows the Tailwind CSS convention.
data ColorShade
  = Shade50
  | Shade100
  | Shade200
  | Shade300
  | Shade400
  | Shade500   -- ^ Base shade
  | Shade600
  | Shade700
  | Shade800
  | Shade900
  | Shade950

derive instance eqColorShade :: Eq ColorShade
derive instance ordColorShade :: Ord ColorShade

instance showColorShade :: Show ColorShade where
  show = show <<< shadeToInt

-- | Convert shade to numeric value.
shadeToInt :: ColorShade -> Int
shadeToInt = case _ of
  Shade50 -> 50
  Shade100 -> 100
  Shade200 -> 200
  Shade300 -> 300
  Shade400 -> 400
  Shade500 -> 500
  Shade600 -> 600
  Shade700 -> 700
  Shade800 -> 800
  Shade900 -> 900
  Shade950 -> 950

-- | Parse shade from numeric value.
shadeFromInt :: Int -> Maybe ColorShade
shadeFromInt = case _ of
  50 -> Just Shade50
  100 -> Just Shade100
  200 -> Just Shade200
  300 -> Just Shade300
  400 -> Just Shade400
  500 -> Just Shade500
  600 -> Just Shade600
  700 -> Just Shade700
  800 -> Just Shade800
  900 -> Just Shade900
  950 -> Just Shade950
  _ -> Nothing

-- | All shade levels.
allShades :: Array ColorShade
allShades =
  [ Shade50
  , Shade100
  , Shade200
  , Shade300
  , Shade400
  , Shade500
  , Shade600
  , Shade700
  , Shade800
  , Shade900
  , Shade950
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color design token.
-- |
-- | Binds a semantic name to an OKLCH color value with role metadata.
-- |
-- | ## Invariants
-- |
-- | - Name follows token naming conventions
-- | - Value is a valid OKLCH color
-- | - Role matches the intended usage
type ColorToken =
  { meta :: TokenMeta
  , value :: OKLCH
  , role :: ColorRole
  }

-- | Create a color token with full metadata.
mkColorToken :: TokenName -> TokenDesc -> OKLCH -> ColorRole -> ColorToken
mkColorToken name desc value role =
  { meta: mkTokenMeta name desc CategoryColor
  , value: value
  , role: role
  }

-- | Create a color token with minimal metadata.
-- |
-- | Description is derived from the token name.
mkColorTokenSimple :: TokenName -> OKLCH -> ColorRole -> ColorToken
mkColorTokenSimple name value role =
  let
    desc = mkTokenDesc ("Color token: " <> unTokenName name)
  in
    mkColorToken name desc value role

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the token name.
colorTokenName :: ColorToken -> TokenName
colorTokenName t = t.meta.name

-- | Get the token description.
colorTokenDesc :: ColorToken -> TokenDesc
colorTokenDesc t = t.meta.description

-- | Get the color value.
colorTokenValue :: ColorToken -> OKLCH
colorTokenValue t = t.value

-- | Get the color role.
colorTokenRole :: ColorToken -> ColorRole
colorTokenRole t = t.role

-- | Get the full metadata.
colorTokenMeta :: ColorToken -> TokenMeta
colorTokenMeta t = t.meta

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if token is a primary color.
isPrimary :: ColorToken -> Boolean
isPrimary t = t.role == RolePrimary

-- | Check if token is a secondary color.
isSecondary :: ColorToken -> Boolean
isSecondary t = t.role == RoleSecondary

-- | Check if token is an accent color.
isAccent :: ColorToken -> Boolean
isAccent t = t.role == RoleAccent

-- | Check if token is a neutral color.
isNeutral :: ColorToken -> Boolean
isNeutral t = t.role == RoleNeutral

-- | Check if token is a semantic feedback color.
isSemantic :: ColorToken -> Boolean
isSemantic t =
  t.role == RoleSuccess ||
  t.role == RoleWarning ||
  t.role == RoleError ||
  t.role == RoleInfo
