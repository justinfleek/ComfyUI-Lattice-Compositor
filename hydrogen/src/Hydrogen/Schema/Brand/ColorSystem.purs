-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // brand // color-system
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color System Compound.
-- |
-- | A ColorSystem organizes all color tokens in a design system into
-- | semantic layers:
-- |
-- | ## Layers
-- |
-- | 1. **Primitive Colors** — Raw color values with numeric names
-- |    (blue-500, gray-100, red-700)
-- |
-- | 2. **Semantic Colors** — Contextual meanings
-- |    (primary, secondary, success, error)
-- |
-- | 3. **Component Colors** — UI-specific assignments
-- |    (button-bg, card-border, input-focus)
-- |
-- | 4. **State Colors** — Interactive state variants
-- |    (button-hover, link-active, input-disabled)
-- |
-- | ## Theme Modes
-- |
-- | Color systems support multiple palettes:
-- | - Light mode (default)
-- | - Dark mode
-- | - High contrast (accessibility)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Color systems enable deterministic theming. An agent building a button
-- | references `color.button.background` — the color system resolves this
-- | to the appropriate value for the current theme mode.

module Hydrogen.Schema.Brand.ColorSystem
  ( -- * ColorSystem Type
    ColorSystem
  , mkColorSystem
  , emptyColorSystem
  
  -- * Accessors
  , primitiveColors
  , semanticColors
  , componentColors
  , stateColors
  , colorSystemSize
  , colorSystemDisplay
  
  -- * Color Palettes
  , ColorPalette
  , mkColorPalette
  , paletteMode
  , paletteColors
  , paletteSize
  , getPaletteColor
  , hasPaletteColor
  
  -- * Palette Mode
  , PaletteMode(..)
  , paletteModeToString
  , paletteModeFromString
  , allPaletteModes
  
  -- * Multi-Mode System
  , ThemedColorSystem
  , mkThemedColorSystem
  , lightPalette
  , darkPalette
  , contrastPalette
  , getPaletteForMode
  , resolveColor
  
  -- * Shade Scale
  , ShadeScale
  , mkShadeScale
  , shadeScaleName
  , getShade
  , allShades
  , shadeCount
  
  -- * Color Filtering
  , filterByRole
  , getColorsByRole
  , createColorToken
  , getColorValue
  , sortPaletteByName
  
  -- * Palette Operations
  , mergePalettes
  , insertColorAt
  , firstColor
  , restColors
  
  -- * Shade Scale Generation
  , standardShadeScale
  , standardShades
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, EQ, GT)
  , show
  , compare
  , bind
  , (==)
  , (<)
  , (+)
  , (<>)
  , map
  , otherwise
  )

import Data.Array (filter, foldl, head, insertAt, length, tail)
import Data.Array (sortBy) as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower, trim)

import Hydrogen.Schema.Brand.Token (TokenName, mkTokenDesc, unTokenName)
import Hydrogen.Schema.Brand.Token.Color 
  ( ColorToken
  , ColorRole
  , ColorShade(..)
  , colorTokenName
  , colorTokenRole
  , mkColorToken
  )
import Hydrogen.Schema.Color.OKLCH (OKLCH)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // palette // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Theme mode for color palettes.
data PaletteMode
  = ModeLight       -- ^ Light mode (default)
  | ModeDark        -- ^ Dark mode
  | ModeContrast    -- ^ High contrast (accessibility)
  | ModeCustom String  -- ^ Custom named mode

derive instance eqPaletteMode :: Eq PaletteMode

instance ordPaletteMode :: Ord PaletteMode where
  compare ModeLight ModeLight = EQ
  compare ModeLight _ = LT
  compare ModeDark ModeLight = GT
  compare ModeDark ModeDark = EQ
  compare ModeDark _ = LT
  compare ModeContrast ModeLight = GT
  compare ModeContrast ModeDark = GT
  compare ModeContrast ModeContrast = EQ
  compare ModeContrast _ = LT
  compare (ModeCustom a) (ModeCustom b) = compareStrings a b
  compare (ModeCustom _) _ = GT

-- | Compare strings lexicographically.
compareStrings :: String -> String -> Ordering
compareStrings a b
  | a == b = EQ
  | a < b = LT
  | otherwise = GT

instance showPaletteMode :: Show PaletteMode where
  show = paletteModeToString

-- | Convert mode to string.
paletteModeToString :: PaletteMode -> String
paletteModeToString = case _ of
  ModeLight -> "light"
  ModeDark -> "dark"
  ModeContrast -> "contrast"
  ModeCustom name -> name

-- | Parse mode from string.
paletteModeFromString :: String -> PaletteMode
paletteModeFromString s = case toLower (trim s) of
  "light" -> ModeLight
  "dark" -> ModeDark
  "contrast" -> ModeContrast
  "high-contrast" -> ModeContrast
  name -> ModeCustom name

-- | All standard palette modes.
allPaletteModes :: Array PaletteMode
allPaletteModes = [ModeLight, ModeDark, ModeContrast]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // color // palette
-- ═════════════════════════════════════════════════════════════════════════════

-- | A palette of color tokens for a specific mode.
type ColorPalette =
  { mode :: PaletteMode
  , colors :: Array ColorToken
  }

-- | Create a color palette.
mkColorPalette :: PaletteMode -> Array ColorToken -> ColorPalette
mkColorPalette mode colors =
  { mode: mode
  , colors: colors
  }

-- | Get palette mode.
paletteMode :: ColorPalette -> PaletteMode
paletteMode p = p.mode

-- | Get all colors in palette.
paletteColors :: ColorPalette -> Array ColorToken
paletteColors p = p.colors

-- | Get number of colors in palette.
paletteSize :: ColorPalette -> Int
paletteSize p = length p.colors

-- | Get a color from palette by name.
getPaletteColor :: TokenName -> ColorPalette -> Maybe ColorToken
getPaletteColor name p =
  case filter (\c -> unTokenName (colorTokenName c) == unTokenName name) p.colors of
    [c] -> Just c
    _ -> Nothing

-- | Check if palette contains a color.
hasPaletteColor :: TokenName -> ColorPalette -> Boolean
hasPaletteColor name p = case getPaletteColor name p of
  Just _ -> true
  Nothing -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // shade // scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | A scale of shades for a single color (e.g., primary-50 through primary-950).
type ShadeScale =
  { name :: String                            -- ^ Scale name (e.g., "primary")
  , shades :: Array { shade :: ColorShade, token :: ColorToken }
  }

-- | Create a shade scale.
mkShadeScale :: String -> Array { shade :: ColorShade, token :: ColorToken } -> ShadeScale
mkShadeScale name shades =
  { name: name
  , shades: shades
  }

-- | Get scale name.
shadeScaleName :: ShadeScale -> String
shadeScaleName s = s.name

-- | Get a specific shade from the scale.
getShade :: ColorShade -> ShadeScale -> Maybe ColorToken
getShade shade scale =
  case filter (\s -> s.shade == shade) scale.shades of
    [s] -> Just s.token
    _ -> Nothing

-- | Get all shades in the scale.
allShades :: ShadeScale -> Array ColorToken
allShades scale = map (\s -> s.token) scale.shades

-- | Get number of shades in the scale.
shadeCount :: ShadeScale -> Int
shadeCount scale = length scale.shades

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // color // system
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete color system with semantic organization.
-- |
-- | Organizes colors into layers for progressive abstraction.
type ColorSystem =
  { primitive :: Array ColorToken   -- ^ Raw values (blue-500, gray-100)
  , semantic :: Array ColorToken    -- ^ Contextual (primary, success)
  , component :: Array ColorToken   -- ^ UI-specific (button-bg, card-border)
  , state :: Array ColorToken       -- ^ Interactive (hover, active, disabled)
  }

-- | Create a color system with all layers.
mkColorSystem 
  :: Array ColorToken  -- ^ Primitive colors
  -> Array ColorToken  -- ^ Semantic colors
  -> Array ColorToken  -- ^ Component colors
  -> Array ColorToken  -- ^ State colors
  -> ColorSystem
mkColorSystem primitive semantic component state =
  { primitive: primitive
  , semantic: semantic
  , component: component
  , state: state
  }

-- | Create an empty color system.
emptyColorSystem :: ColorSystem
emptyColorSystem =
  { primitive: []
  , semantic: []
  , component: []
  , state: []
  }

-- | Get primitive colors.
primitiveColors :: ColorSystem -> Array ColorToken
primitiveColors cs = cs.primitive

-- | Get semantic colors.
semanticColors :: ColorSystem -> Array ColorToken
semanticColors cs = cs.semantic

-- | Get component colors.
componentColors :: ColorSystem -> Array ColorToken
componentColors cs = cs.component

-- | Get state colors.
stateColors :: ColorSystem -> Array ColorToken
stateColors cs = cs.state

-- | Get total number of colors in system.
colorSystemSize :: ColorSystem -> Int
colorSystemSize cs = 
  length cs.primitive + 
  length cs.semantic + 
  length cs.component + 
  length cs.state

-- | Display color system summary.
colorSystemDisplay :: ColorSystem -> String
colorSystemDisplay cs =
  "ColorSystem(" <>
  show (length cs.primitive) <> " primitive, " <>
  show (length cs.semantic) <> " semantic, " <>
  show (length cs.component) <> " component, " <>
  show (length cs.state) <> " state)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // themed // color // system
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color system with multiple theme modes.
-- |
-- | Supports light, dark, and high-contrast modes with automatic
-- | resolution based on current theme.
type ThemedColorSystem =
  { light :: ColorPalette
  , dark :: ColorPalette
  , contrast :: ColorPalette
  , custom :: Array ColorPalette  -- ^ Additional custom modes
  }

-- | Create a themed color system.
mkThemedColorSystem 
  :: ColorPalette  -- ^ Light mode
  -> ColorPalette  -- ^ Dark mode
  -> ColorPalette  -- ^ High contrast mode
  -> ThemedColorSystem
mkThemedColorSystem light dark contrast =
  { light: light
  , dark: dark
  , contrast: contrast
  , custom: []
  }

-- | Get light palette.
lightPalette :: ThemedColorSystem -> ColorPalette
lightPalette tcs = tcs.light

-- | Get dark palette.
darkPalette :: ThemedColorSystem -> ColorPalette
darkPalette tcs = tcs.dark

-- | Get contrast palette.
contrastPalette :: ThemedColorSystem -> ColorPalette
contrastPalette tcs = tcs.contrast

-- | Get palette for a specific mode.
getPaletteForMode :: PaletteMode -> ThemedColorSystem -> Maybe ColorPalette
getPaletteForMode mode tcs = case mode of
  ModeLight -> Just tcs.light
  ModeDark -> Just tcs.dark
  ModeContrast -> Just tcs.contrast
  ModeCustom name -> 
    case filter (\p -> paletteModeToString p.mode == name) tcs.custom of
      [p] -> Just p
      _ -> Nothing

-- | Resolve a color token name to a value for a specific mode.
-- |
-- | This is the key function for theme-aware rendering. Given a token
-- | name like "color.button.background" and a mode like ModeDark,
-- | returns the appropriate OKLCH value for dark mode.
resolveColor :: TokenName -> PaletteMode -> ThemedColorSystem -> Maybe ColorToken
resolveColor name mode tcs = do
  palette <- getPaletteForMode mode tcs
  getPaletteColor name palette

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // color // filtering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter colors by role.
-- |
-- | Returns all colors in the palette that have the specified role.
-- | Useful for finding all primary colors, all semantic colors, etc.
filterByRole :: ColorRole -> Array ColorToken -> Array ColorToken
filterByRole role tokens = filter (\t -> colorTokenRole t == role) tokens

-- | Get colors by role from a palette.
-- |
-- | Convenience function combining palette access and role filtering.
getColorsByRole :: ColorRole -> ColorPalette -> Array ColorToken
getColorsByRole role palette = filterByRole role (paletteColors palette)

-- | Create a new color token.
-- |
-- | Convenience function for creating tokens with full metadata.
-- | Uses the color system's token creation infrastructure.
createColorToken :: TokenName -> String -> OKLCH -> ColorRole -> ColorToken
createColorToken name description value role =
  mkColorToken name (mkTokenDesc description) value role

-- | Get the OKLCH value from a color token.
-- |
-- | Extracts the raw color value for use in rendering or calculations.
getColorValue :: ColorToken -> OKLCH
getColorValue t = t.value

-- | Sort a palette by token name.
-- |
-- | Returns colors sorted lexicographically by name for consistent ordering.
sortPaletteByName :: ColorPalette -> Array ColorToken
sortPaletteByName palette = Array.sortBy compareTokenNames (paletteColors palette)
  where
  compareTokenNames :: ColorToken -> ColorToken -> Ordering
  compareTokenNames a b = compare (unTokenName (colorTokenName a)) (unTokenName (colorTokenName b))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // palette // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Merge two palettes, combining all colors.
-- |
-- | Uses foldl to accumulate colors from the second palette into the first.
-- | The resulting palette uses the mode from the first palette.
-- | Duplicate token names are kept (no deduplication).
mergePalettes :: ColorPalette -> ColorPalette -> ColorPalette
mergePalettes base addition =
  { mode: base.mode
  , colors: foldl (\acc c -> acc <> [c]) base.colors addition.colors
  }

-- | Insert a color at a specific position in a palette.
-- |
-- | If index is out of bounds, appends to the end.
-- | Returns the modified palette.
insertColorAt :: Int -> ColorToken -> ColorPalette -> ColorPalette
insertColorAt index token palette =
  case insertAt index token palette.colors of
    Just newColors -> { mode: palette.mode, colors: newColors }
    Nothing -> { mode: palette.mode, colors: palette.colors <> [token] }

-- | Get the first color from a palette.
-- |
-- | Returns Nothing for empty palettes.
firstColor :: ColorPalette -> Maybe ColorToken
firstColor palette = head palette.colors

-- | Get all colors except the first.
-- |
-- | Returns Nothing for empty palettes.
restColors :: ColorPalette -> Maybe (Array ColorToken)
restColors palette = tail palette.colors

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // shade // scale // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard shade levels used in design systems.
-- |
-- | Returns the 11 standard shade levels from 50 (lightest) to 950 (darkest).
-- | These correspond to common naming conventions (e.g., blue-500, gray-100).
standardShades :: Array ColorShade
standardShades =
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

-- | Create a standard shade scale from a base color.
-- |
-- | Given a name and a generator function that produces colors for each shade,
-- | creates a complete ShadeScale with all 11 standard shades.
-- |
-- | Example usage:
-- | ```purescript
-- | primaryScale = standardShadeScale "primary" generatePrimaryShade
-- | where
-- |   generatePrimaryShade Shade500 = mkColorToken "primary-500" ...
-- |   ...
-- | ```
standardShadeScale 
  :: String 
  -> (ColorShade -> ColorToken) 
  -> ShadeScale
standardShadeScale name generateToken =
  { name: name
  , shades: map (\s -> { shade: s, token: generateToken s }) standardShades
  }
