-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // brand // token // shadow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shadow Token molecule.
-- |
-- | A ShadowToken binds a semantic name to a shadow definition.
-- | Shadow tokens define elevation and depth in the design system.
-- |
-- | ## Structure
-- |
-- | ```
-- | ShadowToken = TokenMeta + ShadowValue + ElevationLevel
-- | ```
-- |
-- | ## Elevation Scale
-- |
-- | - `shadow.none` = no shadow (elevation 0)
-- | - `shadow.sm` = subtle lift (elevation 1)
-- | - `shadow.md` = standard card (elevation 2)
-- | - `shadow.lg` = raised element (elevation 3)
-- | - `shadow.xl` = floating element (elevation 4)
-- | - `shadow.2xl` = modal/overlay (elevation 5)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Shadows communicate hierarchy. When agents use semantic elevation
-- | tokens, the visual hierarchy remains consistent even when shadows
-- | are customized for different themes or contexts.

module Hydrogen.Schema.Brand.Token.Shadow
  ( -- * ShadowToken Type
    ShadowToken
  , mkShadowToken
  , mkShadowTokenSimple
  
  -- * Accessors
  , shadowTokenName
  , shadowTokenDesc
  , shadowTokenValue
  , shadowTokenElevation
  , shadowTokenMeta
  
  -- * Shadow Value
  , ShadowValue
  , mkShadowValue
  , shadowOffsetX
  , shadowOffsetY
  , shadowBlur
  , shadowSpread
  , shadowOpacity
  , shadowInset
  
  -- * Elevation Level
  , ElevationLevel(..)
  , elevationToInt
  , elevationFromInt
  , elevationToString
  
  -- * Shadow Layers
  , ShadowLayers
  , singleShadow
  , layeredShadow
  , shadowLayerCount
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (<)
  , (>)
  , otherwise
  )

import Data.Array (length)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Brand.Token
  ( TokenName
  , TokenDesc
  , TokenCategory(CategoryShadow)
  , TokenMeta
  , mkTokenMeta
  , mkTokenDesc
  , unTokenName
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // shadow // value
-- ═════════════════════════════════════════════════════════════════════════════

-- | Single shadow layer definition.
-- |
-- | All measurements in pixels. Opacity is 0.0-1.0.
type ShadowValue =
  { offsetX :: Number   -- ^ Horizontal offset (positive = right)
  , offsetY :: Number   -- ^ Vertical offset (positive = down)
  , blur :: Number      -- ^ Blur radius (>= 0)
  , spread :: Number    -- ^ Spread radius (can be negative)
  , opacity :: Number   -- ^ Shadow opacity (0.0-1.0)
  , inset :: Boolean    -- ^ Inner shadow if true
  }

-- | Create a shadow value with validation.
mkShadowValue 
  :: Number    -- ^ Offset X
  -> Number    -- ^ Offset Y
  -> Number    -- ^ Blur radius
  -> Number    -- ^ Spread radius
  -> Number    -- ^ Opacity
  -> Boolean   -- ^ Inset
  -> ShadowValue
mkShadowValue ox oy blur spread opacity inset =
  { offsetX: ox
  , offsetY: oy
  , blur: clampMin 0.0 blur
  , spread: spread
  , opacity: clamp01 opacity
  , inset: inset
  }
  where
  clampMin :: Number -> Number -> Number
  clampMin minVal n = if n < minVal then minVal else n
  
  clamp01 :: Number -> Number
  clamp01 n
    | n < 0.0 = 0.0
    | n > 1.0 = 1.0
    | otherwise = n

-- | Get X offset.
shadowOffsetX :: ShadowValue -> Number
shadowOffsetX s = s.offsetX

-- | Get Y offset.
shadowOffsetY :: ShadowValue -> Number
shadowOffsetY s = s.offsetY

-- | Get blur radius.
shadowBlur :: ShadowValue -> Number
shadowBlur s = s.blur

-- | Get spread radius.
shadowSpread :: ShadowValue -> Number
shadowSpread s = s.spread

-- | Get opacity.
shadowOpacity :: ShadowValue -> Number
shadowOpacity s = s.opacity

-- | Check if inset shadow.
shadowInset :: ShadowValue -> Boolean
shadowInset s = s.inset

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // elevation // level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic elevation level.
-- |
-- | Maps to Material Design elevation concept.
data ElevationLevel
  = Elevation0   -- ^ Ground level (no shadow)
  | Elevation1   -- ^ Subtle lift (cards)
  | Elevation2   -- ^ Raised (FAB, active cards)
  | Elevation3   -- ^ Floating (menus)
  | Elevation4   -- ^ Modal (dialogs)
  | Elevation5   -- ^ Overlay (maximum elevation)

derive instance eqElevationLevel :: Eq ElevationLevel
derive instance ordElevationLevel :: Ord ElevationLevel

instance showElevationLevel :: Show ElevationLevel where
  show = elevationToString

-- | Convert to integer (0-5).
elevationToInt :: ElevationLevel -> Int
elevationToInt = case _ of
  Elevation0 -> 0
  Elevation1 -> 1
  Elevation2 -> 2
  Elevation3 -> 3
  Elevation4 -> 4
  Elevation5 -> 5

-- | Parse from integer.
elevationFromInt :: Int -> Maybe ElevationLevel
elevationFromInt = case _ of
  0 -> Just Elevation0
  1 -> Just Elevation1
  2 -> Just Elevation2
  3 -> Just Elevation3
  4 -> Just Elevation4
  5 -> Just Elevation5
  _ -> Nothing

-- | Convert to string.
elevationToString :: ElevationLevel -> String
elevationToString = case _ of
  Elevation0 -> "none"
  Elevation1 -> "sm"
  Elevation2 -> "md"
  Elevation3 -> "lg"
  Elevation4 -> "xl"
  Elevation5 -> "2xl"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // shadow // layers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Multiple shadow layers (for realistic shadows).
-- |
-- | Real shadows often use multiple layers for ambient + key light effects.
newtype ShadowLayers = ShadowLayers (Array ShadowValue)

derive instance eqShadowLayers :: Eq ShadowLayers
derive instance ordShadowLayers :: Ord ShadowLayers

instance showShadowLayers :: Show ShadowLayers where
  show (ShadowLayers layers) = "ShadowLayers[" <> show (length layers) <> "]"

-- | Create single-layer shadow.
singleShadow :: ShadowValue -> ShadowLayers
singleShadow s = ShadowLayers [s]

-- | Create multi-layer shadow.
layeredShadow :: Array ShadowValue -> ShadowLayers
layeredShadow = ShadowLayers

-- | Get number of shadow layers.
shadowLayerCount :: ShadowLayers -> Int
shadowLayerCount (ShadowLayers layers) = length layers

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // shadow // token
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow design token.
-- |
-- | Binds a semantic name to shadow layers with elevation metadata.
type ShadowToken =
  { meta :: TokenMeta
  , value :: ShadowLayers
  , elevation :: ElevationLevel
  }

-- | Create a shadow token with full metadata.
mkShadowToken :: TokenName -> TokenDesc -> ShadowLayers -> ElevationLevel -> ShadowToken
mkShadowToken name desc value elevation =
  { meta: mkTokenMeta name desc CategoryShadow
  , value: value
  , elevation: elevation
  }

-- | Create a simple shadow token (single layer).
mkShadowTokenSimple 
  :: TokenName 
  -> Number           -- ^ Y offset
  -> Number           -- ^ Blur
  -> Number           -- ^ Opacity
  -> ElevationLevel 
  -> ShadowToken
mkShadowTokenSimple name y blur opacity elevation =
  let
    desc = mkTokenDesc ("Shadow token: " <> unTokenName name)
    shadow = mkShadowValue 0.0 y blur 0.0 opacity false
    layers = singleShadow shadow
  in
    { meta: mkTokenMeta name desc CategoryShadow
    , value: layers
    , elevation: elevation
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the token name.
shadowTokenName :: ShadowToken -> TokenName
shadowTokenName t = t.meta.name

-- | Get the token description.
shadowTokenDesc :: ShadowToken -> TokenDesc
shadowTokenDesc t = t.meta.description

-- | Get the shadow value.
shadowTokenValue :: ShadowToken -> ShadowLayers
shadowTokenValue t = t.value

-- | Get the elevation level.
shadowTokenElevation :: ShadowToken -> ElevationLevel
shadowTokenElevation t = t.elevation

-- | Get the full metadata.
shadowTokenMeta :: ShadowToken -> TokenMeta
shadowTokenMeta t = t.meta
