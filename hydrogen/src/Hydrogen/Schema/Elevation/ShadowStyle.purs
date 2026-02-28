-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // elevation // shadow-style
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shadow style compounds — aesthetic shadow presets.
-- |
-- | ## Design Philosophy
-- |
-- | These compounds represent **stylistic choices** rather than semantic
-- | elevation. They define the aesthetic quality of a shadow:
-- |
-- | - **Soft**: Diffuse, gentle shadows (modern, minimal)
-- | - **Hard**: Crisp, defined shadows (bold, graphic)
-- | - **Layered**: Multiple shadows for depth (realistic, premium)
-- | - **Colored**: Tinted shadows matching element (playful, branded)
-- | - **Long**: Extended shadows (dramatic, low sun angle)
-- |
-- | ## Relationship to SemanticElevation
-- |
-- | SemanticElevation defines WHAT level (flat, raised, floating, etc.)
-- | ShadowStyle defines HOW that elevation looks visually.
-- |
-- | A modal dialog might be at Elevation4 (Modal level) but rendered with
-- | either ShadowSoft for a gentle appearance or ShadowHard for emphasis.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Elevation.ShadowStyle as SS
-- | import Hydrogen.Schema.Color.RGB as RGB
-- |
-- | -- Get a soft shadow with intensity 2 (1-5 scale)
-- | cardShadow = SS.shadowSoft 2
-- |
-- | -- Get a colored shadow based on element color
-- | coloredShadow = SS.shadowColored (RGB.rgb 59 130 246) 3
-- |
-- | -- Convert to CSS
-- | css = SS.toLegacyCss cardShadow
-- | ```

module Hydrogen.Schema.Elevation.ShadowStyle
  ( -- * Shadow Style Type
    ShadowStyle(..)
  , Intensity
  
  -- * No Shadow
  , shadowNone
  
  -- * Soft Shadows
  , shadowSoft
  , shadowSoftConfig
  
  -- * Hard Shadows
  , shadowHard
  , shadowHardConfig
  
  -- * Layered Shadows
  , shadowLayered
  , shadowLayeredConfig
  
  -- * Colored Shadows
  , shadowColored
  , shadowColoredConfig
  
  -- * Long Shadows
  , shadowLong
  , shadowLongConfig
  
  -- * Accessors
  , getStyleName
  , getIntensity
  , getShadow
  
  -- * Conversion (Legacy CSS, not FFI)
  , toLegacyCss
  
  -- * Predicates
  , isNone
  , isSoft
  , isHard
  , isLayered
  , isColored
  , isLong
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , negate
  , (+)
  , (-)
  , (*)
  , (<)
  , (>)
  , (<>)
  , (==)
  , ($)
  , max
  , min
  )

import Data.Int as Int

import Hydrogen.Schema.Color.RGB (RGBA, RGB, rgba, toRecord)
import Hydrogen.Schema.Elevation.Shadow 
  ( LayeredShadow
  , BoxShadow
  , boxShadow
  , layered
  , noShadow
  , layeredToLegacyCss
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow style — aesthetic category with intensity.
-- |
-- | Each style has a 1-5 intensity scale where:
-- | - 1 = Subtle, barely visible
-- | - 2 = Light, noticeable but gentle
-- | - 3 = Medium, balanced (default)
-- | - 4 = Strong, prominent
-- | - 5 = Maximum, dramatic
data ShadowStyle
  = None
  | Soft Intensity LayeredShadow
  | Hard Intensity LayeredShadow
  | Layered Intensity LayeredShadow
  | Colored Intensity RGBA LayeredShadow
  | Long Intensity LayeredShadow

derive instance eqShadowStyle :: Eq ShadowStyle

instance showShadowStyle :: Show ShadowStyle where
  show None = "ShadowNone"
  show (Soft i _) = "ShadowSoft " <> show (getIntensityValue i)
  show (Hard i _) = "ShadowHard " <> show (getIntensityValue i)
  show (Layered i _) = "ShadowLayered " <> show (getIntensityValue i)
  show (Colored i _ _) = "ShadowColored " <> show (getIntensityValue i)
  show (Long i _) = "ShadowLong " <> show (getIntensityValue i)

-- | Intensity level (1-5, clamped)
newtype Intensity = Intensity Int

derive instance eqIntensity :: Eq Intensity
derive instance ordIntensity :: Ord Intensity

instance showIntensity :: Show Intensity where
  show (Intensity n) = show n

-- | Create intensity (clamped 1-5)
intensity :: Int -> Intensity
intensity n = Intensity (max 1 (min 5 n))

-- | Get raw intensity value
getIntensityValue :: Intensity -> Int
getIntensityValue (Intensity n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // no shadow
-- ═════════════════════════════════════════════════════════════════════════════

-- | No shadow — explicit absence of shadow styling.
-- |
-- | Use this when you want to explicitly indicate "no shadow" rather than
-- | just omitting the shadow property. This is semantically meaningful:
-- | it says "I deliberately chose no shadow" vs "I forgot to set one".
shadowNone :: ShadowStyle
shadowNone = None

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // soft shadows
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for soft shadows
type SoftConfig =
  { blurMultiplier :: Number     -- ^ Blur per intensity level
  , spreadMultiplier :: Number   -- ^ Negative spread per level
  , opacityBase :: Int           -- ^ Base alpha percentage
  }

-- | Default soft shadow configuration
shadowSoftConfig :: SoftConfig
shadowSoftConfig =
  { blurMultiplier: 8.0
  , spreadMultiplier: -2.0
  , opacityBase: 8
  }

-- | Create a soft shadow with intensity 1-5.
-- |
-- | Soft shadows have:
-- | - Large blur radius
-- | - Negative spread (tighter shadow shape)
-- | - Low opacity
-- | - Minimal offset (nearly centered)
shadowSoft :: Int -> ShadowStyle
shadowSoft level =
  let
    i = intensity level
    n = getIntensityValue i
    blur = shadowSoftConfig.blurMultiplier * intToNumber n
    spread = shadowSoftConfig.spreadMultiplier * intToNumber n
    alpha = shadowSoftConfig.opacityBase + (n * 2)
    shadow = layered
      [ mkShadow 0.0 (intToNumber n) blur spread (blackAlpha alpha)
      ]
  in
    Soft i shadow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // hard shadows
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for hard shadows
type HardConfig =
  { blurMultiplier :: Number     -- ^ Blur per intensity (small for hardness)
  , offsetMultiplier :: Number   -- ^ Offset per level
  , opacityBase :: Int           -- ^ Base alpha percentage
  }

-- | Default hard shadow configuration
shadowHardConfig :: HardConfig
shadowHardConfig =
  { blurMultiplier: 1.0
  , offsetMultiplier: 2.0
  , opacityBase: 15
  }

-- | Create a hard shadow with intensity 1-5.
-- |
-- | Hard shadows have:
-- | - Minimal blur (crisp edges)
-- | - Higher opacity
-- | - Clear directional offset
-- | - No spread
shadowHard :: Int -> ShadowStyle
shadowHard level =
  let
    i = intensity level
    n = getIntensityValue i
    blur = shadowHardConfig.blurMultiplier * intToNumber n
    offset = shadowHardConfig.offsetMultiplier * intToNumber n
    alpha = shadowHardConfig.opacityBase + (n * 5)
    shadow = layered
      [ mkShadow offset offset blur 0.0 (blackAlpha alpha)
      ]
  in
    Hard i shadow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // layered shadows
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for layered shadows
type LayeredConfig =
  { layers :: Int                -- ^ Number of shadow layers
  , blurScale :: Number          -- ^ Blur growth per layer
  , opacityDecay :: Number       -- ^ Opacity reduction per layer
  }

-- | Default layered shadow configuration
shadowLayeredConfig :: LayeredConfig
shadowLayeredConfig =
  { layers: 3
  , blurScale: 2.0
  , opacityDecay: 0.6
  }

-- | Create a layered shadow with intensity 1-5.
-- |
-- | Layered shadows have:
-- | - Multiple shadow layers
-- | - Each layer has progressively more blur
-- | - Opacity decreases with distance
-- | - Creates realistic depth perception
shadowLayered :: Int -> ShadowStyle
shadowLayered level =
  let
    i = intensity level
    n = getIntensityValue i
    baseBlur = 2.0 * intToNumber n
    baseAlpha = 12 - n  -- Lower intensity = higher base opacity per layer
    
    -- Layer 1: Tight, subtle
    layer1 = mkShadow 0.0 1.0 baseBlur (-1.0) (blackAlpha baseAlpha)
    
    -- Layer 2: Medium blur
    layer2 = mkShadow 0.0 (2.0 * intToNumber n) (baseBlur * 2.0) 
             (-2.0) (blackAlpha (baseAlpha - 2))
    
    -- Layer 3: Wide, soft
    layer3 = mkShadow 0.0 (4.0 * intToNumber n) (baseBlur * 4.0) 
             (-4.0) (blackAlpha (baseAlpha - 4))
    
    shadow = layered [layer1, layer2, layer3]
  in
    Layered i shadow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // colored shadows
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for colored shadows
type ColoredConfig =
  { blurMultiplier :: Number     -- ^ Blur per intensity
  , opacityBase :: Int           -- ^ Alpha percentage for color
  }

-- | Default colored shadow configuration
shadowColoredConfig :: ColoredConfig
shadowColoredConfig =
  { blurMultiplier: 8.0
  , opacityBase: 30
  }

-- | Create a colored shadow with intensity 1-5.
-- |
-- | Colored shadows have:
-- | - Tint matching or complementing the element
-- | - Moderate blur (to show color clearly)
-- | - Good for buttons, cards with strong colors
-- | - Creates playful, branded feel
shadowColored :: RGB -> Int -> ShadowStyle
shadowColored color level =
  let
    i = intensity level
    n = getIntensityValue i
    blur = shadowColoredConfig.blurMultiplier * intToNumber n
    alpha = shadowColoredConfig.opacityBase + (n * 5)
    
    -- Get RGBA from RGB with calculated alpha
    -- Extract RGB channels and combine with alpha
    rec = toRecord color
    colorRGBA = rgba rec.r rec.g rec.b alpha
    
    shadow = layered
      [ mkShadowColor 0.0 (intToNumber n * 2.0) blur 0.0 colorRGBA
      ]
  in
    Colored i colorRGBA shadow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // long shadows
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for long shadows
type LongConfig =
  { lengthMultiplier :: Number   -- ^ Shadow length per intensity
  , blurMultiplier :: Number     -- ^ Blur per intensity
  , opacityBase :: Int           -- ^ Base alpha
  }

-- | Default long shadow configuration
shadowLongConfig :: LongConfig
shadowLongConfig =
  { lengthMultiplier: 15.0
  , blurMultiplier: 3.0
  , opacityBase: 8
  }

-- | Create a long shadow with intensity 1-5.
-- |
-- | Long shadows have:
-- | - Extended offset (simulating low sun angle)
-- | - Multiple steps for smooth gradient
-- | - Dramatic, illustrative feel
-- | - Popular in flat design / material design
shadowLong :: Int -> ShadowStyle
shadowLong level =
  let
    i = intensity level
    n = getIntensityValue i
    length = shadowLongConfig.lengthMultiplier * intToNumber n
    blur = shadowLongConfig.blurMultiplier * intToNumber n
    alpha = shadowLongConfig.opacityBase
    
    -- Multiple layers for smooth long shadow
    step1 = mkShadow (length * 0.25) (length * 0.25) (blur * 0.5) 0.0 (blackAlpha (alpha + 4))
    step2 = mkShadow (length * 0.5) (length * 0.5) blur 0.0 (blackAlpha alpha)
    step3 = mkShadow length length (blur * 1.5) 0.0 (blackAlpha (alpha - 2))
    
    shadow = layered [step1, step2, step3]
  in
    Long i shadow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the style name as a string
getStyleName :: ShadowStyle -> String
getStyleName None = "none"
getStyleName (Soft _ _) = "soft"
getStyleName (Hard _ _) = "hard"
getStyleName (Layered _ _) = "layered"
getStyleName (Colored _ _ _) = "colored"
getStyleName (Long _ _) = "long"

-- | Get the intensity level (0 for None)
getIntensity :: ShadowStyle -> Int
getIntensity None = 0
getIntensity (Soft i _) = getIntensityValue i
getIntensity (Hard i _) = getIntensityValue i
getIntensity (Layered i _) = getIntensityValue i
getIntensity (Colored i _ _) = getIntensityValue i
getIntensity (Long i _) = getIntensityValue i

-- | Get the underlying LayeredShadow
getShadow :: ShadowStyle -> LayeredShadow
getShadow None = noShadow
getShadow (Soft _ s) = s
getShadow (Hard _ s) = s
getShadow (Layered _ s) = s
getShadow (Colored _ _ s) = s
getShadow (Long _ s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert shadow style to CSS box-shadow string.
-- |
-- | NOT an FFI boundary — pure string generation.
toLegacyCss :: ShadowStyle -> String
toLegacyCss = layeredToLegacyCss <<< getShadow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if shadow is none (no shadow)
isNone :: ShadowStyle -> Boolean
isNone None = true
isNone _ = false

-- | Check if shadow is soft style
isSoft :: ShadowStyle -> Boolean
isSoft (Soft _ _) = true
isSoft _ = false

-- | Check if shadow is hard style
isHard :: ShadowStyle -> Boolean
isHard (Hard _ _) = true
isHard _ = false

-- | Check if shadow is layered style
isLayered :: ShadowStyle -> Boolean
isLayered (Layered _ _) = true
isLayered _ = false

-- | Check if shadow is colored style
isColored :: ShadowStyle -> Boolean
isColored (Colored _ _ _) = true
isColored _ = false

-- | Check if shadow is long style
isLong :: ShadowStyle -> Boolean
isLong (Long _ _) = true
isLong _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Function composition
infixr 9 composeFlipped as <<<

composeFlipped :: forall a b c. (b -> c) -> (a -> b) -> a -> c
composeFlipped f g x = f (g x)

-- | Create shadow with black color
mkShadow :: Number -> Number -> Number -> Number -> RGBA -> BoxShadow
mkShadow ox oy blur spread color = boxShadow
  { offsetX: ox
  , offsetY: oy
  , blur: blur
  , spread: spread
  , color: color
  , inset: false
  }

-- | Create shadow with custom color
mkShadowColor :: Number -> Number -> Number -> Number -> RGBA -> BoxShadow
mkShadowColor = mkShadow

-- | Black with alpha percentage
blackAlpha :: Int -> RGBA
blackAlpha alpha = rgba 0 0 0 (max 1 (min 100 alpha))

-- | Convert Int to Number
-- |
-- | Uses Data.Int.toNumber from the standard library.
intToNumber :: Int -> Number
intToNumber = Int.toNumber
