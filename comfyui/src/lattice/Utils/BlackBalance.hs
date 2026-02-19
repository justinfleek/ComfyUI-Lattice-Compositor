-- |
-- Module      : Lattice.Utils.BlackBalance
-- Description : Black balance mathematics for OLED vs LCD displays
-- 
-- Handles monitor-specific black balance calculations
-- Lean4 proofs: lattice-core/lean/Color/BlackBalance.lean
--

{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.BlackBalance
  ( -- Types
    MonitorType(..)
  , BaseColor(..)
  , HeroColor(..)
  , ThemeConfig(..)
  , ThemeVariant(..)
    -- Black balance functions
  , applyBlackBalance
  , optimalBackgroundLightness
  , recommendedBackgroundLightness
    -- Theme generation
  , generateThemeVariants
  , generateLightThemeVariants
  , adjustColorForMonitor
  , generateGrayscaleRamp
  ) where

import Lattice.Types.Color
  ( Hue(..)
  , Saturation(..)
  , Lightness(..)
  , HSL(..)
  , validateLightness
  , validateHue
  , validateSaturation
  , hueValue
  , saturationValue
  , lightnessValue
  )
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Data.Aeson (ToJSON(..), FromJSON(..), Value(..), Options(..), defaultOptions, fieldLabelModifier, object, (.=), (.:), withText)
import Data.Aeson.Key (fromString)
import GHC.Generics (Generic)

-- ============================================================================
-- MONITOR TYPE
-- ============================================================================

-- | Monitor type enumeration
data MonitorType = OLED | LCD
  deriving (Eq, Show, Enum, Bounded)

instance ToJSON MonitorType where
  toJSON OLED = toJSON (T.pack "oled")
  toJSON LCD = toJSON (T.pack "lcd")

instance FromJSON MonitorType where
  parseJSON = withText "MonitorType" $ \s ->
    case T.toLower s of
      t | t == T.pack "oled" -> return OLED
      t | t == T.pack "lcd" -> return LCD
      _ -> fail "Invalid MonitorType: expected 'oled' or 'lcd'"

-- | LCD minimum black level (backlight bleed)
lcdMinBlack :: Double
lcdMinBlack = 0.02  -- 2% typical minimum

-- | OLED black balance offset (typically 0, but can be calibrated)
oledBlackBalanceOffset :: Double
oledBlackBalanceOffset = 0.0

-- ============================================================================
-- BLACK BALANCE CALCULATION
-- ============================================================================

-- | LCD black balance function
-- Maps requested lightness to actual display lightness accounting for backlight
lcdBlackBalance :: Lightness -> Lightness
lcdBlackBalance (Lightness v) =
  validateLightness (max lcdMinBlack v)

-- | OLED black balance function
-- OLED can achieve true black, but may have slight calibration offset
oledBlackBalance :: Lightness -> Lightness
oledBlackBalance (Lightness v) =
  validateLightness (max 0.0 (v - oledBlackBalanceOffset))

-- | Calculate actual display lightness accounting for monitor type
applyBlackBalance :: MonitorType -> Lightness -> Lightness
applyBlackBalance OLED = oledBlackBalance
applyBlackBalance LCD = lcdBlackBalance

-- | Calculate optimal background lightness for monitor type
optimalBackgroundLightness :: MonitorType -> Lightness
optimalBackgroundLightness OLED = validateLightness 0.0  -- True black
optimalBackgroundLightness LCD = validateLightness lcdMinBlack  -- Minimum black

-- | Calculate recommended background lightness for readability
recommendedBackgroundLightness :: MonitorType -> Lightness
recommendedBackgroundLightness OLED = validateLightness 0.11  -- OLED-safe (prevents burn-in)
recommendedBackgroundLightness LCD = validateLightness 0.16  -- LCD minimum for contrast

-- ============================================================================
-- THEME CONFIGURATION
-- ============================================================================

-- | User-selected base color (from color wheel)
data BaseColor = BaseColor
  { baseHue :: Hue
  , baseSaturation :: Saturation
  , baseLightness :: Lightness
  }
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- | User-selected hero color (from color wheel)
data HeroColor = HeroColor
  { heroHue :: Hue
  , heroSaturation :: Saturation
  , heroLightness :: Lightness
  }
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- | Theme generation configuration
data ThemeConfig = ThemeConfig
  { configBaseColor :: BaseColor
  , configHeroColor :: HeroColor
  , configMonitorType :: MonitorType
  , configBlackBalance :: Lightness  -- User-adjusted black balance
  , configMode :: Bool  -- false = dark, true = light
  }
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- ============================================================================
-- THEME VARIANT GENERATION
-- ============================================================================

-- | Theme variant with name, background lightness, and color palette
data ThemeVariant = ThemeVariant
  { variantName :: String
  , variantBackgroundLightness :: Lightness
  , variantColors :: Map.Map Text Text  -- Map from color name (base00-base0F) to hex string
  }
  deriving (Eq, Show, Generic)

-- Custom JSON instances to match TypeScript interface
-- Unwraps Lightness to a plain number and converts Map to object
instance ToJSON ThemeVariant where
  toJSON (ThemeVariant name bgL colors) =
    object
      [ fromString "name" .= name
      , fromString "backgroundLightness" .= lightnessValue bgL
      , fromString "colors" .= colors
      ]

instance FromJSON ThemeVariant where
  parseJSON = \v -> do
    obj <- parseJSON v
    name <- obj .: fromString "name"
    bgLNum <- obj .: fromString "backgroundLightness"
    colors <- obj .: fromString "colors"
    let bgL = validateLightness bgLNum
    return (ThemeVariant name bgL colors)

-- | Generate multiple theme variants from configuration
-- Colors are populated separately by generateAllVariants
generateThemeVariants :: ThemeConfig -> [ThemeVariant]
generateThemeVariants config =
  let baseL = lightnessValue (configBlackBalance config)
      emptyColors = Map.empty
  in case configMonitorType config of
    OLED ->
      [ ThemeVariant "pure-black" (validateLightness 0.0) emptyColors
      , ThemeVariant "ultra-dark" (validateLightness 0.04) emptyColors
      , ThemeVariant "dark" (validateLightness 0.08) emptyColors
      , ThemeVariant "tuned" (validateLightness 0.11) emptyColors
      , ThemeVariant "balanced" (validateLightness (max baseL 0.11)) emptyColors
      ]
    LCD ->
      [ ThemeVariant "minimum" (validateLightness lcdMinBlack) emptyColors
      , ThemeVariant "dark" (validateLightness 0.08) emptyColors
      , ThemeVariant "balanced" (validateLightness (max baseL 0.11)) emptyColors
      , ThemeVariant "github" (validateLightness 0.16) emptyColors
      , ThemeVariant "bright" (validateLightness 0.20) emptyColors
      ]

-- | Generate light mode theme variants
-- Colors are populated separately by generateAllVariants
generateLightThemeVariants :: ThemeConfig -> [ThemeVariant]
generateLightThemeVariants _config =
  let emptyColors = Map.empty
  in [ ThemeVariant "light" (validateLightness 0.95) emptyColors
     , ThemeVariant "bright" (validateLightness 0.98) emptyColors
     , ThemeVariant "paper" (validateLightness 0.96) emptyColors
     ]

-- ============================================================================
-- COLOR ADJUSTMENT FOR BLACK BALANCE
-- ============================================================================

-- | Adjust HSL color to account for monitor black balance
adjustColorForMonitor :: MonitorType -> HSL -> HSL
adjustColorForMonitor monitorType (HSL h s l) =
  let adjustedL = applyBlackBalance monitorType l
  in HSL h s adjustedL

-- | Generate grayscale ramp accounting for monitor black balance
generateGrayscaleRamp :: MonitorType -> Hue -> Lightness -> Lightness -> Int -> [HSL]
generateGrayscaleRamp monitorType baseHue startL endL steps =
  let startV = lightnessValue startL
      endV = lightnessValue endL
      stepSize = (endV - startV) / fromIntegral (steps - 1)
      generateStep i =
        let requestedV = startV + stepSize * fromIntegral i
            requestedL = validateLightness requestedV
            adjustedL = applyBlackBalance monitorType requestedL
            satV = 0.12 + 0.04 * fromIntegral i / fromIntegral (steps - 1)
            saturation = validateSaturation satV
        in HSL baseHue saturation adjustedL
  in map generateStep [0 .. steps - 1]
