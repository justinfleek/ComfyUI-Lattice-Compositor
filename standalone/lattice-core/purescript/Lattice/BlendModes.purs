-- | Lattice.BlendModes - Industry standard blend modes
-- |
-- | Source: lattice-core/lean/Lattice/BlendModes.lean

module Lattice.BlendModes
  ( BlendMode(..)
  , BlendModeCategory(..)
  , blendModeCategory
  , categoryModes
  , allBlendModes
  , blendModeToString
  , blendModeFromString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Blend Mode
--------------------------------------------------------------------------------

data BlendMode
  -- Normal
  = BMNormal | BMDissolve
  -- Darken
  | BMDarken | BMMultiply | BMColorBurn | BMLinearBurn | BMDarkerColor
  -- Lighten
  | BMLighten | BMScreen | BMColorDodge | BMLinearDodge | BMLighterColor | BMAdd
  -- Contrast
  | BMOverlay | BMSoftLight | BMHardLight | BMVividLight | BMLinearLight | BMPinLight | BMHardMix
  -- Inversion
  | BMDifference | BMExclusion | BMSubtract | BMDivide
  -- Component (HSL)
  | BMHue | BMSaturation | BMColor | BMLuminosity
  -- Utility/Advanced
  | BMStencilAlpha | BMStencilLuma | BMSilhouetteAlpha | BMSilhouetteLuma
  | BMAlphaAdd | BMLuminescentPremul
  -- Classic (legacy)
  | BMClassicColorBurn | BMClassicColorDodge

derive instance Eq BlendMode
derive instance Ord BlendMode
derive instance Generic BlendMode _
instance Show BlendMode where show = genericShow

--------------------------------------------------------------------------------
-- Blend Mode Category
--------------------------------------------------------------------------------

data BlendModeCategory
  = BMCNormal | BMCDarken | BMCLighten | BMCContrast
  | BMCInversion | BMCComponent | BMCUtility

derive instance Eq BlendModeCategory
derive instance Generic BlendModeCategory _
instance Show BlendModeCategory where show = genericShow

blendModeCategory :: BlendMode -> BlendModeCategory
blendModeCategory bm = case bm of
  -- Normal
  BMNormal -> BMCNormal
  BMDissolve -> BMCNormal
  -- Darken
  BMDarken -> BMCDarken
  BMMultiply -> BMCDarken
  BMColorBurn -> BMCDarken
  BMLinearBurn -> BMCDarken
  BMDarkerColor -> BMCDarken
  -- Lighten
  BMLighten -> BMCLighten
  BMScreen -> BMCLighten
  BMColorDodge -> BMCLighten
  BMLinearDodge -> BMCLighten
  BMLighterColor -> BMCLighten
  BMAdd -> BMCLighten
  -- Contrast
  BMOverlay -> BMCContrast
  BMSoftLight -> BMCContrast
  BMHardLight -> BMCContrast
  BMVividLight -> BMCContrast
  BMLinearLight -> BMCContrast
  BMPinLight -> BMCContrast
  BMHardMix -> BMCContrast
  -- Inversion
  BMDifference -> BMCInversion
  BMExclusion -> BMCInversion
  BMSubtract -> BMCInversion
  BMDivide -> BMCInversion
  -- Component
  BMHue -> BMCComponent
  BMSaturation -> BMCComponent
  BMColor -> BMCComponent
  BMLuminosity -> BMCComponent
  -- Utility
  BMStencilAlpha -> BMCUtility
  BMStencilLuma -> BMCUtility
  BMSilhouetteAlpha -> BMCUtility
  BMSilhouetteLuma -> BMCUtility
  BMAlphaAdd -> BMCUtility
  BMLuminescentPremul -> BMCUtility
  -- Classic
  BMClassicColorBurn -> BMCDarken
  BMClassicColorDodge -> BMCLighten

categoryModes :: BlendModeCategory -> Array BlendMode
categoryModes cat = case cat of
  BMCNormal -> [BMNormal, BMDissolve]
  BMCDarken -> [BMDarken, BMMultiply, BMColorBurn, BMLinearBurn, BMDarkerColor]
  BMCLighten -> [BMLighten, BMScreen, BMColorDodge, BMLinearDodge, BMLighterColor, BMAdd]
  BMCContrast -> [BMOverlay, BMSoftLight, BMHardLight, BMVividLight, BMLinearLight, BMPinLight, BMHardMix]
  BMCInversion -> [BMDifference, BMExclusion, BMSubtract, BMDivide]
  BMCComponent -> [BMHue, BMSaturation, BMColor, BMLuminosity]
  BMCUtility -> [BMStencilAlpha, BMStencilLuma, BMSilhouetteAlpha, BMSilhouetteLuma, BMAlphaAdd, BMLuminescentPremul]

allBlendModes :: Array BlendMode
allBlendModes =
  [ BMNormal, BMDissolve
  , BMDarken, BMMultiply, BMColorBurn, BMLinearBurn, BMDarkerColor
  , BMLighten, BMScreen, BMColorDodge, BMLinearDodge, BMLighterColor, BMAdd
  , BMOverlay, BMSoftLight, BMHardLight, BMVividLight, BMLinearLight, BMPinLight, BMHardMix
  , BMDifference, BMExclusion, BMSubtract, BMDivide
  , BMHue, BMSaturation, BMColor, BMLuminosity
  , BMStencilAlpha, BMStencilLuma, BMSilhouetteAlpha, BMSilhouetteLuma, BMAlphaAdd, BMLuminescentPremul
  , BMClassicColorBurn, BMClassicColorDodge
  ]

--------------------------------------------------------------------------------
-- String Conversion (for JSON interop)
--------------------------------------------------------------------------------

-- | Convert blend mode to kebab-case string (matches TypeScript)
blendModeToString :: BlendMode -> String
blendModeToString BMNormal = "normal"
blendModeToString BMDissolve = "dissolve"
blendModeToString BMDarken = "darken"
blendModeToString BMMultiply = "multiply"
blendModeToString BMColorBurn = "color-burn"
blendModeToString BMLinearBurn = "linear-burn"
blendModeToString BMDarkerColor = "darker-color"
blendModeToString BMLighten = "lighten"
blendModeToString BMScreen = "screen"
blendModeToString BMColorDodge = "color-dodge"
blendModeToString BMLinearDodge = "linear-dodge"
blendModeToString BMLighterColor = "lighter-color"
blendModeToString BMAdd = "add"
blendModeToString BMOverlay = "overlay"
blendModeToString BMSoftLight = "soft-light"
blendModeToString BMHardLight = "hard-light"
blendModeToString BMVividLight = "vivid-light"
blendModeToString BMLinearLight = "linear-light"
blendModeToString BMPinLight = "pin-light"
blendModeToString BMHardMix = "hard-mix"
blendModeToString BMDifference = "difference"
blendModeToString BMExclusion = "exclusion"
blendModeToString BMSubtract = "subtract"
blendModeToString BMDivide = "divide"
blendModeToString BMHue = "hue"
blendModeToString BMSaturation = "saturation"
blendModeToString BMColor = "color"
blendModeToString BMLuminosity = "luminosity"
blendModeToString BMStencilAlpha = "stencil-alpha"
blendModeToString BMStencilLuma = "stencil-luma"
blendModeToString BMSilhouetteAlpha = "silhouette-alpha"
blendModeToString BMSilhouetteLuma = "silhouette-luma"
blendModeToString BMAlphaAdd = "alpha-add"
blendModeToString BMLuminescentPremul = "luminescent-premul"
blendModeToString BMClassicColorBurn = "classic-color-burn"
blendModeToString BMClassicColorDodge = "classic-color-dodge"

-- | Parse blend mode from kebab-case string
blendModeFromString :: String -> Maybe BlendMode
blendModeFromString "normal" = Just BMNormal
blendModeFromString "dissolve" = Just BMDissolve
blendModeFromString "darken" = Just BMDarken
blendModeFromString "multiply" = Just BMMultiply
blendModeFromString "color-burn" = Just BMColorBurn
blendModeFromString "linear-burn" = Just BMLinearBurn
blendModeFromString "darker-color" = Just BMDarkerColor
blendModeFromString "lighten" = Just BMLighten
blendModeFromString "screen" = Just BMScreen
blendModeFromString "color-dodge" = Just BMColorDodge
blendModeFromString "linear-dodge" = Just BMLinearDodge
blendModeFromString "lighter-color" = Just BMLighterColor
blendModeFromString "add" = Just BMAdd
blendModeFromString "overlay" = Just BMOverlay
blendModeFromString "soft-light" = Just BMSoftLight
blendModeFromString "hard-light" = Just BMHardLight
blendModeFromString "vivid-light" = Just BMVividLight
blendModeFromString "linear-light" = Just BMLinearLight
blendModeFromString "pin-light" = Just BMPinLight
blendModeFromString "hard-mix" = Just BMHardMix
blendModeFromString "difference" = Just BMDifference
blendModeFromString "exclusion" = Just BMExclusion
blendModeFromString "subtract" = Just BMSubtract
blendModeFromString "divide" = Just BMDivide
blendModeFromString "hue" = Just BMHue
blendModeFromString "saturation" = Just BMSaturation
blendModeFromString "color" = Just BMColor
blendModeFromString "luminosity" = Just BMLuminosity
blendModeFromString "stencil-alpha" = Just BMStencilAlpha
blendModeFromString "stencil-luma" = Just BMStencilLuma
blendModeFromString "silhouette-alpha" = Just BMSilhouetteAlpha
blendModeFromString "silhouette-luma" = Just BMSilhouetteLuma
blendModeFromString "alpha-add" = Just BMAlphaAdd
blendModeFromString "luminescent-premul" = Just BMLuminescentPremul
blendModeFromString "classic-color-burn" = Just BMClassicColorBurn
blendModeFromString "classic-color-dodge" = Just BMClassicColorDodge
blendModeFromString _ = Nothing
