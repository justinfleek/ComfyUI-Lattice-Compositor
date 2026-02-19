{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.BlendModes
Description : Industry standard blend modes
Copyright   : (c) Lattice, 2026
License     : MIT

Source: lattice-core/lean/Lattice/BlendModes.lean
-}

module Lattice.BlendModes
  ( BlendMode(..)
  , BlendModeCategory(..)
  , blendModeCategory
  , categoryModes
  , allBlendModes
  ) where

import GHC.Generics (Generic)
import Data.Vector (Vector)
import qualified Data.Vector as V

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
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Blend Mode Category
--------------------------------------------------------------------------------

data BlendModeCategory
  = BMCNormal | BMCDarken | BMCLighten | BMCContrast
  | BMCInversion | BMCComponent | BMCUtility
  deriving stock (Eq, Show, Generic)

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

categoryModes :: BlendModeCategory -> Vector BlendMode
categoryModes cat = case cat of
  BMCNormal -> V.fromList [BMNormal, BMDissolve]
  BMCDarken -> V.fromList [BMDarken, BMMultiply, BMColorBurn, BMLinearBurn, BMDarkerColor]
  BMCLighten -> V.fromList [BMLighten, BMScreen, BMColorDodge, BMLinearDodge, BMLighterColor, BMAdd]
  BMCContrast -> V.fromList [BMOverlay, BMSoftLight, BMHardLight, BMVividLight, BMLinearLight, BMPinLight, BMHardMix]
  BMCInversion -> V.fromList [BMDifference, BMExclusion, BMSubtract, BMDivide]
  BMCComponent -> V.fromList [BMHue, BMSaturation, BMColor, BMLuminosity]
  BMCUtility -> V.fromList [BMStencilAlpha, BMStencilLuma, BMSilhouetteAlpha, BMSilhouetteLuma, BMAlphaAdd, BMLuminescentPremul]

allBlendModes :: Vector BlendMode
allBlendModes = V.fromList
  [ BMNormal, BMDissolve
  , BMDarken, BMMultiply, BMColorBurn, BMLinearBurn, BMDarkerColor
  , BMLighten, BMScreen, BMColorDodge, BMLinearDodge, BMLighterColor, BMAdd
  , BMOverlay, BMSoftLight, BMHardLight, BMVividLight, BMLinearLight, BMPinLight, BMHardMix
  , BMDifference, BMExclusion, BMSubtract, BMDivide
  , BMHue, BMSaturation, BMColor, BMLuminosity
  , BMStencilAlpha, BMStencilLuma, BMSilhouetteAlpha, BMSilhouetteLuma, BMAlphaAdd, BMLuminescentPremul
  , BMClassicColorBurn, BMClassicColorDodge
  ]
