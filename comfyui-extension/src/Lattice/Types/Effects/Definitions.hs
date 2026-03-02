{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.Effects.Definitions
  ( allEffectDefinitions,
  )
where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Lattice.Types.Effects.Core (EffectDefinition)
import Lattice.Types.Effects.Definitions.BlurSharpen (blurSharpenDefinitions)
import Lattice.Types.Effects.Definitions.ColorCorrection (colorCorrectionBasicDefinitions)
import Lattice.Types.Effects.Definitions.ColorCorrectionAdvanced (colorCorrectionAdvancedDefinitions)
import Lattice.Types.Effects.Definitions.Distort (distortDefinitions)
import Lattice.Types.Effects.Definitions.Generate (generateDefinitions)
import Lattice.Types.Effects.Definitions.Time (timeDefinitions)
import Lattice.Types.Effects.Definitions.Stylize (stylizeBasicDefinitions)
import Lattice.Types.Effects.Definitions.StylizeAdvanced (stylizeAdvancedDefinitions)
import Lattice.Types.Effects.Definitions.Utility (utilityDefinitions)
import Lattice.Types.Effects.Definitions.NoiseGrain (noiseGrainDefinitions)

-- | All effect definitions combined
-- Combines all category modules into single HashMap
allEffectDefinitions :: HashMap String EffectDefinition
allEffectDefinitions =
  HM.unions
    [ blurSharpenDefinitions,
      colorCorrectionBasicDefinitions,
      colorCorrectionAdvancedDefinitions,
      distortDefinitions,
      generateDefinitions,
      timeDefinitions,
      stylizeBasicDefinitions,
      stylizeAdvancedDefinitions,
      utilityDefinitions,
      noiseGrainDefinitions
      -- Add more category modules as they're migrated
    ]
