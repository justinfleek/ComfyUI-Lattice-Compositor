{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Definitions.StylizeAdvanced
  ( stylizeAdvancedDefinitions,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..), EffectDefinition (..), EffectParameter (..), EffectParameterType (..), EffectParameterValue (..))

-- | Stylize effect definitions (Advanced)
-- Migrated from ui/src/types/effects.ts EFFECT_DEFINITIONS (stylize category)
-- Complex cinematic-bloom effect with many parameters
stylizeAdvancedDefinitions :: HashMap String EffectDefinition
stylizeAdvancedDefinitions =
  HM.fromList
    [ ( "cinematic-bloom",
        EffectDefinition
          { defName = "Cinematic Bloom",
            defCategory = Stylize,
            defDescription = "Professional bloom with inverse-square falloff, tonemapping, chromatic aberration, and lens dirt",
            defParameters =
              [ -- Core glow settings
                EffectParameter
                  { paramId = "intensity",
                    paramName = "Intensity",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.0,
                    paramMax = Just 10.0,
                    paramStep = Just 0.1,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Core"
                  },
                EffectParameter
                  { paramId = "threshold",
                    paramName = "Threshold",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.8,
                    paramDefaultValue = ParamNumber 0.8,
                    paramMin = Just 0.0,
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Core"
                  },
                EffectParameter
                  { paramId = "radius",
                    paramName = "Radius",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 50.0,
                    paramDefaultValue = ParamNumber 50.0,
                    paramMin = Just 0.0,
                    paramMax = Just 200.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Core"
                  },
                -- Falloff mode
                EffectParameter
                  { paramId = "falloff-mode",
                    paramName = "Falloff Mode",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "inverse_square",
                    paramDefaultValue = ParamString "inverse_square",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Inverse Square (Cinematic)", ParamString "inverse_square"),
                          ("Gaussian (Standard)", ParamString "gaussian"),
                          ("Exponential", ParamString "exponential")
                        ],
                    paramAnimatable = False,
                    paramGroup = Just "Falloff"
                  },
                EffectParameter
                  { paramId = "falloff-exponent",
                    paramName = "Falloff Exponent",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 2.0,
                    paramDefaultValue = ParamNumber 2.0,
                    paramMin = Just 1.0,
                    paramMax = Just 4.0,
                    paramStep = Just 0.1,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Falloff"
                  },
                -- Per-channel radius (color fringing)
                EffectParameter
                  { paramId = "radius-r",
                    paramName = "Radius R",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.0,
                    paramMax = Just 2.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Color Fringing"
                  },
                EffectParameter
                  { paramId = "radius-g",
                    paramName = "Radius G",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.0,
                    paramMax = Just 2.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Color Fringing"
                  },
                EffectParameter
                  { paramId = "radius-b",
                    paramName = "Radius B",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.0,
                    paramMax = Just 2.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Color Fringing"
                  },
                -- Tonemapping
                EffectParameter
                  { paramId = "tonemap",
                    paramName = "Tonemap",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "aces",
                    paramDefaultValue = ParamString "aces",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("None", ParamString "none"),
                          ("ACES Filmic", ParamString "aces"),
                          ("Reinhard", ParamString "reinhard"),
                          ("Hable (Uncharted 2)", ParamString "hable")
                        ],
                    paramAnimatable = False,
                    paramGroup = Just "Tonemapping"
                  },
                EffectParameter
                  { paramId = "exposure",
                    paramName = "Exposure",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-5.0),
                    paramMax = Just 5.0,
                    paramStep = Just 0.1,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Tonemapping"
                  },
                -- Chromatic aberration
                EffectParameter
                  { paramId = "chromatic-aberration",
                    paramName = "Chromatic Aberration",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 20.0,
                    paramStep = Just 0.5,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Aberration"
                  },
                -- Lens dirt
                EffectParameter
                  { paramId = "lens-dirt-enabled",
                    paramName = "Lens Dirt Enabled",
                    paramType = ParamTypeCheckbox,
                    paramValue = ParamBool False,
                    paramDefaultValue = ParamBool False,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Just "Lens Dirt"
                  },
                EffectParameter
                  { paramId = "lens-dirt-intensity",
                    paramName = "Lens Dirt Intensity",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.5,
                    paramDefaultValue = ParamNumber 0.5,
                    paramMin = Just 0.0,
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Lens Dirt"
                  },
                EffectParameter
                  { paramId = "lens-dirt-scale",
                    paramName = "Lens Dirt Scale",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.5,
                    paramMax = Just 2.0,
                    paramStep = Just 0.1,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Lens Dirt"
                  },
                -- Blend mode
                EffectParameter
                  { paramId = "blend-mode",
                    paramName = "Blend Mode",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "add",
                    paramDefaultValue = ParamString "add",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Add", ParamString "add"),
                          ("Screen", ParamString "screen"),
                          ("Overlay", ParamString "overlay"),
                          ("Soft Light", ParamString "soft_light")
                        ],
                    paramAnimatable = False,
                    paramGroup = Just "Blending"
                  }
              ],
            defFragmentShader = Nothing
          }
      )
    ]
