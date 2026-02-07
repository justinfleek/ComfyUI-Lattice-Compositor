{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Definitions.NoiseGrain
  ( noiseGrainDefinitions,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..), EffectDefinition (..), EffectParameter (..), EffectParameterType (..), EffectParameterValue (..))

-- | Noise & Grain effect definitions
-- Migrated from ui/src/types/effects.ts EFFECT_DEFINITIONS (noise-grain category)
-- 2 effects total
noiseGrainDefinitions :: HashMap String EffectDefinition
noiseGrainDefinitions =
  HM.fromList
    [       ( "fractal-noise",
        EffectDefinition
          { defName = "Fractal Noise",
            defCategory = NoiseGrain,
            defDescription = "Generate fractal noise pattern",
            defParameters =
              [ EffectParameter
                  { paramId = "fractal-type",
                    paramName = "Fractal Type",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "basic",
                    paramDefaultValue = ParamString "basic",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Basic", ParamString "basic"),
                          ("Turbulent Basic", ParamString "turbulent-basic"),
                          ("Soft Linear", ParamString "soft-linear"),
                          ("Turbulent Soft", ParamString "turbulent-soft")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "noise-type",
                    paramName = "Noise Type",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "block",
                    paramDefaultValue = ParamString "block",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Block", ParamString "block"),
                          ("Linear", ParamString "linear"),
                          ("Soft Linear", ParamString "soft-linear"),
                          ("Spline", ParamString "spline")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "invert",
                    paramName = "Invert",
                    paramType = ParamTypeCheckbox,
                    paramValue = ParamBool False,
                    paramDefaultValue = ParamBool False,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "contrast",
                    paramName = "Contrast",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 0.0,
                    paramMax = Just 400.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "brightness",
                    paramName = "Brightness",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-200.0),
                    paramMax = Just 200.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "scale",
                    paramName = "Scale",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 10.0,
                    paramMax = Just 10000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "complexity",
                    paramName = "Complexity",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 6.0,
                    paramDefaultValue = ParamNumber 6.0,
                    paramMin = Just 1.0,
                    paramMax = Just 20.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "evolution",
                    paramName = "Evolution",
                    paramType = ParamTypeAngle,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "add-grain",
        EffectDefinition
          { defName = "Add Grain",
            defCategory = NoiseGrain,
            defDescription = "Add film grain texture",
            defParameters =
              [ EffectParameter
                  { paramId = "intensity",
                    paramName = "Intensity",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.5,
                    paramDefaultValue = ParamNumber 0.5,
                    paramMin = Just 0.0,
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "size",
                    paramName = "Size",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.5,
                    paramMax = Just 4.0,
                    paramStep = Just 0.1,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "softness",
                    paramName = "Softness",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "animate",
                    paramName = "Animate",
                    paramType = ParamTypeCheckbox,
                    paramValue = ParamBool True,
                    paramDefaultValue = ParamBool True,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "color",
                    paramName = "Color",
                    paramType = ParamTypeCheckbox,
                    paramValue = ParamBool False,
                    paramDefaultValue = ParamBool False,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      )
    ]
