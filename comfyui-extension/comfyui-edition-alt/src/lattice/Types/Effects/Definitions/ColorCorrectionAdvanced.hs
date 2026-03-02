{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Definitions.ColorCorrectionAdvanced
  ( colorCorrectionAdvancedDefinitions,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..), EffectDefinition (..), EffectParameter (..), EffectParameterType (..), EffectParameterValue (..))

-- | Color Correction effect definitions (Advanced)
-- Migrated from ui/src/types/effects.ts EFFECT_DEFINITIONS (color-correction category)
-- Remaining 4 complex effects (lift-gamma-gain, hsl-secondary, hue-vs-curves, color-match)
-- Split from ColorCorrection.hs when it reached 678 lines (>500 limit)
colorCorrectionAdvancedDefinitions :: HashMap String EffectDefinition
colorCorrectionAdvancedDefinitions =
  HM.fromList
    [ ( "lift-gamma-gain",
        EffectDefinition
          { defName = "Lift/Gamma/Gain",
            defCategory = ColorCorrection,
            defDescription = "ASC CDL-style three-way color correction",
            defParameters =
              [ -- Lift (Shadows)
                EffectParameter
                  { paramId = "lift-red",
                    paramName = "Lift Red",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-1.0),
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "lift-green",
                    paramName = "Lift Green",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-1.0),
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "lift-blue",
                    paramName = "Lift Blue",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-1.0),
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                -- Gamma (Midtones)
                EffectParameter
                  { paramId = "gamma-red",
                    paramName = "Gamma Red",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.1,
                    paramMax = Just 4.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "gamma-green",
                    paramName = "Gamma Green",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.1,
                    paramMax = Just 4.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "gamma-blue",
                    paramName = "Gamma Blue",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.1,
                    paramMax = Just 4.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                -- Gain (Highlights)
                EffectParameter
                  { paramId = "gain-red",
                    paramName = "Gain Red",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.0,
                    paramMax = Just 4.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "gain-green",
                    paramName = "Gain Green",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.0,
                    paramMax = Just 4.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "gain-blue",
                    paramName = "Gain Blue",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.0,
                    paramMax = Just 4.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "hsl-secondary",
        EffectDefinition
          { defName = "HSL Secondary",
            defCategory = ColorCorrection,
            defDescription = "Targeted color correction by hue/saturation/luminance range",
            defParameters =
              [ -- Qualification
                EffectParameter
                  { paramId = "hue-center",
                    paramName = "Hue Center",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 360.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "hue-width",
                    paramName = "Hue Width",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 30.0,
                    paramDefaultValue = ParamNumber 30.0,
                    paramMin = Just 0.0,
                    paramMax = Just 180.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "hue-falloff",
                    paramName = "Hue Falloff",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10.0,
                    paramDefaultValue = ParamNumber 10.0,
                    paramMin = Just 0.0,
                    paramMax = Just 90.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "sat-min",
                    paramName = "Sat Min",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "sat-max",
                    paramName = "Sat Max",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "sat-falloff",
                    paramName = "Sat Falloff",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10.0,
                    paramDefaultValue = ParamNumber 10.0,
                    paramMin = Just 0.0,
                    paramMax = Just 50.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "lum-min",
                    paramName = "Lum Min",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "lum-max",
                    paramName = "Lum Max",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "lum-falloff",
                    paramName = "Lum Falloff",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10.0,
                    paramDefaultValue = ParamNumber 10.0,
                    paramMin = Just 0.0,
                    paramMax = Just 50.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                -- Correction
                EffectParameter
                  { paramId = "hue-shift",
                    paramName = "Hue Shift",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-180.0),
                    paramMax = Just 180.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "saturation",
                    paramName = "Saturation",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "luminance",
                    paramName = "Luminance",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                -- Preview
                EffectParameter
                  { paramId = "show-mask",
                    paramName = "Show Mask",
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
      ),
      ( "hue-vs-curves",
        EffectDefinition
          { defName = "Hue vs Curves",
            defCategory = ColorCorrection,
            defDescription = "HSL-space curve adjustments for precise color control",
            defParameters =
              [ EffectParameter
                  { paramId = "hue-vs-hue",
                    paramName = "Hue vs Hue",
                    paramType = ParamTypeCurve,
                    paramValue = ParamCurve [],
                    paramDefaultValue = ParamCurve [],
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "hue-vs-sat",
                    paramName = "Hue vs Sat",
                    paramType = ParamTypeCurve,
                    paramValue = ParamCurve [],
                    paramDefaultValue = ParamCurve [],
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "hue-vs-lum",
                    paramName = "Hue vs Lum",
                    paramType = ParamTypeCurve,
                    paramValue = ParamCurve [],
                    paramDefaultValue = ParamCurve [],
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "lum-vs-sat",
                    paramName = "Lum vs Sat",
                    paramType = ParamTypeCurve,
                    paramValue = ParamCurve [],
                    paramDefaultValue = ParamCurve [],
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "sat-vs-sat",
                    paramName = "Sat vs Sat",
                    paramType = ParamTypeCurve,
                    paramValue = ParamCurve [],
                    paramDefaultValue = ParamCurve [],
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
      ),
      ( "color-match",
        EffectDefinition
          { defName = "Color Match",
            defCategory = ColorCorrection,
            defDescription = "Match color distribution to a reference image",
            defParameters =
              [ EffectParameter
                  { paramId = "reference-histogram-r",
                    paramName = "Reference Histogram R",
                    paramType = ParamTypeData,
                    paramValue = ParamNull,
                    paramDefaultValue = ParamNull,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "reference-histogram-g",
                    paramName = "Reference Histogram G",
                    paramType = ParamTypeData,
                    paramValue = ParamNull,
                    paramDefaultValue = ParamNull,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "reference-histogram-b",
                    paramName = "Reference Histogram B",
                    paramType = ParamTypeData,
                    paramValue = ParamNull,
                    paramDefaultValue = ParamNull,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "reference-pixels",
                    paramName = "Reference Pixels",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "strength",
                    paramName = "Strength",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Just 1.0,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "match-luminance",
                    paramName = "Match Luminance",
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
                  { paramId = "match-color",
                    paramName = "Match Color",
                    paramType = ParamTypeCheckbox,
                    paramValue = ParamBool True,
                    paramDefaultValue = ParamBool True,
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
