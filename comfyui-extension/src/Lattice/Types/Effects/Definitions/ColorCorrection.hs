{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Definitions.ColorCorrection
  ( colorCorrectionBasicDefinitions,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..), EffectDefinition (..), EffectParameter (..), EffectParameterType (..), EffectParameterValue (..))

-- | Color Correction effect definitions (Basic)
-- Migrated from ui/src/types/effects.ts EFFECT_DEFINITIONS (color-correction category)
-- First 11 effects (basic color correction)
-- NOTE: File split at 678 lines - remaining 4 complex effects moved to ColorCorrectionAdvanced.hs
colorCorrectionBasicDefinitions :: HashMap String EffectDefinition
colorCorrectionBasicDefinitions =
  HM.fromList
    [ ( "brightness-contrast",
        EffectDefinition
          { defName = "Brightness & Contrast",
            defCategory = ColorCorrection,
            defDescription = "Adjust brightness and contrast",
            defParameters =
              [ EffectParameter
                  { paramId = "brightness",
                    paramName = "Brightness",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-150.0),
                    paramMax = Just 150.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "contrast",
                    paramName = "Contrast",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "use-legacy",
                    paramName = "Use Legacy",
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
      ( "hue-saturation",
        EffectDefinition
          { defName = "Hue/Saturation",
            defCategory = ColorCorrection,
            defDescription = "Adjust hue, saturation, and lightness",
            defParameters =
              [ EffectParameter
                  { paramId = "channel-control",
                    paramName = "Channel Control",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "master",
                    paramDefaultValue = ParamString "master",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Master", ParamString "master"),
                          ("Reds", ParamString "reds"),
                          ("Yellows", ParamString "yellows"),
                          ("Greens", ParamString "greens"),
                          ("Cyans", ParamString "cyans"),
                          ("Blues", ParamString "blues"),
                          ("Magentas", ParamString "magentas")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "master-hue",
                    paramName = "Master Hue",
                    paramType = ParamTypeAngle,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Master"
                  },
                EffectParameter
                  { paramId = "master-saturation",
                    paramName = "Master Saturation",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Master"
                  },
                EffectParameter
                  { paramId = "master-lightness",
                    paramName = "Master Lightness",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Master"
                  },
                EffectParameter
                  { paramId = "colorize",
                    paramName = "Colorize",
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
      ( "curves",
        EffectDefinition
          { defName = "Curves",
            defCategory = ColorCorrection,
            defDescription = "Precise tonal adjustment with curves",
            defParameters =
              [ EffectParameter
                  { paramId = "channel",
                    paramName = "Channel",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "rgb",
                    paramDefaultValue = ParamString "rgb",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("RGB", ParamString "rgb"),
                          ("Red", ParamString "red"),
                          ("Green", ParamString "green"),
                          ("Blue", ParamString "blue")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
                -- Note: Actual curve control would be a custom component
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "levels",
        EffectDefinition
          { defName = "Levels",
            defCategory = ColorCorrection,
            defDescription = "Adjust input/output levels",
            defParameters =
              [ EffectParameter
                  { paramId = "channel",
                    paramName = "Channel",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "rgb",
                    paramDefaultValue = ParamString "rgb",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("RGB", ParamString "rgb"),
                          ("Red", ParamString "red"),
                          ("Green", ParamString "green"),
                          ("Blue", ParamString "blue"),
                          ("Alpha", ParamString "alpha")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "input-black",
                    paramName = "Input Black",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 255.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "input-white",
                    paramName = "Input White",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 255.0,
                    paramDefaultValue = ParamNumber 255.0,
                    paramMin = Just 0.0,
                    paramMax = Just 255.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "gamma",
                    paramName = "Gamma",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.1,
                    paramMax = Just 10.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "output-black",
                    paramName = "Output Black",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 255.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "output-white",
                    paramName = "Output White",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 255.0,
                    paramDefaultValue = ParamNumber 255.0,
                    paramMin = Just 0.0,
                    paramMax = Just 255.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "color-balance",
        EffectDefinition
          { defName = "Color Balance",
            defCategory = ColorCorrection,
            defDescription = "Adjust color balance by tonal range",
            defParameters =
              [ -- Shadows
                EffectParameter
                  { paramId = "shadow-red",
                    paramName = "Shadow Red",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Shadows"
                  },
                EffectParameter
                  { paramId = "shadow-green",
                    paramName = "Shadow Green",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Shadows"
                  },
                EffectParameter
                  { paramId = "shadow-blue",
                    paramName = "Shadow Blue",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Shadows"
                  },
                -- Midtones
                EffectParameter
                  { paramId = "midtone-red",
                    paramName = "Midtone Red",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Midtones"
                  },
                EffectParameter
                  { paramId = "midtone-green",
                    paramName = "Midtone Green",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Midtones"
                  },
                EffectParameter
                  { paramId = "midtone-blue",
                    paramName = "Midtone Blue",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Midtones"
                  },
                -- Highlights
                EffectParameter
                  { paramId = "highlight-red",
                    paramName = "Highlight Red",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Highlights"
                  },
                EffectParameter
                  { paramId = "highlight-green",
                    paramName = "Highlight Green",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Highlights"
                  },
                EffectParameter
                  { paramId = "highlight-blue",
                    paramName = "Highlight Blue",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Highlights"
                  },
                EffectParameter
                  { paramId = "preserve-luminosity",
                    paramName = "Preserve Luminosity",
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
      ),
      ( "tint",
        EffectDefinition
          { defName = "Tint",
            defCategory = ColorCorrection,
            defDescription = "Map black and white to colors",
            defParameters =
              [ EffectParameter
                  { paramId = "map-black-to",
                    paramName = "Map Black To",
                    paramType = ParamTypeColor,
                    paramValue = ParamColor 0.0 0.0 0.0 (Just 1.0),
                    paramDefaultValue = ParamColor 0.0 0.0 0.0 (Just 1.0),
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "map-white-to",
                    paramName = "Map White To",
                    paramType = ParamTypeColor,
                    paramValue = ParamColor 255.0 255.0 255.0 (Just 1.0),
                    paramDefaultValue = ParamColor 255.0 255.0 255.0 (Just 1.0),
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "amount-to-tint",
                    paramName = "Amount to Tint",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "exposure",
        EffectDefinition
          { defName = "Exposure",
            defCategory = ColorCorrection,
            defDescription = "Adjust exposure like a camera",
            defParameters =
              [ EffectParameter
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
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "offset",
                    paramName = "Offset",
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
                  { paramId = "gamma",
                    paramName = "Gamma",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.1,
                    paramMax = Just 3.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "vibrance",
        EffectDefinition
          { defName = "Vibrance",
            defCategory = ColorCorrection,
            defDescription = "Intelligent saturation that protects skin tones",
            defParameters =
              [ EffectParameter
                  { paramId = "vibrance",
                    paramName = "Vibrance",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
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
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "invert",
        EffectDefinition
          { defName = "Invert",
            defCategory = ColorCorrection,
            defDescription = "Invert colors",
            defParameters =
              [ EffectParameter
                  { paramId = "blend",
                    paramName = "Blend",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "channel",
                    paramName = "Channel",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "rgb",
                    paramDefaultValue = ParamString "rgb",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("RGB", ParamString "rgb"),
                          ("Red", ParamString "red"),
                          ("Green", ParamString "green"),
                          ("Blue", ParamString "blue")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "posterize",
        EffectDefinition
          { defName = "Posterize",
            defCategory = ColorCorrection,
            defDescription = "Reduce color levels for poster effect",
            defParameters =
              [ EffectParameter
                  { paramId = "levels",
                    paramName = "Levels",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 6.0,
                    paramDefaultValue = ParamNumber 6.0,
                    paramMin = Just 2.0,
                    paramMax = Just 256.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "threshold",
        EffectDefinition
          { defName = "Threshold",
            defCategory = ColorCorrection,
            defDescription = "Convert to black and white based on threshold",
            defParameters =
              [ EffectParameter
                  { paramId = "threshold",
                    paramName = "Threshold",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 128.0,
                    paramDefaultValue = ParamNumber 128.0,
                    paramMin = Just 0.0,
                    paramMax = Just 255.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "lut",
        EffectDefinition
          { defName = "LUT (Look-Up Table)",
            defCategory = ColorCorrection,
            defDescription = "Apply .cube color grading look-up table",
            defParameters =
              [ EffectParameter
                  { paramId = "lut-data",
                    paramName = "LUT Data",
                    paramType = ParamTypeString,
                    paramValue = ParamString "",
                    paramDefaultValue = ParamString "",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "intensity",
                    paramName = "Intensity",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      )
    ]

