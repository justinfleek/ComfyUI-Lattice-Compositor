{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Definitions.Generate
  ( generateDefinitions,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..), EffectDefinition (..), EffectParameter (..), EffectParameterType (..), EffectParameterValue (..))

-- | Generate effect definitions
-- Migrated from ui/src/types/effects.ts EFFECT_DEFINITIONS (generate category)
-- 6 effects total
generateDefinitions :: HashMap String EffectDefinition
generateDefinitions =
  HM.fromList
    [ ( "fill",
        EffectDefinition
          { defName = "Fill",
            defCategory = Generate,
            defDescription = "Fill layer with a solid color",
            defParameters =
              [ EffectParameter
                  { paramId = "fill-mask",
                    paramName = "Fill Mask",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "all",
                    paramDefaultValue = ParamString "all",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("All Masks", ParamString "all"),
                          ("None", ParamString "none")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "color",
                    paramName = "Color",
                    paramType = ParamTypeColor,
                    paramValue = ParamColor 255.0 0.0 0.0 (Just 1.0),
                    paramDefaultValue = ParamColor 255.0 0.0 0.0 (Just 1.0),
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
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
                  { paramId = "horizontal-feather",
                    paramName = "Horizontal Feather",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 500.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "vertical-feather",
                    paramName = "Vertical Feather",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 500.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "opacity",
                    paramName = "Opacity",
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
      ( "gradient-ramp",
        EffectDefinition
          { defName = "Gradient Ramp",
            defCategory = Generate,
            defDescription = "Generate a color gradient",
            defParameters =
              [ EffectParameter
                  { paramId = "start-of-ramp",
                    paramName = "Start of Ramp",
                    paramType = ParamTypePoint,
                    paramValue = ParamPoint 0.0 0.5,
                    paramDefaultValue = ParamPoint 0.0 0.5,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "start-color",
                    paramName = "Start Color",
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
                  { paramId = "end-of-ramp",
                    paramName = "End of Ramp",
                    paramType = ParamTypePoint,
                    paramValue = ParamPoint 1.0 0.5,
                    paramDefaultValue = ParamPoint 1.0 0.5,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "end-color",
                    paramName = "End Color",
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
                  { paramId = "ramp-shape",
                    paramName = "Ramp Shape",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "linear",
                    paramDefaultValue = ParamString "linear",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Linear Ramp", ParamString "linear"),
                          ("Radial Ramp", ParamString "radial")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "ramp-scatter",
                    paramName = "Ramp Scatter",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "blend-with-original",
                    paramName = "Blend With Original",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
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
      ( "radio-waves",
        EffectDefinition
          { defName = "Radio Waves",
            defCategory = Generate,
            defDescription = "Generate expanding concentric rings for shockwave effects",
            defParameters =
              [ EffectParameter
                  { paramId = "center",
                    paramName = "Center",
                    paramType = ParamTypePoint,
                    paramValue = ParamPoint 0.5 0.5,
                    paramDefaultValue = ParamPoint 0.5 0.5,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "frequency",
                    paramName = "Frequency",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 4.0,
                    paramDefaultValue = ParamNumber 4.0,
                    paramMin = Just 1.0,
                    paramMax = Just 50.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "expansion",
                    paramName = "Expansion",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 50.0,
                    paramDefaultValue = ParamNumber 50.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "wave-width",
                    paramName = "Wave Width",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 20.0,
                    paramDefaultValue = ParamNumber 20.0,
                    paramMin = Just 1.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "stroke-color",
                    paramName = "Stroke Color",
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
                  { paramId = "background-color",
                    paramName = "Background Color",
                    paramType = ParamTypeColor,
                    paramValue = ParamColor 128.0 128.0 128.0 (Just 1.0),
                    paramDefaultValue = ParamColor 128.0 128.0 128.0 (Just 1.0),
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "fade-start",
                    paramName = "Fade Start",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "fade-end",
                    paramName = "Fade End",
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
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "ellipse",
        EffectDefinition
          { defName = "Ellipse",
            defCategory = Generate,
            defDescription = "Generate ellipse/circle shapes for displacement maps",
            defParameters =
              [ EffectParameter
                  { paramId = "center",
                    paramName = "Center",
                    paramType = ParamTypePoint,
                    paramValue = ParamPoint 0.5 0.5,
                    paramDefaultValue = ParamPoint 0.5 0.5,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "ellipse-width",
                    paramName = "Ellipse Width",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 200.0,
                    paramDefaultValue = ParamNumber 200.0,
                    paramMin = Just 1.0,
                    paramMax = Just 4000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "ellipse-height",
                    paramName = "Ellipse Height",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 200.0,
                    paramDefaultValue = ParamNumber 200.0,
                    paramMin = Just 1.0,
                    paramMax = Just 4000.0,
                    paramStep = Nothing,
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
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "stroke-width",
                    paramName = "Stroke Width",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 500.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "stroke-color",
                    paramName = "Stroke Color",
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
                  { paramId = "background-color",
                    paramName = "Background Color",
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
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "audio-spectrum",
        EffectDefinition
          { defName = "Audio Spectrum",
            defCategory = Generate,
            defDescription = "Visualize audio frequency spectrum",
            defParameters =
              [ EffectParameter
                  { paramId = "start-point-x",
                    paramName = "Start Point X",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-1000.0),
                    paramMax = Just 4000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "start-point-y",
                    paramName = "Start Point Y",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 360.0,
                    paramDefaultValue = ParamNumber 360.0,
                    paramMin = Just (-1000.0),
                    paramMax = Just 2000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "end-point-x",
                    paramName = "End Point X",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1920.0,
                    paramDefaultValue = ParamNumber 1920.0,
                    paramMin = Just (-1000.0),
                    paramMax = Just 4000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "end-point-y",
                    paramName = "End Point Y",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 360.0,
                    paramDefaultValue = ParamNumber 360.0,
                    paramMin = Just (-1000.0),
                    paramMax = Just 2000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "start-frequency",
                    paramName = "Start Frequency",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 20.0,
                    paramDefaultValue = ParamNumber 20.0,
                    paramMin = Just 20.0,
                    paramMax = Just 20000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "end-frequency",
                    paramName = "End Frequency",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10000.0,
                    paramDefaultValue = ParamNumber 10000.0,
                    paramMin = Just 20.0,
                    paramMax = Just 20000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "frequency-bands",
                    paramName = "Frequency Bands",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 64.0,
                    paramDefaultValue = ParamNumber 64.0,
                    paramMin = Just 8.0,
                    paramMax = Just 256.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "max-height",
                    paramName = "Max Height",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 10.0,
                    paramMax = Just 500.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "thickness",
                    paramName = "Thickness",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 3.0,
                    paramDefaultValue = ParamNumber 3.0,
                    paramMin = Just 1.0,
                    paramMax = Just 20.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "inside-color",
                    paramName = "Inside Color",
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
                  { paramId = "outside-color",
                    paramName = "Outside Color",
                    paramType = ParamTypeColor,
                    paramValue = ParamColor 74.0 144.0 217.0 (Just 1.0),
                    paramDefaultValue = ParamColor 74.0 144.0 217.0 (Just 1.0),
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "audio-duration",
                    paramName = "Audio Duration",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 50.0,
                    paramDefaultValue = ParamNumber 50.0,
                    paramMin = Just 0.0,
                    paramMax = Just 1000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "audio-offset",
                    paramName = "Audio Offset",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-1000.0),
                    paramMax = Just 1000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "audio-waveform",
        EffectDefinition
          { defName = "Audio Waveform",
            defCategory = Generate,
            defDescription = "Visualize audio waveform",
            defParameters =
              [ EffectParameter
                  { paramId = "start-point-x",
                    paramName = "Start Point X",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-1000.0),
                    paramMax = Just 4000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "start-point-y",
                    paramName = "Start Point Y",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 360.0,
                    paramDefaultValue = ParamNumber 360.0,
                    paramMin = Just (-1000.0),
                    paramMax = Just 2000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "end-point-x",
                    paramName = "End Point X",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1920.0,
                    paramDefaultValue = ParamNumber 1920.0,
                    paramMin = Just (-1000.0),
                    paramMax = Just 4000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "end-point-y",
                    paramName = "End Point Y",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 360.0,
                    paramDefaultValue = ParamNumber 360.0,
                    paramMin = Just (-1000.0),
                    paramMax = Just 2000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "displayed-samples",
                    paramName = "Displayed Samples",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 200.0,
                    paramDefaultValue = ParamNumber 200.0,
                    paramMin = Just 50.0,
                    paramMax = Just 1000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "max-height",
                    paramName = "Max Height",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 10.0,
                    paramMax = Just 500.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "thickness",
                    paramName = "Thickness",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 2.0,
                    paramDefaultValue = ParamNumber 2.0,
                    paramMin = Just 1.0,
                    paramMax = Just 20.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "inside-color",
                    paramName = "Inside Color",
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
                  { paramId = "outside-color",
                    paramName = "Outside Color",
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
                  { paramId = "audio-duration",
                    paramName = "Audio Duration",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 50.0,
                    paramDefaultValue = ParamNumber 50.0,
                    paramMin = Just 0.0,
                    paramMax = Just 1000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "audio-offset",
                    paramName = "Audio Offset",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-1000.0),
                    paramMax = Just 1000.0,
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
