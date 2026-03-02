{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Definitions.Time
  ( timeDefinitions,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..), EffectDefinition (..), EffectParameter (..), EffectParameterType (..), EffectParameterValue (..))

-- | Time effect definitions
-- Migrated from ui/src/types/effects.ts EFFECT_DEFINITIONS (time category)
-- 4 effects total
timeDefinitions :: HashMap String EffectDefinition
timeDefinitions =
  HM.fromList
    [ ( "echo",
        EffectDefinition
          { defName = "Echo",
            defCategory = Time,
            defDescription = "Create motion trails by compositing previous frames",
            defParameters =
              [ EffectParameter
                  { paramId = "echo-time",
                    paramName = "Echo Time",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber (-0.033),
                    paramDefaultValue = ParamNumber (-0.033),
                    paramMin = Just (-2.0),
                    paramMax = Just 2.0,
                    paramStep = Just 0.001,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "number-of-echoes",
                    paramName = "Number of Echoes",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 8.0,
                    paramDefaultValue = ParamNumber 8.0,
                    paramMin = Just 1.0,
                    paramMax = Just 50.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "starting-intensity",
                    paramName = "Starting Intensity",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.0,
                    paramMax = Just 2.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "decay",
                    paramName = "Decay",
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
                  { paramId = "echo-operator",
                    paramName = "Echo Operator",
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
                          ("Maximum", ParamString "maximum"),
                          ("Minimum", ParamString "minimum"),
                          ("Composite in Back", ParamString "composite_back"),
                          ("Composite in Front", ParamString "composite_front"),
                          ("Blend", ParamString "blend")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "posterize-time",
        EffectDefinition
          { defName = "Posterize Time",
            defCategory = Time,
            defDescription = "Reduce temporal resolution for stylized frame rate",
            defParameters =
              [ EffectParameter
                  { paramId = "frame-rate",
                    paramName = "Frame Rate",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 12.0,
                    paramDefaultValue = ParamNumber 12.0,
                    paramMin = Just 1.0,
                    paramMax = Just 60.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "freeze-frame",
        EffectDefinition
          { defName = "Freeze Frame",
            defCategory = Time,
            defDescription = "Freezes the layer at a specific source frame",
            defParameters =
              [ EffectParameter
                  { paramId = "freeze-at-frame",
                    paramName = "Freeze At Frame",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
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
      ( "time-displacement",
        EffectDefinition
          { defName = "Time Displacement",
            defCategory = Time,
            defDescription = "Displace pixels in time based on luminance values",
            defParameters =
              [ EffectParameter
                  { paramId = "max-displacement",
                    paramName = "Max Displacement",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10.0,
                    paramDefaultValue = ParamNumber 10.0,
                    paramMin = Just 0.0,
                    paramMax = Just 60.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "time-resolution",
                    paramName = "Time Resolution",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "frame",
                    paramDefaultValue = ParamString "frame",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Frame", ParamString "frame"),
                          ("Half Frame", ParamString "half"),
                          ("Quarter Frame", ParamString "quarter")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      )
    ]
