{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Definitions.Utility
  ( utilityDefinitions,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..), EffectDefinition (..), EffectParameter (..), EffectParameterType (..), EffectParameterValue (..))

-- | Utility effect definitions
-- Migrated from ui/src/types/effects.ts EFFECT_DEFINITIONS (utility category)
-- 8 effects total - expression control effects
utilityDefinitions :: HashMap String EffectDefinition
utilityDefinitions =
  HM.fromList
    [       ( "slider-control",
        EffectDefinition
          { defName = "Slider Control",
            defCategory = Utility,
            defDescription = "Provides an animatable numeric value for expressions. Use effect(\"Slider Control\")(\"Slider\") in expressions.",
            defParameters =
              [ EffectParameter
                  { paramId = "slider",
                    paramName = "Slider",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-1000000.0),
                    paramMax = Just 1000000.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "checkbox-control",
        EffectDefinition
          { defName = "Checkbox Control",
            defCategory = Utility,
            defDescription = "Provides a boolean toggle for expressions. Returns 1 when checked, 0 when unchecked.",
            defParameters =
              [ EffectParameter
                  { paramId = "checkbox",
                    paramName = "Checkbox",
                    paramType = ParamTypeCheckbox,
                    paramValue = ParamBool False,
                    paramDefaultValue = ParamBool False,
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
      ( "dropdown-menu-control",
        EffectDefinition
          { defName = "Dropdown Menu Control",
            defCategory = Utility,
            defDescription = "Provides a menu selection for expressions. Returns the index (1-based) of the selected option.",
            defParameters =
              [ EffectParameter
                  { paramId = "menu",
                    paramName = "Menu",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "1",
                    paramDefaultValue = ParamString "1",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Option 1", ParamString "1"),
                          ("Option 2", ParamString "2"),
                          ("Option 3", ParamString "3")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "color-control",
        EffectDefinition
          { defName = "Color Control",
            defCategory = Utility,
            defDescription = "Provides an animatable color value for expressions.",
            defParameters =
              [ EffectParameter
                  { paramId = "color",
                    paramName = "Color",
                    paramType = ParamTypeColor,
                    paramValue = ParamColor 255.0 0.0 0.0 Nothing,
                    paramDefaultValue = ParamColor 255.0 0.0 0.0 Nothing,
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
      ( "point-control",
        EffectDefinition
          { defName = "Point Control",
            defCategory = Utility,
            defDescription = "Provides an animatable 2D point for expressions.",
            defParameters =
              [ EffectParameter
                  { paramId = "point",
                    paramName = "Point",
                    paramType = ParamTypePoint,
                    paramValue = ParamPoint 0.0 0.0,
                    paramDefaultValue = ParamPoint 0.0 0.0,
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
      ( "3d-point-control",
        EffectDefinition
          { defName = "3D Point Control",
            defCategory = Utility,
            defDescription = "Provides an animatable 3D point for expressions.",
            defParameters =
              [ EffectParameter
                  { paramId = "3d-point",
                    paramName = "3D Point",
                    paramType = ParamTypePoint3D,
                    paramValue = ParamPoint3D 0.0 0.0 0.0,
                    paramDefaultValue = ParamPoint3D 0.0 0.0 0.0,
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
      ( "angle-control",
        EffectDefinition
          { defName = "Angle Control",
            defCategory = Utility,
            defDescription = "Provides an animatable angle value for expressions.",
            defParameters =
              [ EffectParameter
                  { paramId = "angle",
                    paramName = "Angle",
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
      ( "layer-control",
        EffectDefinition
          { defName = "Layer Control",
            defCategory = Utility,
            defDescription = "Provides a layer reference for expressions.",
            defParameters =
              [ EffectParameter
                  { paramId = "layer",
                    paramName = "Layer",
                    paramType = ParamTypeLayer,
                    paramValue = ParamNull,
                    paramDefaultValue = ParamNull,
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
