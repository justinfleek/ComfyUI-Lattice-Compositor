{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Definitions.BlurSharpen
  ( blurSharpenDefinitions,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..), EffectDefinition (..), EffectParameter (..), EffectParameterType (..), EffectParameterValue (..))

-- | Blur & Sharpen effect definitions
-- Migrated from ui/src/types/effects.ts EFFECT_DEFINITIONS (blur-sharpen category)
blurSharpenDefinitions :: HashMap String EffectDefinition
blurSharpenDefinitions =
  HM.fromList
    [ ( "gaussian-blur",
        EffectDefinition
          { defName = "Gaussian Blur",
            defCategory = BlurSharpen,
            defDescription = "Smooth, bell-curve blur",
            defParameters =
              [ EffectParameter
                  { paramId = "blurriness",
                    paramName = "Blurriness",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10.0,
                    paramDefaultValue = ParamNumber 10.0,
                    paramMin = Just 0.0,
                    paramMax = Just 250.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "blur-dimensions",
                    paramName = "Blur Dimensions",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "both",
                    paramDefaultValue = ParamString "both",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Horizontal and Vertical", ParamString "both"),
                          ("Horizontal", ParamString "horizontal"),
                          ("Vertical", ParamString "vertical")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "repeat-edge-pixels",
                    paramName = "Repeat Edge Pixels",
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
      ( "directional-blur",
        EffectDefinition
          { defName = "Directional Blur",
            defCategory = BlurSharpen,
            defDescription = "Blur in a specific direction",
            defParameters =
              [ EffectParameter
                  { paramId = "direction",
                    paramName = "Direction",
                    paramType = ParamTypeAngle,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "blur-length",
                    paramName = "Blur Length",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10.0,
                    paramDefaultValue = ParamNumber 10.0,
                    paramMin = Just 0.0,
                    paramMax = Just 500.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "radial-blur",
        EffectDefinition
          { defName = "Radial Blur",
            defCategory = BlurSharpen,
            defDescription = "Spin or zoom blur effect",
            defParameters =
              [ EffectParameter
                  { paramId = "amount",
                    paramName = "Amount",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10.0,
                    paramDefaultValue = ParamNumber 10.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
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
                  { paramId = "type",
                    paramName = "Type",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "spin",
                    paramDefaultValue = ParamString "spin",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Spin", ParamString "spin"),
                          ("Zoom", ParamString "zoom")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "antialiasing",
                    paramName = "Antialiasing",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "high",
                    paramDefaultValue = ParamString "high",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Low", ParamString "low"),
                          ("Medium", ParamString "medium"),
                          ("High", ParamString "high")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "box-blur",
        EffectDefinition
          { defName = "Box Blur",
            defCategory = BlurSharpen,
            defDescription = "Fast uniform blur using box averaging",
            defParameters =
              [ EffectParameter
                  { paramId = "blur-radius",
                    paramName = "Blur Radius",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 5.0,
                    paramDefaultValue = ParamNumber 5.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "iterations",
                    paramName = "Iterations",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 1.0,
                    paramMax = Just 5.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "sharpen",
        EffectDefinition
          { defName = "Sharpen",
            defCategory = BlurSharpen,
            defDescription = "Increase image contrast at edges",
            defParameters =
              [ EffectParameter
                  { paramId = "sharpen-amount",
                    paramName = "Sharpen Amount",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 50.0,
                    paramDefaultValue = ParamNumber 50.0,
                    paramMin = Just 0.0,
                    paramMax = Just 500.0,
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
