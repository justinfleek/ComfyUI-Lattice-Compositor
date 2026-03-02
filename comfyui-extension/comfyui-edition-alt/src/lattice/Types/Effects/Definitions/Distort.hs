{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Definitions.Distort
  ( distortDefinitions,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..), EffectDefinition (..), EffectParameter (..), EffectParameterType (..), EffectParameterValue (..))

-- | Distort effect definitions
-- Migrated from ui/src/types/effects.ts EFFECT_DEFINITIONS (distort category)
-- 7 effects total - will split if file exceeds ~500 lines
distortDefinitions :: HashMap String EffectDefinition
distortDefinitions =
  HM.fromList
    [ ( "transform",
        EffectDefinition
          { defName = "Transform",
            defCategory = Distort,
            defDescription = "Transform layer with anchor point control",
            defParameters =
              [ EffectParameter
                  { paramId = "anchor-point",
                    paramName = "Anchor Point",
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
                  { paramId = "position",
                    paramName = "Position",
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
                  { paramId = "scale-height",
                    paramName = "Scale Height",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just (-10000.0),
                    paramMax = Just 10000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "scale-width",
                    paramName = "Scale Width",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just (-10000.0),
                    paramMax = Just 10000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "skew",
                    paramName = "Skew",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-85.0),
                    paramMax = Just 85.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "skew-axis",
                    paramName = "Skew Axis",
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
                  { paramId = "rotation",
                    paramName = "Rotation",
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
      ( "warp",
        EffectDefinition
          { defName = "Warp",
            defCategory = Distort,
            defDescription = "Apply warp distortion",
            defParameters =
              [ EffectParameter
                  { paramId = "warp-style",
                    paramName = "Warp Style",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "arc",
                    paramDefaultValue = ParamString "arc",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Arc", ParamString "arc"),
                          ("Arc Lower", ParamString "arc-lower"),
                          ("Arc Upper", ParamString "arc-upper"),
                          ("Arch", ParamString "arch"),
                          ("Bulge", ParamString "bulge"),
                          ("Shell Lower", ParamString "shell-lower"),
                          ("Shell Upper", ParamString "shell-upper"),
                          ("Flag", ParamString "flag"),
                          ("Wave", ParamString "wave"),
                          ("Fish", ParamString "fish"),
                          ("Rise", ParamString "rise"),
                          ("Fisheye", ParamString "fisheye"),
                          ("Inflate", ParamString "inflate"),
                          ("Squeeze", ParamString "squeeze"),
                          ("Twist", ParamString "twist")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "bend",
                    paramName = "Bend",
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
                  { paramId = "horizontal-distortion",
                    paramName = "Horizontal Distortion",
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
                  { paramId = "vertical-distortion",
                    paramName = "Vertical Distortion",
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
      ( "displacement-map",
        EffectDefinition
          { defName = "Displacement Map",
            defCategory = Distort,
            defDescription = "Displace pixels using a map layer or procedural pattern",
            defParameters =
              [ EffectParameter
                  { paramId = "displacement-map-layer",
                    paramName = "Displacement Map Layer",
                    paramType = ParamTypeLayer,
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
                  { paramId = "map-type",
                    paramName = "Map Type",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "layer",
                    paramDefaultValue = ParamString "layer",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Use Layer", ParamString "layer"),
                          ("Noise", ParamString "noise"),
                          ("Gradient H", ParamString "gradient-h"),
                          ("Gradient V", ParamString "gradient-v"),
                          ("Radial", ParamString "radial"),
                          ("Sine H", ParamString "sine-h"),
                          ("Sine V", ParamString "sine-v"),
                          ("Checker", ParamString "checker")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "displacement-map-behavior",
                    paramName = "Displacement Map Behavior",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "stretch",
                    paramDefaultValue = ParamString "stretch",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Center Map", ParamString "center"),
                          ("Stretch Map to Fit", ParamString "stretch"),
                          ("Tile Map", ParamString "tile")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "use-for-horizontal",
                    paramName = "Use For Horizontal",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "red",
                    paramDefaultValue = ParamString "red",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Red", ParamString "red"),
                          ("Green", ParamString "green"),
                          ("Blue", ParamString "blue"),
                          ("Alpha", ParamString "alpha"),
                          ("Luminance", ParamString "luminance"),
                          ("Off", ParamString "off")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "max-horizontal",
                    paramName = "Max Horizontal",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-4000.0),
                    paramMax = Just 4000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "use-for-vertical",
                    paramName = "Use For Vertical",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "green",
                    paramDefaultValue = ParamString "green",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Red", ParamString "red"),
                          ("Green", ParamString "green"),
                          ("Blue", ParamString "blue"),
                          ("Alpha", ParamString "alpha"),
                          ("Luminance", ParamString "luminance"),
                          ("Off", ParamString "off")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "max-vertical",
                    paramName = "Max Vertical",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just (-4000.0),
                    paramMax = Just 4000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "edge-behavior",
                    paramName = "Edge Behavior",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "off",
                    paramDefaultValue = ParamString "off",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Clip", ParamString "off"),
                          ("Wrap Pixels", ParamString "tiles"),
                          ("Mirror Pixels", ParamString "mirror")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "map-scale",
                    paramName = "Map Scale",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.1,
                    paramMax = Just 10.0,
                    paramStep = Just 0.1,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Just "Procedural"
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "ripple",
        EffectDefinition
          { defName = "Ripple",
            defCategory = Distort,
            defDescription = "Water ripple distortion",
            defParameters =
              [ EffectParameter
                  { paramId = "radius",
                    paramName = "Radius",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 1.0,
                    paramMax = Just 500.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "wave-length",
                    paramName = "Wave Length",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 30.0,
                    paramDefaultValue = ParamNumber 30.0,
                    paramMin = Just 1.0,
                    paramMax = Just 999.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "amplitude",
                    paramName = "Amplitude",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10.0,
                    paramDefaultValue = ParamNumber 10.0,
                    paramMin = Just (-100.0),
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
                  { paramId = "phase",
                    paramName = "Phase",
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
      ( "turbulent-displace",
        EffectDefinition
          { defName = "Turbulent Displace",
            defCategory = Distort,
            defDescription = "Procedural organic distortion using turbulent noise",
            defParameters =
              [ EffectParameter
                  { paramId = "displacement",
                    paramName = "Displacement",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "turbulent",
                    paramDefaultValue = ParamString "turbulent",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Turbulent", ParamString "turbulent"),
                          ("Bulge", ParamString "bulge"),
                          ("Twist", ParamString "twist"),
                          ("Turbulent Smoother", ParamString "turbulent-smoother"),
                          ("Horizontal Displacement", ParamString "horizontal"),
                          ("Vertical Displacement", ParamString "vertical"),
                          ("Cross Displacement", ParamString "cross")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "amount",
                    paramName = "Amount",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 50.0,
                    paramDefaultValue = ParamNumber 50.0,
                    paramMin = Just 0.0,
                    paramMax = Just 1000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "size",
                    paramName = "Size",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 1.0,
                    paramMax = Just 1000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "complexity",
                    paramName = "Complexity",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 3.0,
                    paramDefaultValue = ParamNumber 3.0,
                    paramMin = Just 1.0,
                    paramMax = Just 10.0,
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
                  },
                EffectParameter
                  { paramId = "cycle-evolution",
                    paramName = "Cycle Evolution",
                    paramType = ParamTypeCheckbox,
                    paramValue = ParamBool False,
                    paramDefaultValue = ParamBool False,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Just "Evolution Options"
                  },
                EffectParameter
                  { paramId = "cycle-revolutions",
                    paramName = "Cycle Revolutions",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 1.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Just "Evolution Options"
                  },
                EffectParameter
                  { paramId = "random-seed",
                    paramName = "Random Seed",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.0,
                    paramDefaultValue = ParamNumber 0.0,
                    paramMin = Just 0.0,
                    paramMax = Just 99999.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "offset",
                    paramName = "Offset",
                    paramType = ParamTypePoint,
                    paramValue = ParamPoint 0.0 0.0,
                    paramDefaultValue = ParamPoint 0.0 0.0,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "pinning",
                    paramName = "Pinning",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "none",
                    paramDefaultValue = ParamString "none",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("None", ParamString "none"),
                          ("Pin All", ParamString "all"),
                          ("Pin Horizontally", ParamString "horizontal"),
                          ("Pin Vertically", ParamString "vertical")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "ripple-distort",
        EffectDefinition
          { defName = "Ripple",
            defCategory = Distort,
            defDescription = "Concentric wave distortion from center point",
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
                  { paramId = "radius",
                    paramName = "Radius",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 200.0,
                    paramDefaultValue = ParamNumber 200.0,
                    paramMin = Just 1.0,
                    paramMax = Just 2000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "wave-length",
                    paramName = "Wave Length",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 50.0,
                    paramDefaultValue = ParamNumber 50.0,
                    paramMin = Just 1.0,
                    paramMax = Just 500.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "amplitude",
                    paramName = "Amplitude",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 20.0,
                    paramDefaultValue = ParamNumber 20.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "phase",
                    paramName = "Phase",
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
                  { paramId = "decay",
                    paramName = "Decay",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 50.0,
                    paramDefaultValue = ParamNumber 50.0,
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
      --                                                                      // note
      -- Will be added when meshWarp.ts is migrated (Phase 4.1)
    ]
