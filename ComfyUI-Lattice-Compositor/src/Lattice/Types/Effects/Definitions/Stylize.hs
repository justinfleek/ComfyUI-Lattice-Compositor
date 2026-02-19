{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Definitions.Stylize
  ( stylizeBasicDefinitions,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..), EffectDefinition (..), EffectParameter (..), EffectParameterType (..), EffectParameterValue (..))

-- | Stylize effect definitions (Basic)
-- Migrated from ui/src/types/effects.ts EFFECT_DEFINITIONS (stylize category)
-- 12 basic effects - cinematic-bloom moved to StylizeAdvanced.hs
stylizeBasicDefinitions :: HashMap String EffectDefinition
stylizeBasicDefinitions =
  HM.fromList
    [ ( "glow",
        EffectDefinition
          { defName = "Glow",
            defCategory = Stylize,
            defDescription = "Add a glow effect",
            defParameters =
              [ EffectParameter
                  { paramId = "glow-threshold",
                    paramName = "Glow Threshold",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 60.0,
                    paramDefaultValue = ParamNumber 60.0,
                    paramMin = Just 0.0,
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "glow-radius",
                    paramName = "Glow Radius",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 25.0,
                    paramDefaultValue = ParamNumber 25.0,
                    paramMin = Just 0.0,
                    paramMax = Just 500.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "glow-intensity",
                    paramName = "Glow Intensity",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.0,
                    paramMax = Just 10.0,
                    paramStep = Just 0.1,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "composite-original",
                    paramName = "Composite Original",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "on-top",
                    paramDefaultValue = ParamString "on-top",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("On Top", ParamString "on-top"),
                          ("Behind", ParamString "behind"),
                          ("None", ParamString "none")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "glow-colors",
                    paramName = "Glow Colors",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "original",
                    paramDefaultValue = ParamString "original",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Original Colors", ParamString "original"),
                          ("A & B Colors", ParamString "ab")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "color-a",
                    paramName = "Color A",
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
                  { paramId = "color-b",
                    paramName = "Color B",
                    paramType = ParamTypeColor,
                    paramValue = ParamColor 255.0 128.0 0.0 (Just 1.0),
                    paramDefaultValue = ParamColor 255.0 128.0 0.0 (Just 1.0),
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "color-looping",
                    paramName = "Color Looping",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "none",
                    paramDefaultValue = ParamString "none",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("None", ParamString "none"),
                          ("Sawtooth A>B", ParamString "sawtooth_ab"),
                          ("Sawtooth B>A", ParamString "sawtooth_ba"),
                          ("Triangle A>B>A", ParamString "triangle")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "color-looping-speed",
                    paramName = "Color Looping Speed",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 1.0,
                    paramDefaultValue = ParamNumber 1.0,
                    paramMin = Just 0.1,
                    paramMax = Just 10.0,
                    paramStep = Just 0.1,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "glow-dimensions",
                    paramName = "Glow Dimensions",
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
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "drop-shadow",
        EffectDefinition
          { defName = "Drop Shadow",
            defCategory = Stylize,
            defDescription = "Add a drop shadow",
            defParameters =
              [ EffectParameter
                  { paramId = "shadow-color",
                    paramName = "Shadow Color",
                    paramType = ParamTypeColor,
                    paramValue = ParamColor 0.0 0.0 0.0 (Just 0.5),
                    paramDefaultValue = ParamColor 0.0 0.0 0.0 (Just 0.5),
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
                  { paramId = "direction",
                    paramName = "Direction",
                    paramType = ParamTypeAngle,
                    paramValue = ParamNumber 135.0,
                    paramDefaultValue = ParamNumber 135.0,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "distance",
                    paramName = "Distance",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 5.0,
                    paramDefaultValue = ParamNumber 5.0,
                    paramMin = Just 0.0,
                    paramMax = Just 1000.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "softness",
                    paramName = "Softness",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 5.0,
                    paramDefaultValue = ParamNumber 5.0,
                    paramMin = Just 0.0,
                    paramMax = Just 250.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "shadow-only",
                    paramName = "Shadow Only",
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
      ( "rgb-split",
        EffectDefinition
          { defName = "RGB Split",
            defCategory = Stylize,
            defDescription = "Chromatic aberration / RGB channel separation",
            defParameters =
              [ EffectParameter
                  { paramId = "red-offset-x",
                    paramName = "Red Offset X",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 5.0,
                    paramDefaultValue = ParamNumber 5.0,
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "red-offset-y",
                    paramName = "Red Offset Y",
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
                  { paramId = "green-offset-x",
                    paramName = "Green Offset X",
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
                  { paramId = "green-offset-y",
                    paramName = "Green Offset Y",
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
                  { paramId = "blue-offset-x",
                    paramName = "Blue Offset X",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber (-5.0),
                    paramDefaultValue = ParamNumber (-5.0),
                    paramMin = Just (-100.0),
                    paramMax = Just 100.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "blue-offset-y",
                    paramName = "Blue Offset Y",
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
                  { paramId = "blend-mode",
                    paramName = "Blend Mode",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "screen",
                    paramDefaultValue = ParamString "screen",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Screen", ParamString "screen"),
                          ("Add", ParamString "add"),
                          ("Normal", ParamString "normal")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "scanlines",
        EffectDefinition
          { defName = "Scan Lines",
            defCategory = Stylize,
            defDescription = "CRT monitor scan line effect",
            defParameters =
              [ EffectParameter
                  { paramId = "line-width",
                    paramName = "Line Width",
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
                  { paramId = "line-spacing",
                    paramName = "Line Spacing",
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
                  { paramId = "opacity",
                    paramName = "Opacity",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.3,
                    paramDefaultValue = ParamNumber 0.3,
                    paramMin = Just 0.0,
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "direction",
                    paramName = "Direction",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "horizontal",
                    paramDefaultValue = ParamString "horizontal",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Horizontal", ParamString "horizontal"),
                          ("Vertical", ParamString "vertical")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "animate",
                    paramName = "Animate",
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
      ( "vhs",
        EffectDefinition
          { defName = "VHS",
            defCategory = Stylize,
            defDescription = "VHS tape distortion effect",
            defParameters =
              [ EffectParameter
                  { paramId = "tracking",
                    paramName = "Tracking",
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
                  { paramId = "noise",
                    paramName = "Noise",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.3,
                    paramDefaultValue = ParamNumber 0.3,
                    paramMin = Just 0.0,
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "color-bleed",
                    paramName = "Color Bleed",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 3.0,
                    paramDefaultValue = ParamNumber 3.0,
                    paramMin = Just 0.0,
                    paramMax = Just 20.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "jitter",
                    paramName = "Jitter",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.5,
                    paramDefaultValue = ParamNumber 0.5,
                    paramMin = Just 0.0,
                    paramMax = Just 5.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "rolling-bands",
                    paramName = "Rolling Bands",
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
      ( "pixel-sort",
        EffectDefinition
          { defName = "Pixel Sort",
            defCategory = Stylize,
            defDescription = "Sort pixels by color properties within intervals",
            defParameters =
              [ EffectParameter
                  { paramId = "direction",
                    paramName = "Direction",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "horizontal",
                    paramDefaultValue = ParamString "horizontal",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Horizontal", ParamString "horizontal"),
                          ("Vertical", ParamString "vertical")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "threshold",
                    paramName = "Threshold",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.25,
                    paramDefaultValue = ParamNumber 0.25,
                    paramMin = Just 0.0,
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "smoothing",
                    paramName = "Smoothing",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 0.1,
                    paramDefaultValue = ParamNumber 0.1,
                    paramMin = Just 0.0,
                    paramMax = Just 1.0,
                    paramStep = Just 0.01,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "sort-by",
                    paramName = "Sort By",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "saturation",
                    paramDefaultValue = ParamString "saturation",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Saturation", ParamString "saturation"),
                          ("Brightness", ParamString "brightness"),
                          ("Hue", ParamString "hue")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "reverse",
                    paramName = "Reverse",
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
      ( "glitch",
        EffectDefinition
          { defName = "Glitch",
            defCategory = Stylize,
            defDescription = "Digital corruption/distortion effect",
            defParameters =
              [ EffectParameter
                  { paramId = "glitch-amount",
                    paramName = "Glitch Amount",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 5.0,
                    paramDefaultValue = ParamNumber 5.0,
                    paramMin = Just 0.0,
                    paramMax = Just 10.0,
                    paramStep = Just 0.1,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "color-offset",
                    paramName = "Color Offset",
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
                  { paramId = "block-size",
                    paramName = "Block Size",
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
                  { paramId = "seed",
                    paramName = "Seed",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 12345.0,
                    paramDefaultValue = ParamNumber 12345.0,
                    paramMin = Just 0.0,
                    paramMax = Just 99999.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "scanlines",
                    paramName = "Scanlines",
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
      ( "halftone",
        EffectDefinition
          { defName = "Halftone",
            defCategory = Stylize,
            defDescription = "Print-style dot pattern effect",
            defParameters =
              [ EffectParameter
                  { paramId = "dot-size",
                    paramName = "Dot Size",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 6.0,
                    paramDefaultValue = ParamNumber 6.0,
                    paramMin = Just 2.0,
                    paramMax = Just 20.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "angle",
                    paramName = "Angle",
                    paramType = ParamTypeAngle,
                    paramValue = ParamNumber 45.0,
                    paramDefaultValue = ParamNumber 45.0,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "color-mode",
                    paramName = "Color Mode",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "grayscale",
                    paramDefaultValue = ParamString "grayscale",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Grayscale", ParamString "grayscale"),
                          ("RGB", ParamString "rgb"),
                          ("CMYK", ParamString "cmyk")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "dither",
        EffectDefinition
          { defName = "Dither",
            defCategory = Stylize,
            defDescription = "Reduce color depth with dithering patterns",
            defParameters =
              [ EffectParameter
                  { paramId = "method",
                    paramName = "Method",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "ordered",
                    paramDefaultValue = ParamString "ordered",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("Ordered (Bayer)", ParamString "ordered"),
                          ("Floyd-Steinberg", ParamString "floyd_steinberg"),
                          ("Atkinson", ParamString "atkinson")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "levels",
                    paramName = "Levels",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 4.0,
                    paramDefaultValue = ParamNumber 4.0,
                    paramMin = Just 2.0,
                    paramMax = Just 256.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "matrix-size",
                    paramName = "Matrix Size",
                    paramType = ParamTypeDropdown,
                    paramValue = ParamString "4",
                    paramDefaultValue = ParamString "4",
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions =
                      Just
                        [ ("2x2", ParamString "2"),
                          ("4x4", ParamString "4"),
                          ("8x8", ParamString "8")
                        ],
                    paramAnimatable = False,
                    paramGroup = Nothing
                  }
              ],
            defFragmentShader = Nothing
          }
      ),
      ( "emboss",
        EffectDefinition
          { defName = "Emboss",
            defCategory = Stylize,
            defDescription = "Create embossed relief effect",
            defParameters =
              [ EffectParameter
                  { paramId = "direction",
                    paramName = "Direction",
                    paramType = ParamTypeAngle,
                    paramValue = ParamNumber 135.0,
                    paramDefaultValue = ParamNumber 135.0,
                    paramMin = Nothing,
                    paramMax = Nothing,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "height",
                    paramName = "Height",
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
                  { paramId = "amount",
                    paramName = "Amount",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 100.0,
                    paramDefaultValue = ParamNumber 100.0,
                    paramMin = Just 1.0,
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
      ( "find-edges",
        EffectDefinition
          { defName = "Find Edges",
            defCategory = Stylize,
            defDescription = "Detect and highlight edges",
            defParameters =
              [ EffectParameter
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
                  { paramId = "blend-with-original",
                    paramName = "Blend with Original",
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
      ( "mosaic",
        EffectDefinition
          { defName = "Mosaic",
            defCategory = Stylize,
            defDescription = "Pixelate effect",
            defParameters =
              [ EffectParameter
                  { paramId = "horizontal-blocks",
                    paramName = "Horizontal Blocks",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10.0,
                    paramDefaultValue = ParamNumber 10.0,
                    paramMin = Just 2.0,
                    paramMax = Just 200.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "vertical-blocks",
                    paramName = "Vertical Blocks",
                    paramType = ParamTypeNumber,
                    paramValue = ParamNumber 10.0,
                    paramDefaultValue = ParamNumber 10.0,
                    paramMin = Just 2.0,
                    paramMax = Just 200.0,
                    paramStep = Nothing,
                    paramOptions = Nothing,
                    paramAnimatable = True,
                    paramGroup = Nothing
                  },
                EffectParameter
                  { paramId = "sharp-corners",
                    paramName = "Sharp Corners",
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
      -- NOTE: cinematic-bloom is complex (many parameters) - moved to StylizeAdvanced.hs
    ]
