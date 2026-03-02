{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.AnimationPresets
  ( AnimationPreset (..),
    KeyframeProperty (..),
    PresetKeyframe (..),
    BezierHandle (..),
    animationPresets,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectParameterValue (..))

-- | Bezier curve handle for keyframe interpolation
data BezierHandle = BezierHandle
  { handleX :: Double,
    handleY :: Double
  }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Keyframe within a preset
data PresetKeyframe = PresetKeyframe
  { presetTime :: Double, -- 0-1 normalized
    presetValue :: EffectParameterValue, -- Type-safe effect parameter value
    presetInHandle :: Maybe BezierHandle,
    presetOutHandle :: Maybe BezierHandle
  }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Property keyframes for a preset
data KeyframeProperty = KeyframeProperty
  { propProperty :: String,
    propKeyframes :: [PresetKeyframe]
  }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Animation preset definition
data AnimationPreset = AnimationPreset
  { presetId :: String,
    presetName :: String,
    presetCategory :: String,
    presetDescription :: String,
    presetKeyframes :: [KeyframeProperty]
  }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Animation presets
-- Migrated from ui/src/types/effects.ts ANIMATION_PRESETS array
animationPresets :: [AnimationPreset]
animationPresets =
  [ AnimationPreset
      { presetId = "fade-in",
        presetName = "Fade In",
        presetCategory = "Fade",
        presetDescription = "Fade from transparent to opaque",
        presetKeyframes =
          [ KeyframeProperty
              { propProperty = "opacity",
                propKeyframes =
                  [ PresetKeyframe
                      { presetTime = 0.0,
                        presetValue = ParamNumber 0.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Just (BezierHandle 0.4 0.0)
                      },
                    PresetKeyframe
                      { presetTime = 1.0,
                        presetValue = ParamNumber 100.0,
                        presetInHandle = Just (BezierHandle 0.6 1.0),
                        presetOutHandle = Nothing
                      }
                  ]
              }
          ]
      },
    AnimationPreset
      { presetId = "fade-out",
        presetName = "Fade Out",
        presetCategory = "Fade",
        presetDescription = "Fade from opaque to transparent",
        presetKeyframes =
          [ KeyframeProperty
              { propProperty = "opacity",
                propKeyframes =
                  [ PresetKeyframe
                      { presetTime = 0.0,
                        presetValue = ParamNumber 100.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Just (BezierHandle 0.4 1.0)
                      },
                    PresetKeyframe
                      { presetTime = 1.0,
                        presetValue = ParamNumber 0.0,
                        presetInHandle = Just (BezierHandle 0.6 0.0),
                        presetOutHandle = Nothing
                      }
                  ]
              }
          ]
      },
    AnimationPreset
      { presetId = "scale-up",
        presetName = "Scale Up",
        presetCategory = "Scale",
        presetDescription = "Scale from small to full size",
        presetKeyframes =
          [ KeyframeProperty
              { propProperty = "scale",
                propKeyframes =
                  [ PresetKeyframe
                      { presetTime = 0.0,
                        presetValue = ParamPoint 0.0 0.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Just (BezierHandle 0.25 0.1)
                      },
                    PresetKeyframe
                      { presetTime = 1.0,
                        presetValue = ParamPoint 100.0 100.0,
                        presetInHandle = Just (BezierHandle 0.25 1.0),
                        presetOutHandle = Nothing
                      }
                  ]
              }
          ]
      },
    AnimationPreset
      { presetId = "bounce-in",
        presetName = "Bounce In",
        presetCategory = "Scale",
        presetDescription = "Scale up with bounce effect",
        presetKeyframes =
          [ KeyframeProperty
              { propProperty = "scale",
                propKeyframes =
                  [ PresetKeyframe
                      { presetTime = 0.0,
                        presetValue = ParamPoint 0.0 0.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Nothing
                      },
                    PresetKeyframe
                      { presetTime = 0.6,
                        presetValue = ParamPoint 110.0 110.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Nothing
                      },
                    PresetKeyframe
                      { presetTime = 0.8,
                        presetValue = ParamPoint 95.0 95.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Nothing
                      },
                    PresetKeyframe
                      { presetTime = 1.0,
                        presetValue = ParamPoint 100.0 100.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Nothing
                      }
                  ]
              }
          ]
      },
    AnimationPreset
      { presetId = "slide-left",
        presetName = "Slide Left",
        presetCategory = "Position",
        presetDescription = "Slide in from right",
        presetKeyframes =
          [ KeyframeProperty
              { propProperty = "position",
                propKeyframes =
                  [ PresetKeyframe
                      { presetTime = 0.0,
                        presetValue = ParamPoint 1.5 0.5,
                        presetInHandle = Nothing,
                        presetOutHandle = Just (BezierHandle 0.25 0.1)
                      },
                    PresetKeyframe
                      { presetTime = 1.0,
                        presetValue = ParamPoint 0.5 0.5,
                        presetInHandle = Just (BezierHandle 0.25 1.0),
                        presetOutHandle = Nothing
                      }
                  ]
              }
          ]
      },
    AnimationPreset
      { presetId = "rotate-in",
        presetName = "Rotate In",
        presetCategory = "Rotation",
        presetDescription = "Rotate from 0 to 360 degrees",
        presetKeyframes =
          [ KeyframeProperty
              { propProperty = "rotation",
                propKeyframes =
                  [ PresetKeyframe
                      { presetTime = 0.0,
                        presetValue = ParamNumber 0.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Nothing
                      },
                    PresetKeyframe
                      { presetTime = 1.0,
                        presetValue = ParamNumber 360.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Nothing
                      }
                  ]
              }
          ]
      },
    AnimationPreset
      { presetId = "typewriter",
        presetName = "Typewriter",
        presetCategory = "Text",
        presetDescription = "Reveal text character by character",
        presetKeyframes =
          [ KeyframeProperty
              { propProperty = "textReveal",
                propKeyframes =
                  [ PresetKeyframe
                      { presetTime = 0.0,
                        presetValue = ParamNumber 0.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Nothing
                      },
                    PresetKeyframe
                      { presetTime = 1.0,
                        presetValue = ParamNumber 100.0,
                        presetInHandle = Nothing,
                        presetOutHandle = Nothing
                      }
                  ]
              }
          ]
      }
  ]
