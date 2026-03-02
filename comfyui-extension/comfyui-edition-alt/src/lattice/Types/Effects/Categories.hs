{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Categories
  ( EffectCategoryInfo (..),
    effectCategories,
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import GHC.Generics (Generic)
import Lattice.Types.Effects.Core (EffectCategory (..))

-- | Effect category metadata (label, icon, description)
data EffectCategoryInfo = EffectCategoryInfo
  { catLabel :: String,
    catIcon :: String,
    catDescription :: String
  }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Effect categories with icons and descriptions
-- Migrated from ui/src/types/effects.ts EFFECT_CATEGORIES constant
effectCategories :: HashMap EffectCategory EffectCategoryInfo
effectCategories =
  HM.fromList
    [ ( BlurSharpen,
        EffectCategoryInfo
          { catLabel = "Blur & Sharpen",
            catIcon = "B",
            catDescription = "Blur and sharpen effects"
          }
      ),
      ( ColorCorrection,
        EffectCategoryInfo
          { catLabel = "Color Correction",
            catIcon = "C",
            catDescription = "Color adjustment effects"
          }
      ),
      ( Distort,
        EffectCategoryInfo
          { catLabel = "Distort",
            catIcon = "D",
            catDescription = "Distortion effects"
          }
      ),
      ( Generate,
        EffectCategoryInfo
          { catLabel = "Generate",
            catIcon = "G",
            catDescription = "Generate patterns and fills"
          }
      ),
      ( Keying,
        EffectCategoryInfo
          { catLabel = "Keying",
            catIcon = "K",
            catDescription = "Chromakey and luma key"
          }
      ),
      ( Matte,
        EffectCategoryInfo
          { catLabel = "Matte",
            catIcon = "M",
            catDescription = "Matte manipulation"
          }
      ),
      ( NoiseGrain,
        EffectCategoryInfo
          { catLabel = "Noise & Grain",
            catIcon = "N",
            catDescription = "Add or remove noise"
          }
      ),
      ( Perspective,
        EffectCategoryInfo
          { catLabel = "Perspective",
            catIcon = "P",
            catDescription = "3D perspective effects"
          }
      ),
      ( Stylize,
        EffectCategoryInfo
          { catLabel = "Stylize",
            catIcon = "S",
            catDescription = "Stylization effects"
          }
      ),
      ( Time,
        EffectCategoryInfo
          { catLabel = "Time",
            catIcon = "T",
            catDescription = "Time-based effects"
          }
      ),
      ( Transition,
        EffectCategoryInfo
          { catLabel = "Transition",
            catIcon = "Tr",
            catDescription = "Transition effects"
          }
      ),
      ( Utility,
        EffectCategoryInfo
          { catLabel = "Utility",
            catIcon = "U",
            catDescription = "Utility effects"
          }
      )
    ]
