-- | Lattice.EffectsPresets - Animation presets and templates
-- |
-- | Source: leancomfy/lean/Lattice/Effects/Presets.lean

module Lattice.EffectsPresets
  ( PresetCategory(..)
  , PresetBezierHandle
  , PresetKeyframe
  , PresetPropertyAnimation
  , AnimationPreset
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives
import Lattice.Effects (EffectParameterValue)

--------------------------------------------------------------------------------
-- Preset Category
--------------------------------------------------------------------------------

data PresetCategory
  = PCFade | PCScale | PCPosition | PCRotation | PCText | PCCustom

derive instance Eq PresetCategory
derive instance Generic PresetCategory _
instance Show PresetCategory where show = genericShow

--------------------------------------------------------------------------------
-- Preset Types
--------------------------------------------------------------------------------

type PresetBezierHandle =
  { x :: UnitFloat  -- 0-1
  , y :: FiniteFloat
  }

type PresetKeyframe =
  { time      :: UnitFloat  -- 0-1 normalized time
  , value     :: EffectParameterValue
  , inHandle  :: Maybe PresetBezierHandle
  , outHandle :: Maybe PresetBezierHandle
  }

type PresetPropertyAnimation =
  { property  :: NonEmptyString
  , keyframes :: Array PresetKeyframe  -- min 2
  }

type AnimationPreset =
  { id          :: NonEmptyString
  , name        :: NonEmptyString
  , category    :: PresetCategory
  , description :: String
  , keyframes   :: Array PresetPropertyAnimation
  }
