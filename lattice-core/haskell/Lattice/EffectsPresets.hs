{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.EffectsPresets
Description : Animation presets and templates
Copyright   : (c) Lattice, 2026
License     : MIT

Source: lattice-core/lean/Lattice/Effects/Presets.lean
-}

module Lattice.EffectsPresets
  ( -- * Preset Category
    PresetCategory(..)
    -- * Preset Types
  , PresetBezierHandle(..)
  , PresetKeyframe(..)
  , PresetPropertyAnimation(..)
  , AnimationPreset(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives
import Lattice.Effects (EffectParameterValue)

-- ────────────────────────────────────────────────────────────────────────────
-- Preset Category
-- ────────────────────────────────────────────────────────────────────────────

data PresetCategory
  = PCFade | PCScale | PCPosition | PCRotation | PCText | PCCustom
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Preset Types
-- ────────────────────────────────────────────────────────────────────────────

data PresetBezierHandle = PresetBezierHandle
  { pbhX :: !UnitFloat  -- 0-1
  , pbhY :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

data PresetKeyframe = PresetKeyframe
  { pkTime      :: !UnitFloat  -- 0-1 normalized time
  , pkValue     :: !EffectParameterValue
  , pkInHandle  :: !(Maybe PresetBezierHandle)
  , pkOutHandle :: !(Maybe PresetBezierHandle)
  } deriving stock (Eq, Show, Generic)

data PresetPropertyAnimation = PresetPropertyAnimation
  { ppaProperty  :: !NonEmptyString
  , ppaKeyframes :: !(Vector PresetKeyframe)  -- min 2
  } deriving stock (Eq, Show, Generic)

data AnimationPreset = AnimationPreset
  { apId          :: !NonEmptyString
  , apName        :: !NonEmptyString
  , apCategory    :: !PresetCategory
  , apDescription :: !Text
  , apKeyframes   :: !(Vector PresetPropertyAnimation)
  } deriving stock (Eq, Show, Generic)
