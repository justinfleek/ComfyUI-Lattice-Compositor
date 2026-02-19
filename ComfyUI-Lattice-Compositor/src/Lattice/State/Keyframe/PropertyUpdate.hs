-- |
-- Module      : Lattice.State.Keyframe.PropertyUpdate
-- Description : Helper functions for updating keyframes in layer properties
--
-- Internal module for keyframe operations
-- Provides functions to update keyframes in specific properties in Layer structure
-- NOTE: This module works with typed properties (Position2DOr3D, Vec3, Double)
-- For operations that need PropertyValue, conversion happens at call site
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.PropertyUpdate
  ( updateKeyframesInProperty
  , setPropertyAnimated
  ) where

import Data.List (findIndex, sortBy)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , Keyframe(..)
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Transform (LayerTransform(..))

-- | Update keyframes in a property
-- Pure function: takes property and keyframe update function
-- Returns updated property
updateKeyframesInProperty ::
  AnimatableProperty a ->
  ([Keyframe a] -> [Keyframe a]) ->
  AnimatableProperty a
updateKeyframesInProperty prop updateKeyframes =
  let
    currentKeyframes = animatablePropertyKeyframes prop
    newKeyframes = updateKeyframes currentKeyframes
    sortedKeyframes = sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) newKeyframes
  in
    prop
      { animatablePropertyKeyframes = sortedKeyframes
      , animatablePropertyAnimated = not (null sortedKeyframes)
      }

-- | Set property animated state
-- Pure function: takes property and animated flag
-- Returns updated property
setPropertyAnimated ::
  AnimatableProperty a ->
  Bool ->
  AnimatableProperty a
setPropertyAnimated prop animated =
  prop {animatablePropertyAnimated = animated}
