-- |
-- Module      : Lattice.State.Keyframe.Helpers
-- Description : Helper functions for keyframe operations
--
-- Migrated from ui/src/stores/keyframeStore/helpers.ts
-- Pure utility functions for frame validation and property lookup
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.Helpers
  ( safeFrame
  , findPropertyByPath
  -- Type conversion functions
  , positionToPropertyValue
  , vec3ToPropertyValue
  , doubleToPropertyValue
  ) where

import Data.Aeson (Value)
import Data.List (find)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , Keyframe(..)
  , PropertyValue(..)
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives
  ( Position2DOr3D(..)
  , Vec2(..)
  , Vec3(..)
  , validateFinite
  )
import Lattice.Types.Transform (LayerTransform(..))

-- ============================================================================
-- FRAME VALIDATION
-- ============================================================================

-- | Validate and sanitize frame number, returning fallback if invalid
-- Pure function: takes frame and fallback, returns valid frame
-- Guards against NaN, undefined, null, and Infinity
-- Ensures frame is >= 1
-- Frames start at 1, not 0
-- Default: 1.0 if both frame and fallback are invalid
safeFrame ::
  Maybe Double -> -- Frame number (may be invalid)
  Double -> -- Fallback value
  Double -- Valid frame number (always finite and >= 1)
safeFrame mFrame fallback =
  let
    -- Validate and clampD to minimum frame (>= 1)
    validateAndClamp x = if validateFinite x && x >= 1 then x else 1.0
  in
    case mFrame of
      Nothing -> validateAndClamp fallback
      Just frame -> validateAndClamp frame

-- ============================================================================
-- TYPE CONVERSIONS
-- ============================================================================

-- | Convert Position2DOr3D to PropertyValue
positionToPropertyValue :: Position2DOr3D -> PropertyValue
positionToPropertyValue pos =
  PropertyValuePosition2DOr3D
    (Vec2 (position2DOr3DX pos) (position2DOr3DY pos))
    (position2DOr3DZ pos)

-- | Convert Vec3 to PropertyValue
vec3ToPropertyValue :: Vec3 -> PropertyValue
vec3ToPropertyValue (Vec3 x y z) = PropertyValueVec3 (Vec3 x y z)

-- | Convert Double to PropertyValue
doubleToPropertyValue :: Double -> PropertyValue
doubleToPropertyValue d = PropertyValueNumber d

-- | Convert AnimatableProperty with specific type to AnimatableProperty PropertyValue
convertPropertyToPropertyValue ::
  AnimatableProperty a ->
  (a -> PropertyValue) ->
  AnimatableProperty PropertyValue
convertPropertyToPropertyValue prop convertValue =
  AnimatableProperty
    { animatablePropertyId = animatablePropertyId prop
    , animatablePropertyName = animatablePropertyName prop
    , animatablePropertyType = animatablePropertyType prop
    , animatablePropertyValue = convertValue (animatablePropertyValue prop)
    , animatablePropertyAnimated = animatablePropertyAnimated prop
    , animatablePropertyKeyframes = map (\kf -> kf {keyframeValue = convertValue (keyframeValue kf)}) (animatablePropertyKeyframes prop)
    , animatablePropertyGroup = animatablePropertyGroup prop
    , animatablePropertyExpression = animatablePropertyExpression prop
    }

-- ============================================================================
-- PROPERTY LOOKUP
-- ============================================================================

-- | Find a property by its path on a layer
-- Pure function: takes layer and property path, returns property or Nothing
-- Supports both 'position' and 'transform.position' formats
-- Returns AnimatableProperty PropertyValue for compatibility
findPropertyByPath ::
  Layer -> -- The layer to search
  Text -> -- Path to the property (e.g., 'position', 'transform.position', 'opacity')
  Maybe (AnimatableProperty PropertyValue) -- The animatable property or Nothing if not found
findPropertyByPath layer propertyPath =
  let
    -- Normalize path - strip 'transform.' prefix if present
    normalizedPath = T.replace "transform." "" propertyPath
    transform = layerTransform layer
  in
    -- Check transform properties
    if normalizedPath == "position"
      then Just (convertPropertyToPropertyValue (transformPosition transform) positionToPropertyValue)
      else if normalizedPath == "scale"
        then Just (convertPropertyToPropertyValue (transformScale transform) vec3ToPropertyValue)
        else if normalizedPath == "rotation"
          then Just (convertPropertyToPropertyValue (transformRotation transform) doubleToPropertyValue)
          else if normalizedPath == "anchorPoint"
            then fmap (\prop -> convertPropertyToPropertyValue prop positionToPropertyValue) (transformAnchorPoint transform)
            else if normalizedPath == "origin"
              then Just (convertPropertyToPropertyValue (transformOrigin transform) positionToPropertyValue)
              else if propertyPath == "opacity"
                then Just (convertPropertyToPropertyValue (layerOpacity layer) doubleToPropertyValue)
                else if normalizedPath == "rotationX"
                  then fmap (\prop -> convertPropertyToPropertyValue prop doubleToPropertyValue) (transformRotationX transform)
                  else if normalizedPath == "rotationY"
                    then fmap (\prop -> convertPropertyToPropertyValue prop doubleToPropertyValue) (transformRotationY transform)
                    else if normalizedPath == "rotationZ"
                      then fmap (\prop -> convertPropertyToPropertyValue prop doubleToPropertyValue) (transformRotationZ transform)
                      else if normalizedPath == "orientation"
                        then fmap (\prop -> convertPropertyToPropertyValue prop vec3ToPropertyValue) (transformOrientation transform)
                        else
                          -- Check custom properties by name or id
                          find (\p -> animatablePropertyName p == normalizedPath || animatablePropertyId p == normalizedPath) (layerProperties layer)
