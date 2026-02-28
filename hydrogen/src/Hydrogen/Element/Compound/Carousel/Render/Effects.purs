-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // element // carousel // render // effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Effects — Slide effect computations based on position.
-- |
-- | ## Design Philosophy
-- |
-- | Effects are computed as CSS style arrays based on slide position
-- | relative to the active slide. Each effect type (opacity, scale, blur,
-- | etc.) has configurable active/inactive values with falloff for nearby
-- | slides.
-- |
-- | ## Effect Types
-- |
-- | - Opacity: fade inactive slides
-- | - Scale: shrink inactive slides  
-- | - Blur: blur inactive slides
-- | - Grayscale: desaturate inactive slides
-- | - Rotation: 3D rotation based on position offset
-- | - Glow: box-shadow on active slide
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Types (SlidePosition)
-- | - Carousel.Effects (SlideEffects)
-- | - Hydrogen.Schema.Dimension.Device

module Hydrogen.Element.Compound.Carousel.Render.Effects
  ( -- * Position Computation
    computeSlidePosition
  , computeSlidePositionFromIndex
  , positionToClass
  , positionOffset
  
  -- * Effect Styles
  , computeEffectStyles
  , computeTransformComponents
  , computeFilterComponents
  
  -- * Helpers
  , pow
  , interpolateEffect
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (==)
  , (+)
  , (-)
  , (*)
  , (>=)
  , (<=)
  , (<)
  , (&&)
  , not
  , negate
  , otherwise
  )

import Data.Array as Array
import Data.Int (toNumber)
import Data.Tuple (Tuple(Tuple))
import Data.String.Common (joinWith) as String

import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Color.RGB as Color

import Hydrogen.Element.Compound.Carousel.Types 
  ( SlideIndex
  , unwrapSlideIndex
  , SlidePosition
      ( PositionActive
      , PositionPrev
      , PositionNext
      , PositionNearby
      , PositionOffscreen
      )
  )
import Hydrogen.Element.Compound.Carousel.State (CarouselState)
import Hydrogen.Element.Compound.Carousel.Effects 
  ( SlideEffects
  , isEffectEnabled
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // position computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute slide position relative to active slide
computeSlidePosition :: CarouselState -> Int -> SlidePosition
computeSlidePosition state index =
  let 
    currentIdx = unwrapSlideIndex state.current
    diff = index - currentIdx
  in
    if diff == 0 then PositionActive
    else if diff == (-1) then PositionPrev
    else if diff == 1 then PositionNext
    else if diff >= (-3) && diff <= 3 then PositionNearby diff
    else PositionOffscreen

-- | Compute slide position using SlideIndex type
-- | Type-safe version that accepts SlideIndex instead of raw Int
computeSlidePositionFromIndex :: CarouselState -> SlideIndex -> SlidePosition
computeSlidePositionFromIndex state idx = computeSlidePosition state (unwrapSlideIndex idx)

-- | Convert position to CSS class
positionToClass :: SlidePosition -> String
positionToClass PositionActive = "carousel-slide-active"
positionToClass PositionPrev = "carousel-slide-prev"
positionToClass PositionNext = "carousel-slide-next"
positionToClass (PositionNearby n) = "carousel-slide-nearby carousel-slide-nearby-" <> show n
positionToClass PositionOffscreen = "carousel-slide-offscreen"

-- | Get the numeric offset from active position
-- | Returns 0 for active, negative for previous, positive for next
positionOffset :: SlidePosition -> Int
positionOffset PositionActive = 0
positionOffset PositionPrev = negate 1
positionOffset PositionNext = 1
positionOffset (PositionNearby n) = n
positionOffset PositionOffscreen = 100  -- Large value indicating far away

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // effect styles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute effect styles based on slide position
computeEffectStyles :: SlideEffects -> SlidePosition -> Array (Tuple String String)
computeEffectStyles effects position =
  let
    -- Opacity effect
    opacityStyle = if isEffectEnabled effects.opacity.enabled
      then case position of
        PositionActive -> [ Tuple "opacity" (show effects.opacity.active) ]
        PositionPrev -> [ Tuple "opacity" (show effects.opacity.inactive) ]
        PositionNext -> [ Tuple "opacity" (show effects.opacity.inactive) ]
        PositionNearby n -> 
          let falloff = effects.opacity.nearbyFalloff
              dist = if n < 0 then negate (toNumber n) else toNumber n
              opacity = effects.opacity.inactive * (falloff `pow` dist)
          in [ Tuple "opacity" (show opacity) ]
        PositionOffscreen -> [ Tuple "opacity" "0" ]
      else []
    
    -- Build transform components (scale + rotation combined)
    transformComponents = computeTransformComponents effects position
    transformStyle = if not (Array.null transformComponents)
      then [ Tuple "transform" (String.joinWith " " transformComponents) ]
      else []
    
    -- Add perspective if rotation is enabled
    perspectiveStyle = if isEffectEnabled effects.rotation.enabled
      then [ Tuple "perspective" (show (Device.unwrapPixel effects.rotation.perspective) <> "px") ]
      else []
    
    -- Build filter components (blur + grayscale combined into one property)
    filterComponents = computeFilterComponents effects position
    filterStyle = if not (Array.null filterComponents)
      then [ Tuple "filter" (String.joinWith " " filterComponents) ]
      else []
    
    -- Glow effect (box-shadow on active slide)
    glowStyle = if isEffectEnabled effects.glow.enabled && position == PositionActive
      then 
        let 
          colorRec = Color.rgbToRecord effects.glow.color
          radius = show (Device.unwrapPixel effects.glow.radius)
          spread = show (Device.unwrapPixel effects.glow.spread)
          opacity = show effects.glow.opacity
        in [ Tuple "box-shadow" ("0 0 " <> radius <> "px " <> spread <> "px rgba(" <> show colorRec.r <> "," <> show colorRec.g <> "," <> show colorRec.b <> "," <> opacity <> ")") ]
      else []
    
  in opacityStyle <> transformStyle <> perspectiveStyle <> filterStyle <> glowStyle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // transform components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute transform CSS components (scale, rotation)
computeTransformComponents :: SlideEffects -> SlidePosition -> Array String
computeTransformComponents effects position =
  let
    -- Scale component
    scaleComponent = if isEffectEnabled effects.scale.enabled
      then case position of
        PositionActive -> [ "scale(" <> show effects.scale.active <> ")" ]
        PositionPrev -> [ "scale(" <> show effects.scale.inactive <> ")" ]
        PositionNext -> [ "scale(" <> show effects.scale.inactive <> ")" ]
        PositionNearby n ->
          let falloff = effects.scale.nearbyFalloff
              dist = if n < 0 then negate (toNumber n) else toNumber n
              scale = effects.scale.inactive * (falloff `pow` dist)
          in [ "scale(" <> show scale <> ")" ]
        PositionOffscreen -> [ "scale(0.5)" ]
      else []
    
    -- Rotation component (3D transforms based on position offset)
    rotationComponent = if isEffectEnabled effects.rotation.enabled
      then case position of
        PositionActive -> []  -- No rotation on active
        PositionPrev -> 
          [ "rotateY(" <> show (negate effects.rotation.rotateY) <> "deg)"
          , "rotateX(" <> show effects.rotation.rotateX <> "deg)"
          , "rotateZ(" <> show effects.rotation.rotateZ <> "deg)"
          ]
        PositionNext ->
          [ "rotateY(" <> show effects.rotation.rotateY <> "deg)"
          , "rotateX(" <> show effects.rotation.rotateX <> "deg)"
          , "rotateZ(" <> show (negate effects.rotation.rotateZ) <> "deg)"
          ]
        PositionNearby n ->
          let multiplier = toNumber n
          in [ "rotateY(" <> show (effects.rotation.rotateY * multiplier) <> "deg)"
             , "rotateX(" <> show (effects.rotation.rotateX * multiplier) <> "deg)"
             , "rotateZ(" <> show (effects.rotation.rotateZ * multiplier) <> "deg)"
             ]
        PositionOffscreen -> []
      else []
    
  in scaleComponent <> rotationComponent

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // filter components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute filter CSS components (blur, grayscale)
computeFilterComponents :: SlideEffects -> SlidePosition -> Array String
computeFilterComponents effects position =
  let
    -- Blur component
    blurComponent = if isEffectEnabled effects.blur.enabled
      then case position of
        PositionActive -> [ "blur(" <> show (Device.unwrapPixel effects.blur.active) <> "px)" ]
        _ -> [ "blur(" <> show (Device.unwrapPixel effects.blur.inactive) <> "px)" ]
      else []
    
    -- Grayscale component
    grayscaleComponent = if isEffectEnabled effects.grayscale.enabled
      then case position of
        PositionActive -> [ "grayscale(" <> show (effects.grayscale.active * 100.0) <> "%)" ]
        _ -> [ "grayscale(" <> show (effects.grayscale.inactive * 100.0) <> "%)" ]
      else []
    
  in blurComponent <> grayscaleComponent

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Simple power function for falloff calculations
pow :: Number -> Number -> Number
pow base exp = powImpl base exp 1.0
  where
    powImpl :: Number -> Number -> Number -> Number
    powImpl b e acc
      | e <= 0.0 = acc
      | otherwise = powImpl b (e - 1.0) (acc * b)

-- | Interpolate between two effect values based on position
-- | Useful for smooth transitions between active/inactive states
-- | t is progress (0.0 = from, 1.0 = to)
interpolateEffect :: Number -> Number -> Number -> Number
interpolateEffect from to t =
  let 
    -- Clamp t to [0, 1]
    clampedT = if t < 0.0 then 0.0 else if t >= 1.0 then 1.0 else t
    -- Linear interpolation: from + (to - from) * t
    delta = to - from
  in from + delta * clampedT
