-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // carousel // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Render — Pure render function for carousel state.
-- |
-- | ## Design Philosophy
-- |
-- | The render function is pure: State -> Element.
-- | It composes all the carousel sub-modules to produce the final UI.
-- | No side effects, no DOM manipulation — just Element construction.
-- |
-- | ## Render Structure
-- |
-- | ```
-- | .carousel-container
-- |   .carousel-track
-- |     .carousel-slide[n]
-- |   .carousel-nav-arrows
-- |   .carousel-nav-dots
-- |   .carousel-nav-progress
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Carousel.State (CarouselState)
-- | - Carousel.Slide (SlideCollection, SlideData)
-- | - Carousel.Navigation (NavigationConfig)
-- | - Carousel.Effects (SlideEffects)
-- | - Hydrogen.Render.Element (Element constructors)

module Hydrogen.Element.Compound.Carousel.Render
  ( -- * Render Function
    carousel
  , carouselWithCaptions
  
  -- * Carousel Config
  , CarouselConfig
  , defaultConfig
  
  -- * Messages (re-exported from Types)
  , module CarouselMsgExport
  
  -- * State Accessors
  , getTransitionState
  , getGestureState
  
  -- * Validation
  , isValidSlideIndex
  , clampSlideIndex
  
  -- * Slide Visibility
  , isSlideVisible
  , visibleSlideIndices
  
  -- * Color Effects
  , slidePositionTint
  
  -- * Position Calculations
  , wavePosition
  , circularPosition
  , easeOutPosition
  , positionDistance
  , defaultCase
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , map
  , (<>)
  , (==)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
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
import Data.Maybe (Maybe(Nothing, Just))




import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Temporal as Temporal
import Hydrogen.Schema.Color.RGB as Color
import Data.String.Common (joinWith) as String
import Hydrogen.Element.Compound.Carousel.Types 
  ( slideIndex
  , unwrapSlideIndex
  , SlidePosition
      ( PositionActive
      , PositionPrev
      , PositionNext
      , PositionNearby
      , PositionOffscreen
      )
  , TransitionKind
      ( TransitionNone
      , TransitionSlide
      , TransitionSlideVertical
      , TransitionFade
      , TransitionZoom
      , TransitionFlip
      , TransitionFlipVertical
      , TransitionCube
      , TransitionCoverflow
      , TransitionCards
      , TransitionWheel
      , TransitionSpiral
      , TransitionParallax
      , TransitionMorph
      , TransitionDissolve
      , TransitionBlur
      , TransitionWipe
      , TransitionReveal
      )
  , LayoutPath
      ( PathLinear
      , PathLinearVertical
      , PathGrid
      , PathMasonry
      , PathStack
      , PathCircular
      , PathArc
      , PathHelix
      , PathSphere
      , PathCylinder
      , PathMobius
      , PathCustom
      )
  , CarouselMsg
  )
import Hydrogen.Element.Compound.Carousel.Types 
  ( CarouselMsg
      ( GoToSlide
      , NextSlide
      , PrevSlide
      , StartAutoplay
      , StopAutoplay
      , ToggleAutoplay
      )
  ) as CarouselMsgExport
import Hydrogen.Element.Compound.Carousel.State 
  ( CarouselState
  , TransitionState
  , isTransitioning
  , transitionProgress
  )
import Hydrogen.Element.Compound.Carousel.Slide 
  ( SlideCollection
  , SlideData
  , slideAt
  , slideCount
  )
import Hydrogen.Element.Compound.Carousel.Navigation 
  ( NavigationConfig
  , defaultNavigation
  )
import Hydrogen.Element.Compound.Carousel.Render.Navigation 
  ( renderNavigation
  )
import Hydrogen.Element.Compound.Carousel.Render.Layout
  ( computeLayoutTransform
  , sin
  , cos
  , abs
  , absInt
  , toInt
  )
import Hydrogen.Element.Compound.Carousel.Render.Content
  ( renderSlideContent
  , renderCaption
  )
import Hydrogen.Element.Compound.Carousel.Render.Effects
  ( computeSlidePosition
  , positionToClass
  , computeEffectStyles
  , pow
  )
import Hydrogen.Element.Compound.Carousel.Effects 
  ( SlideEffects
  , defaultEffects
  , isEffectEnabled
  , ParallaxDirection
      ( ParallaxHorizontal
      , ParallaxVertical
      , ParallaxBoth
      )
  )
import Hydrogen.Element.Compound.Carousel.Transitions 
  ( TransitionConfig
  , defaultTransition
  , easingToCss
  )
import Hydrogen.Element.Compound.Carousel.Gestures (GestureState, isDragActive, dragOffset)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // carousel config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete carousel configuration
type CarouselConfig =
  { navigation :: NavigationConfig
  , transition :: TransitionConfig
  , effects :: SlideEffects
  , layoutPath :: LayoutPath      -- spatial arrangement of slides
  , loop :: Boolean
  , autoplayInterval :: Int      -- milliseconds, 0 = no autoplay
  , cssClass :: String           -- additional CSS class
  }

-- | Default carousel configuration
defaultConfig :: CarouselConfig
defaultConfig =
  { navigation: defaultNavigation
  , transition: defaultTransition
  , effects: defaultEffects
  , layoutPath: PathLinear
  , loop: true
  , autoplayInterval: 0
  , cssClass: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // render functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a carousel from state and configuration
-- |
-- | This is the main entry point for carousel rendering.
carousel :: CarouselConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
carousel config state slides' =
  E.div_
    [ E.class_ ("carousel-container" <> additionalClass) ]
    [ renderTrack config state slides'
    , renderNavigation config.navigation config.loop state slides'
    ]
  where
    additionalClass = if config.cssClass == "" then "" else " " <> config.cssClass

-- | Render the slide track with transition and gesture transforms
renderTrack :: CarouselConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
renderTrack config state slides' =
  let 
    -- Transition type class for CSS styling hooks
    transitionClass = transitionKindToClass config.transition.kind
  in
    E.div_
      ([ E.class_ ("carousel-track " <> transitionClass) ] <> E.styles (trackStyles config state))
      (renderSlides config state slides')

-- | Convert transition kind to CSS class for transition-specific styling
transitionKindToClass :: TransitionKind -> String
transitionKindToClass kind = case kind of
  TransitionNone -> "carousel-transition-none"
  TransitionSlide -> "carousel-transition-slide"
  TransitionSlideVertical -> "carousel-transition-slide-vertical"
  TransitionFade -> "carousel-transition-fade"
  TransitionZoom -> "carousel-transition-zoom"
  TransitionFlip -> "carousel-transition-flip"
  TransitionFlipVertical -> "carousel-transition-flip-vertical"
  TransitionCube -> "carousel-transition-cube"
  TransitionCoverflow -> "carousel-transition-coverflow"
  TransitionCards -> "carousel-transition-cards"
  TransitionWheel -> "carousel-transition-wheel"
  TransitionSpiral -> "carousel-transition-spiral"
  TransitionParallax -> "carousel-transition-parallax"
  TransitionMorph -> "carousel-transition-morph"
  TransitionDissolve -> "carousel-transition-dissolve"
  TransitionBlur -> "carousel-transition-blur"
  TransitionWipe -> "carousel-transition-wipe"
  TransitionReveal -> "carousel-transition-reveal"

-- | Compute track styles based on state and layout path
trackStyles :: CarouselConfig -> CarouselState -> Array (Tuple String String)
trackStyles config state =
  case config.layoutPath of
    -- Linear layouts use translate on the track
    PathLinear -> linearTrackStyles config state
    PathLinearVertical -> linearVerticalTrackStyles config state
    -- 3D layouts use perspective on the track, slides positioned individually
    PathCircular -> layout3DContainerStyles config
    PathHelix -> layout3DContainerStyles config
    PathSphere -> layout3DContainerStyles config
    PathCylinder -> layout3DContainerStyles config
    PathMobius -> layout3DContainerStyles config
    -- Other layouts
    PathGrid -> gridContainerStyles
    PathMasonry -> masonryContainerStyles
    PathStack -> stackContainerStyles config state
    PathArc -> layout3DContainerStyles config
    PathCustom -> linearTrackStyles config state  -- Fallback to linear

-- | Linear horizontal track styles (traditional carousel)
linearTrackStyles :: CarouselConfig -> CarouselState -> Array (Tuple String String)
linearTrackStyles config state =
  let 
    currentIdx = unwrapSlideIndex state.current
    baseOffset = toNumber currentIdx * (-100.0)
    gestureOffset = if isDragActive state.gesture.drag
      then (dragOffset state.gesture.drag).x / 10.0
      else 0.0
    transitionOffset = if isTransitioning state.transition
      then 
        let 
          fromIdx = unwrapSlideIndex state.transition.fromIndex
          toIdx = unwrapSlideIndex state.transition.toIndex
          progress = transitionProgress state.transition
          fromOffset = toNumber fromIdx * (-100.0)
          toOffset = toNumber toIdx * (-100.0)
        in fromOffset + (toOffset - fromOffset) * progress
      else baseOffset
    finalOffset = if isTransitioning state.transition 
      then transitionOffset 
      else baseOffset + gestureOffset
    transitionCss = if isTransitioning state.transition
      then "transform " <> show (Device.unwrapPixel (toPixel config.transition.duration)) <> "ms " <> easingToCss config.transition.easing
      else "none"
  in
    [ Tuple "transform" ("translateX(" <> show finalOffset <> "%)")
    , Tuple "transition" transitionCss
    , Tuple "display" "flex"
    ]

-- | Linear vertical track styles
linearVerticalTrackStyles :: CarouselConfig -> CarouselState -> Array (Tuple String String)
linearVerticalTrackStyles config state =
  let 
    currentIdx = unwrapSlideIndex state.current
    baseOffset = toNumber currentIdx * (-100.0)
    gestureOffset = if isDragActive state.gesture.drag
      then (dragOffset state.gesture.drag).y / 10.0
      else 0.0
    finalOffset = baseOffset + gestureOffset
    transitionCss = if isTransitioning state.transition
      then "transform " <> show (Device.unwrapPixel (toPixel config.transition.duration)) <> "ms " <> easingToCss config.transition.easing
      else "none"
  in
    [ Tuple "transform" ("translateY(" <> show finalOffset <> "%)")
    , Tuple "transition" transitionCss
    , Tuple "display" "flex"
    , Tuple "flex-direction" "column"
    ]

-- | 3D container styles (for circular, helix, sphere, etc.)
layout3DContainerStyles :: CarouselConfig -> Array (Tuple String String)
layout3DContainerStyles _config =
  [ Tuple "perspective" "1000px"
  , Tuple "perspective-origin" "50% 50%"
  , Tuple "transform-style" "preserve-3d"
  , Tuple "position" "relative"
  ]

-- | Grid container styles
gridContainerStyles :: Array (Tuple String String)
gridContainerStyles =
  [ Tuple "display" "grid"
  , Tuple "grid-template-columns" "repeat(auto-fill, minmax(200px, 1fr))"
  , Tuple "gap" "16px"
  ]

-- | Masonry container styles
masonryContainerStyles :: Array (Tuple String String)
masonryContainerStyles =
  [ Tuple "columns" "3"
  , Tuple "column-gap" "16px"
  ]

-- | Stack container styles (cards stacked on top of each other)
stackContainerStyles :: CarouselConfig -> CarouselState -> Array (Tuple String String)
stackContainerStyles _config _state =
  [ Tuple "position" "relative"
  , Tuple "perspective" "1000px"
  ]

-- Note: computeLayoutTransform, circularTransform, helixTransform, etc.
-- have been moved to Render/Layout.purs and are imported above.

-- | Convert milliseconds to pixel (for duration display)
toPixel :: Temporal.Milliseconds -> Device.Pixel
toPixel ms = Device.px (Temporal.unwrapMilliseconds ms)

-- | Render all slides with position-aware effects
renderSlides :: CarouselConfig -> CarouselState -> SlideCollection -> Array (E.Element CarouselMsg)
renderSlides config state slides' =
  Array.mapWithIndex (\i _ -> renderSlide config state i slides') (Array.range 0 (slideCount slides' - 1))

-- | Render a single slide with effects based on position
renderSlide :: CarouselConfig -> CarouselState -> Int -> SlideCollection -> E.Element CarouselMsg
renderSlide config state index slides' =
  case slideAt (slideIndex index) slides' of
    Just slideData' ->
      let 
        position = computeSlidePosition state index
        currentIdx = unwrapSlideIndex state.current
        total = slideCount slides'
        -- Visual effects based on position (opacity, scale, blur, etc.)
        effectStyles = computeEffectStyles config.effects position
        -- 3D layout transform based on layout path (circular, helix, sphere, etc.)
        layoutStyles = computeLayoutTransform config.layoutPath index currentIdx total
        -- Combine all styles
        allStyles = effectStyles <> layoutStyles
        positionClass = positionToClass position
        baseAttrs = 
          [ E.class_ ("carousel-slide " <> positionClass)
          , E.dataAttr "slide-index" (show index)
          , E.ariaHidden (position == PositionOffscreen)
          ]
        -- Base content (may be wrapped in parallax layers)
        baseContent = renderSlideContent slideData'
        -- Apply parallax wrapper if enabled
        parallaxContent = renderParallaxLayers config.effects position baseContent
        -- Reflection element (rendered below slide content)
        reflectionEl = renderReflection config.effects slideData'
      in
        E.div_
          (baseAttrs <> E.styles allStyles)
          [ parallaxContent
          , reflectionEl
          ]
    Nothing ->
      E.empty

-- | Render reflection effect (mirrored content below slide)
renderReflection :: SlideEffects -> SlideData -> E.Element CarouselMsg
renderReflection effects slideData' =
  if isEffectEnabled effects.reflection.enabled
    then 
      let
        heightPercent = show (effects.reflection.height * 100.0) <> "%"
        startOpacity = show effects.reflection.opacity
        gapPx = show (Device.unwrapPixel effects.reflection.gap) <> "px"
        -- Reflection uses CSS transform: scaleY(-1) to flip vertically
        -- and a gradient mask to fade out
        reflectionStyles = 
          [ Tuple "height" heightPercent
          , Tuple "margin-top" gapPx
          , Tuple "transform" "scaleY(-1)"
          , Tuple "opacity" startOpacity
          , Tuple "mask-image" "linear-gradient(to bottom, rgba(0,0,0,1) 0%, rgba(0,0,0,0) 100%)"
          , Tuple "-webkit-mask-image" "linear-gradient(to bottom, rgba(0,0,0,1) 0%, rgba(0,0,0,0) 100%)"
          , Tuple "pointer-events" "none"
          , Tuple "overflow" "hidden"
          ]
      in
        E.div_
          ([ E.class_ "carousel-slide-reflection"
           , E.ariaHidden true
           ] <> E.styles reflectionStyles)
          [ renderSlideContent slideData' ]
    else
      E.empty

-- Note: renderSlideContent is imported from Render/Content.purs

-- | Render parallax layers wrapper
-- | Each layer moves at a different speed based on its depth
renderParallaxLayers :: SlideEffects -> SlidePosition -> E.Element CarouselMsg -> E.Element CarouselMsg
renderParallaxLayers effects position content =
  if isEffectEnabled effects.parallax.enabled
    then
      let 
        numLayers = effects.parallax.layers
        speedRatio = effects.parallax.speedRatio
        direction = effects.parallax.direction
      in
        E.div_
          [ E.class_ "carousel-parallax-container" ]
          (map (renderParallaxLayer speedRatio direction position content) (Array.range 0 (numLayers - 1)))
    else
      content

-- | Render a single parallax layer with depth-based transform
renderParallaxLayer :: Number -> ParallaxDirection -> SlidePosition -> E.Element CarouselMsg -> Int -> E.Element CarouselMsg
renderParallaxLayer speedRatio direction position content layerIndex =
  let
    -- Calculate speed multiplier for this layer (deeper layers move slower)
    layerDepth = toNumber layerIndex
    speedMultiplier = 1.0 - (layerDepth * speedRatio)
    
    -- Calculate offset based on position and layer depth
    positionOffset = case position of
      PositionActive -> 0.0
      PositionPrev -> negate 20.0 * speedMultiplier
      PositionNext -> 20.0 * speedMultiplier
      PositionNearby n -> toNumber n * 10.0 * speedMultiplier
      PositionOffscreen -> 0.0
    
    -- Build transform based on direction
    transformValue = case direction of
      ParallaxHorizontal -> "translateX(" <> show positionOffset <> "px)"
      ParallaxVertical -> "translateY(" <> show positionOffset <> "px)"
      ParallaxBoth -> "translate(" <> show positionOffset <> "px, " <> show (positionOffset * 0.5) <> "px)"
    
    -- Z-index for layering (deeper = lower z-index)
    zIndex = show (10 - layerIndex)
    
    layerStyles = 
      [ Tuple "transform" transformValue
      , Tuple "z-index" zIndex
      , Tuple "transition" "transform 0.3s ease-out"
      ]
  in
    E.div_
      ([ E.class_ ("carousel-parallax-layer carousel-parallax-layer-" <> show layerIndex) 
       ] <> E.styles layerStyles)
      [ if layerIndex == 0 then content else E.empty ]  -- Only first layer has content

-- | Get the current transition state from carousel state
-- | Useful for tracking animation progress
getTransitionState :: CarouselState -> TransitionState
getTransitionState state = state.transition

-- | Get the current gesture state from carousel state
-- | Useful for responding to user input
getGestureState :: CarouselState -> GestureState
getGestureState state = state.gesture

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a slide index is valid for the given collection
isValidSlideIndex :: Int -> SlideCollection -> Boolean
isValidSlideIndex idx slides' =
  idx >= 0 && idx < slideCount slides'

-- | Clamp a slide index to valid bounds
-- | If loop is enabled, wraps around; otherwise clamps to [0, count-1]
clampSlideIndex :: Boolean -> Int -> SlideCollection -> Int
clampSlideIndex loop idx slides' =
  let count = slideCount slides'
  in if count <= 0 then 0
     else if loop then modulo idx count
     else if idx < 0 then 0
     else if idx >= count then count - 1
     else idx
  where
    -- Positive modulo for wrapping
    modulo :: Int -> Int -> Int
    modulo a b = 
      let r = a - (a / b) * b
      in if r < 0 then r + b else r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // slide visibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a slide should be visible (rendered) based on current position
-- | Slides outside the visibility threshold are not rendered for performance
isSlideVisible :: CarouselConfig -> CarouselState -> Int -> SlideCollection -> Boolean
isSlideVisible config state idx slides' =
  let 
    currentIdx = unwrapSlideIndex state.current
    total = slideCount slides'
    threshold = visibilityThreshold config
    distance = slideDistance config.loop currentIdx idx total
  in
    isValidSlideIndex idx slides' && distance <= threshold

-- | Get indices of all currently visible slides
visibleSlideIndices :: CarouselConfig -> CarouselState -> SlideCollection -> Array Int
visibleSlideIndices config state slides' =
  Array.filter (\idx -> isSlideVisible config state idx slides') 
    (Array.range 0 (slideCount slides' - 1))

-- | Calculate distance between two slide indices (accounting for loop)
slideDistance :: Boolean -> Int -> Int -> Int -> Int
slideDistance loop fromIdx toIdx total =
  if not loop then
    absInt (toIdx - fromIdx)
  else
    let direct = absInt (toIdx - fromIdx)
        wrapped = total - direct
    in if direct <= wrapped then direct else wrapped

-- | How many slides on each side of current to render
visibilityThreshold :: CarouselConfig -> Int
visibilityThreshold config = case config.layoutPath of
  PathLinear -> 2
  PathLinearVertical -> 2
  PathGrid -> slideCount' -- All visible in grid
  PathMasonry -> slideCount' -- All visible
  PathStack -> 5
  PathCircular -> 4
  PathArc -> 3
  PathHelix -> 6
  PathSphere -> 8
  PathCylinder -> 5
  PathMobius -> 6
  PathCustom -> 3
  where
    -- Placeholder for when we need all slides
    slideCount' = 100

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate a color tint based on slide position
-- | Returns an RGB color representing the intensity at this position
-- | Can be used for overlay effects or color grading based on distance from active
slidePositionTint :: SlideEffects -> SlidePosition -> Color.RGB
slidePositionTint effects position =
  let
    -- Base intensity based on distance from active
    intensity = case position of
      PositionActive -> 1.0
      PositionPrev -> 0.8
      PositionNext -> 0.8
      PositionNearby n -> 
        let dist = toNumber (absInt n)
        in 1.0 - (dist * 0.1)
      PositionOffscreen -> 0.5
    
    -- Apply grayscale effect if enabled (reduces saturation based on distance)
    grayscaleAmount = if isEffectEnabled effects.grayscale.enabled
      then effects.grayscale.inactive
      else 0.0
    
    -- Compute channel values (intensity-based white)
    -- When grayscale is applied, slides fade toward gray
    baseChannel = toInt (intensity * 255.0)
    grayOffset = toInt (grayscaleAmount * (1.0 - intensity) * 50.0)
    channelValue = baseChannel - grayOffset
    clampedChannel = if channelValue < 0 then 0 
                     else if channelValue > 255 then 255 
                     else channelValue
  in
    Color.rgb clampedChannel clampedChannel clampedChannel

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // carousel variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a carousel with captions displayed below each slide
carouselWithCaptions :: CarouselConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
carouselWithCaptions config state slides' =
  E.div_
    [ E.class_ (String.joinWith " " ["carousel-container", "carousel-with-captions", config.cssClass]) ]
    [ renderTrack config state slides'
    , renderCaptionBar config state slides'
    , renderNavigation config.navigation config.loop state slides'
    ]

-- | Render the caption bar showing current slide's caption
renderCaptionBar :: CarouselConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
renderCaptionBar _config state slides' =
  case slideAt state.current slides' of
    Just slideData' -> 
      E.div_
        [ E.class_ "carousel-caption-bar" ]
        [ renderCaption slideData' ]
    Nothing -> 
      E.empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // position calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate a wave-based position offset for smooth oscillating effects
-- | Uses sine wave for natural motion. Returns offset in range [-amplitude, amplitude]
wavePosition :: Number -> Number -> Number -> Number
wavePosition progress amplitude frequency =
  let angle = progress * frequency * 2.0 * pi
  in amplitude * sin angle
  where
    pi = 3.14159265358979

-- | Calculate position on a circle given angle and radius
-- | Returns {x, y} coordinates for circular carousel layouts
circularPosition :: Number -> Number -> { x :: Number, y :: Number }
circularPosition angle radius =
  { x: radius * cos angle
  , y: radius * sin angle
  }

-- | Apply ease-out curve to a progress value using power function
-- | Higher power = more dramatic ease-out (starts fast, ends slow)
easeOutPosition :: Number -> Number -> Number
easeOutPosition progress power =
  let 
    -- Clamp progress to [0, 1]
    p = if progress < 0.0 then 0.0
        else if progress > 1.0 then 1.0
        else progress
    -- Ease-out: 1 - (1 - p)^power
    inverted = 1.0 - p
    eased = 1.0 - pow inverted power
  in eased

-- | Calculate absolute distance for position comparisons
-- | Used in visibility and effect calculations
positionDistance :: Number -> Number -> Number
positionDistance a b = abs (a - b)

-- | Default case helper for guard expressions
-- | Used in pattern guards as the final fallback
defaultCase :: forall a. a -> a
defaultCase x = if otherwise then x else x

-- Note: Navigation rendering has been moved to Render/Navigation.purs
-- The renderNavigation function is imported and used in the carousel function above.
-- This keeps Render.purs under 500 lines while maintaining full functionality.
-- 
-- sin, cos, abs, absInt, toInt are imported from Render/Layout.purs
-- pow is imported from Render/Effects.purs
