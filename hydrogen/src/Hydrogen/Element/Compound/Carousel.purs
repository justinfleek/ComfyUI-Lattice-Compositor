-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // element // carousel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel — Leader module re-exporting the modular carousel system.
-- |
-- | ## Architecture
-- |
-- | The carousel is composed of the following sub-modules:
-- |
-- | - **Types**: Core type definitions (SlideIndex, TransitionKind, etc.)
-- | - **Effects**: Visual effects (opacity, scale, blur, etc.)
-- | - **Gestures**: Input state (swipe, drag, pinch, retinal)
-- | - **Transitions**: Animation configurations
-- | - **State**: Runtime state compound
-- | - **Slide**: Content-aware slide data
-- | - **Navigation**: Navigation UI configs
-- | - **Render**: Pure render function
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Carousel as Carousel
-- |
-- | view :: Carousel.CarouselState -> Element Carousel.CarouselMsg
-- | view state = 
-- |   Carousel.carousel Carousel.defaultConfig state mySlides
-- | ```

module Hydrogen.Element.Compound.Carousel
  ( -- * Re-exports from Types
    module Hydrogen.Element.Compound.Carousel.Types
  
  -- * Re-exports from Effects
  , module Hydrogen.Element.Compound.Carousel.Effects
  
  -- * Re-exports from Gestures
  , module Hydrogen.Element.Compound.Carousel.Gestures
  
  -- * Re-exports from Transitions
  , module Hydrogen.Element.Compound.Carousel.Transitions
  
  -- * Re-exports from State
  , module Hydrogen.Element.Compound.Carousel.State
  
  -- * Re-exports from Slide
  , module Hydrogen.Element.Compound.Carousel.Slide
  
  -- * Re-exports from Navigation
  , module Hydrogen.Element.Compound.Carousel.Navigation
  
  -- * Re-exports from Render
  , module Hydrogen.Element.Compound.Carousel.Render
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Element.Compound.Carousel.Types 
  ( AutoplayMode
      ( AutoplayOff
      , AutoplayTimed
      , AutoplayContentAware
      , AutoplayAdaptive
      , AutoplayOnVisible
      , AutoplayOnFocus
      , AutoplayOnRetinalFocus
      )
  , ContentKind
      ( ContentImage
      , ContentVideo
      , ContentAudio
      , ContentEmbed
      , ContentText
      , ContentCard
      , ContentHTML
      , ContentCanvas
      , ContentWebGL
      , ContentGame
      , ContentLiveData
      , ContentInteractive
      )
  , FocusMode
      ( FocusKeyboard
      , FocusMouse
      , FocusTouch
      , FocusProximity
      , FocusRetinal
      , FocusRetinalDwell
      , FocusRetinalSaccade
      , FocusAttention
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
  , NavigationMode
      ( NavArrows
      , NavDots
      , NavThumbnails
      , NavProgress
      , NavKeyboard
      , NavSwipe
      , NavDrag
      , NavScroll
      , NavPinch
      , NavVoice
      , NavRetinal
      , NavBrainwave
      )
  , SlideIndex
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
  , firstSlide
  , nextIndex
  , prevIndex
  , slideIndex
  , unwrapSlideIndex
  )
import Hydrogen.Element.Compound.Carousel.Effects 
  ( BlurEffect
  , EffectKind
      ( EffectOpacity
      , EffectScale
      , EffectBlur
      , EffectRotation
      , EffectReflection
      , EffectParallax
      , EffectGrayscale
      , EffectGlow
      , EffectShadow
      , EffectBrightness
      , EffectContrast
      , EffectHueShift
      )
  , EffectToggle
  , GlowEffect
  , GrayscaleEffect
  , OpacityEffect
  , ParallaxDirection
      ( ParallaxHorizontal
      , ParallaxVertical
      , ParallaxBoth
      )
  , ParallaxEffect
  , ReflectionEffect
  , RotationEffect
  , ScaleEffect
  , SlideEffects
  , activeBlur
  , activeOpacity
  , activeScale
  , blurEffect
  , defaultBlurEffect
  , defaultEffects
  , defaultGlowEffect
  , defaultGrayscaleEffect
  , defaultOpacityEffect
  , defaultParallaxEffect
  , defaultReflectionEffect
  , defaultRotationEffect
  , defaultScaleEffect
  , disableEffect
  , effectToggle
  , enableEffect
  , glowEffect
  , grayscaleEffect
  , inactiveBlur
  , inactiveOpacity
  , inactiveScale
  , isEffectEnabled
  , noEffects
  , opacityEffect
  , parallaxEffect
  , reflectionEffect
  , rotationEffect
  , scaleEffect
  )
import Hydrogen.Element.Compound.Carousel.Gestures 
  ( DragGesture
  , GestureState
  , PinchGesture
  , RetinalState
  , ScrollGesture
  , SwipeGesture
  , VoiceCommand
      ( VoiceNext
      , VoicePrevious
      , VoiceFirst
      , VoiceLast
      , VoiceGoTo
      , VoiceStop
      , VoicePlay
      )
  , VoiceState
  , dragGesture
  , dragOffset
  , gazeDwellTime
  , gazePosition
  , initialGestureState
  , isAnyGestureActive
  , isDragActive
  , isGazeFocused
  , isListening
  , isPinchActive
  , isRetinalTracking
  , isSwipeActive
  , lastCommand
  , noDragGesture
  , noPinchGesture
  , noRetinalState
  , noScrollGesture
  , noSwipeGesture
  , noVoiceState
  , pinchGesture
  , pinchScale
  , retinalState
  , scrollDelta
  , scrollGesture
  , swipeGesture
  , swipeProgress
  , voiceState
  )
import Hydrogen.Element.Compound.Carousel.Transitions 
  ( EasingFunction
      ( EaseLinear
      , EaseIn
      , EaseOut
      , EaseInOut
      , EaseInQuad
      , EaseOutQuad
      , EaseInOutQuad
      , EaseInCubic
      , EaseOutCubic
      , EaseInOutCubic
      , EaseInQuart
      , EaseOutQuart
      , EaseInOutQuart
      , EaseInExpo
      , EaseOutExpo
      , EaseInOutExpo
      , EaseInBack
      , EaseOutBack
      , EaseInOutBack
      , EaseSpring
      , EaseBounce
      , EaseCustom
      )
  , TransitionConfig
  , coverflowTransition
  , cubeTransition
  , defaultTransition
  , easingToCss
  , fadeTransition
  , flipTransition
  , instantTransition
  , slideTransition
  , slowTransition
  , transitionConfig
  , zoomTransition
  )
import Hydrogen.Element.Compound.Carousel.State 
  ( AutoplayState
  , CarouselState
  , TransitionState
  , autoplayState
  , autoplaying
  , currentIndex
  , initialState
  , isAutoplaying
  , isFirstSlide
  , isLastSlide
  , isTransitioning
  , noTransition
  , paused
  , totalSlides
  , transitionProgress
  , transitionState
  )
import Hydrogen.Element.Compound.Carousel.Slide 
  ( ContentSource
      ( SourceUrl
      , SourceInline
      , SourceData
      )
  , SlideCollection
  , SlideData
  , embedSlide
  , imageSlide
  , slideAt
  , slideCount
  , slideData
  , slides
  , sourceData
  , sourceUrl
  , textSlide
  , videoSlide
  )
import Hydrogen.Element.Compound.Carousel.Navigation 
  ( ArrowConfig
  , ArrowPosition
      ( ArrowsInside
      , ArrowsOutside
      , ArrowsOverlay
      )
  , DotsConfig
  , DotsPosition
      ( DotsBottom
      , DotsTop
      , DotsLeft
      , DotsRight
      , DotsOverlay
      )
  , NavigationConfig
  , ProgressConfig
  , arrowConfig
  , defaultArrows
  , defaultDots
  , defaultNavigation
  , defaultProgress
  , dotsConfig
  , fullNavigation
  , minimalNavigation
  , progressConfig
  )
import Hydrogen.Element.Compound.Carousel.Render 
  ( CarouselConfig
  , CarouselMsg
      ( GoToSlide
      , NextSlide
      , PrevSlide
      , StartAutoplay
      , StopAutoplay
      , ToggleAutoplay
      )
  , carousel
  , defaultConfig
  , getGestureState
  , getTransitionState
  )
