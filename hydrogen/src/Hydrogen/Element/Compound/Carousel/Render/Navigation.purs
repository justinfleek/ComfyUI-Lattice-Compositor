-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // element // carousel // render // navigation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Navigation — Render functions for navigation controls.
-- |
-- | ## Design Philosophy
-- |
-- | Navigation controls (arrows, dots, progress, thumbnails) are rendered
-- | as pure functions from config and state to Element. Each control type
-- | has configurable appearance and behavior.
-- |
-- | ## Navigation Types
-- |
-- | - Arrows: Prev/Next buttons with position and style options
-- | - Dots: Indicator dots showing current slide
-- | - Progress: Bar showing position in slideshow
-- | - Thumbnails: Strip of slide previews
-- |
-- | ## Dependencies
-- |
-- | - Carousel.State (CarouselState)
-- | - Carousel.Slide (SlideCollection, SlideData)
-- | - Carousel.Navigation (NavigationConfig)
-- | - Hydrogen.Render.Element

module Hydrogen.Element.Compound.Carousel.Render.Navigation
  ( -- * Main Navigation Renderer
    renderNavigation
  
  -- * Individual Renderers
  , renderArrows
  , renderDots
  , renderProgress
  , renderThumbnails
  
  -- * Position Converters
  , arrowPositionToClass
  , dotsPositionToClass
  , thumbnailPositionToClass
  
  -- * Thumbnail Content
  , renderThumbnail
  , renderThumbnailContent
  , contentKindToIcon
  , contentKindToLabel
  
  -- * Utility
  , makeSlideIndex
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
  , (>=)
  , (>)
  , (||)
  , (&&)
  , not
  )

import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing), maybe)
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Color.RGB as Color

import Hydrogen.Element.Compound.Carousel.Types 
  ( SlideIndex
  , slideIndex
  , unwrapSlideIndex
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
  , CarouselMsg
      ( GoToSlide
      , NextSlide
      , PrevSlide
      )
  )
import Hydrogen.Element.Compound.Carousel.State 
  ( CarouselState
  , isTransitioning
  , transitionProgress
  )
import Hydrogen.Element.Compound.Carousel.Slide 
  ( SlideCollection
  , SlideData
  , ContentSource
      ( SourceUrl
      , SourceData
      , SourceInline
      )
  , slideAt
  , slideCount
  )
import Hydrogen.Element.Compound.Carousel.Navigation 
  ( NavigationConfig
  , ArrowPosition
      ( ArrowsInside
      , ArrowsOutside
      , ArrowsOverlay
      )
  , DotsPosition
      ( DotsBottom
      , DotsTop
      , DotsLeft
      , DotsRight
      , DotsOverlay
      )
  , ThumbnailPosition
      ( ThumbnailsBottom
      , ThumbnailsTop
      , ThumbnailsLeft
      , ThumbnailsRight
      )
  )
import Hydrogen.Element.Compound.Carousel.Gestures (isDragActive)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // navigation container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render navigation controls
-- | Takes NavigationConfig and loop Boolean separately
renderNavigation :: NavigationConfig -> Boolean -> CarouselState -> SlideCollection -> E.Element CarouselMsg
renderNavigation config loop state slides' =
  E.div_
    [ E.class_ "carousel-navigation" ]
    [ renderArrows config loop state slides'
    , renderDots config state slides'
    , renderProgress config state slides'
    , renderThumbnails config state slides'
    ]

-- | Check if any gesture is currently active (for showing controls during interaction)
isAnyGestureActive :: CarouselState -> Boolean
isAnyGestureActive state = 
  isDragActive state.gesture.drag

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // arrows
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render arrow navigation
renderArrows :: NavigationConfig -> Boolean -> CarouselState -> SlideCollection -> E.Element CarouselMsg
renderArrows config loop state slides' =
  if config.arrows.enabled || isAnyGestureActive state then
    let
      currentIdx = unwrapSlideIndex state.current
      isFirst = currentIdx == 0
      isLast = currentIdx >= slideCount slides' - 1
      prevDisabled = not loop && isFirst
      nextDisabled = not loop && isLast
      positionClass = arrowPositionToClass config.arrows.position
      hoverClass = if config.arrows.showOnHover then " carousel-arrows-hover-only" else ""
      arrowColor = Color.rgbToRecord config.arrows.color
      arrowColorCss = "rgb(" <> show arrowColor.r <> "," <> show arrowColor.g <> "," <> show arrowColor.b <> ")"
      arrowSizePx = show (Device.unwrapPixel config.arrows.size) <> "px"
    in
      E.div_
        ([ E.class_ ("carousel-arrows " <> positionClass <> hoverClass) ] 
          <> E.styles [ Tuple "font-size" arrowSizePx ])
        [ E.button_
            ([ E.class_ ("carousel-arrow carousel-arrow-prev" <> if prevDisabled then " carousel-arrow-disabled" else "")
            , E.onClick PrevSlide
            , E.ariaLabel "Previous slide"
            , E.disabled prevDisabled
            ] <> E.styles [ Tuple "color" arrowColorCss ])
            [ E.text "\x2190" ]
        , E.button_
            ([ E.class_ ("carousel-arrow carousel-arrow-next" <> if nextDisabled then " carousel-arrow-disabled" else "")
            , E.onClick NextSlide
            , E.ariaLabel "Next slide"
            , E.disabled nextDisabled
            ] <> E.styles [ Tuple "color" arrowColorCss ])
            [ E.text "\x2192" ]
        ]
  else
    E.empty

-- | Convert arrow position to CSS class
arrowPositionToClass :: ArrowPosition -> String
arrowPositionToClass ArrowsInside = "carousel-arrows-inside"
arrowPositionToClass ArrowsOutside = "carousel-arrows-outside"
arrowPositionToClass ArrowsOverlay = "carousel-arrows-overlay"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // dots
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render dot indicators with active state
renderDots :: NavigationConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
renderDots config state slides' =
  if config.dots.enabled then
    let 
      currentIdx = unwrapSlideIndex state.current
      positionClass = dotsPositionToClass config.dots.position
      dotSize = show (Device.unwrapPixel config.dots.size) <> "px"
    in E.div_
        ([ E.class_ ("carousel-dots " <> positionClass) ]
          <> E.styles [ Tuple "--carousel-dot-size" dotSize ])
        (map (renderDot config currentIdx) (Array.range 0 (slideCount slides' - 1)))
  else
    E.empty

-- | Convert dots position to CSS class
dotsPositionToClass :: DotsPosition -> String
dotsPositionToClass DotsBottom = "carousel-dots-bottom"
dotsPositionToClass DotsTop = "carousel-dots-top"
dotsPositionToClass DotsLeft = "carousel-dots-left"
dotsPositionToClass DotsRight = "carousel-dots-right"
dotsPositionToClass DotsOverlay = "carousel-dots-overlay"

-- | Render a single dot with active highlighting
renderDot :: NavigationConfig -> Int -> Int -> E.Element CarouselMsg
renderDot config currentIdx index =
  let 
    isActive = index == currentIdx
    activeClass = if isActive then " carousel-dot-active" else ""
    dotColor = if isActive 
      then Color.rgbToRecord config.dots.activeColor
      else Color.rgbToRecord config.dots.inactiveColor
  in
    E.button_
      ([ E.class_ ("carousel-dot" <> activeClass)
      , E.onClick (GoToSlide (slideIndex index))
      , E.ariaLabel ("Go to slide " <> show (index + 1))
      , E.attr "aria-current" (if isActive then "true" else "false")
      ] <> E.styles [ Tuple "background-color" ("rgb(" <> show dotColor.r <> "," <> show dotColor.g <> "," <> show dotColor.b <> ")") ])
      []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render progress bar showing current position
renderProgress :: NavigationConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
renderProgress config state slides' =
  if config.progress.enabled then
    let 
      total = slideCount slides'
      currentIdx = unwrapSlideIndex state.current
      baseProgress = if total > 1 
        then toNumber currentIdx / toNumber (total - 1) * 100.0
        else 0.0
      progressPercent = if isTransitioning state.transition
        then 
          let 
            fromIdx = toNumber (unwrapSlideIndex state.transition.fromIndex)
            toIdx = toNumber (unwrapSlideIndex state.transition.toIndex)
            tProgress = transitionProgress state.transition
            fromPct = if total > 1 then fromIdx / toNumber (total - 1) * 100.0 else 0.0
            toPct = if total > 1 then toIdx / toNumber (total - 1) * 100.0 else 0.0
          in fromPct + (toPct - fromPct) * tProgress
        else baseProgress
      bgColor = Color.rgbToRecord config.progress.backgroundColor
      fillColor = Color.rgbToRecord config.progress.fillColor
      heightPx = show (Device.unwrapPixel config.progress.height)
      positionClass = if config.progress.showOnTop 
        then "carousel-progress-top" 
        else "carousel-progress-bottom"
    in
      E.div_
        ([ E.class_ ("carousel-progress " <> positionClass) ] 
          <> E.styles 
            [ Tuple "height" (heightPx <> "px")
            , Tuple "background-color" ("rgb(" <> show bgColor.r <> "," <> show bgColor.g <> "," <> show bgColor.b <> ")")
            ])
        [ E.div_
            ([ E.class_ "carousel-progress-fill" ] 
              <> E.styles 
                [ Tuple "width" (show progressPercent <> "%")
                , Tuple "background-color" ("rgb(" <> show fillColor.r <> "," <> show fillColor.g <> "," <> show fillColor.b <> ")")
                , Tuple "height" "100%"
                , Tuple "transition" "width 0.3s ease-out"
                ])
            []
        ]
  else
    E.empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // thumbnails
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render thumbnail navigation strip
renderThumbnails :: NavigationConfig -> CarouselState -> SlideCollection -> E.Element CarouselMsg
renderThumbnails config state slides' =
  if config.thumbnails.enabled then
    let
      currentIdx = unwrapSlideIndex state.current
      positionClass = thumbnailPositionToClass config.thumbnails.position
      gapPx = show (Device.unwrapPixel config.thumbnails.gap) <> "px"
      isVertical = case config.thumbnails.position of
        ThumbnailsLeft -> true
        ThumbnailsRight -> true
        _ -> false
      containerStyles = 
        [ Tuple "display" "flex"
        , Tuple "flex-direction" (if isVertical then "column" else "row")
        , Tuple "gap" gapPx
        , Tuple "align-items" "center"
        , Tuple "justify-content" "center"
        ]
    in
      E.div_
        ([ E.class_ ("carousel-thumbnails " <> positionClass) ] <> E.styles containerStyles)
        (Array.mapWithIndex (\i _ -> renderThumbnail config currentIdx i slides') (Array.range 0 (slideCount slides' - 1)))
  else
    E.empty

-- | Convert thumbnail position to CSS class
thumbnailPositionToClass :: ThumbnailPosition -> String
thumbnailPositionToClass ThumbnailsBottom = "carousel-thumbnails-bottom"
thumbnailPositionToClass ThumbnailsTop = "carousel-thumbnails-top"
thumbnailPositionToClass ThumbnailsLeft = "carousel-thumbnails-left"
thumbnailPositionToClass ThumbnailsRight = "carousel-thumbnails-right"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // thumbnail content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single thumbnail
renderThumbnail :: NavigationConfig -> Int -> Int -> SlideCollection -> E.Element CarouselMsg
renderThumbnail config currentIdx index slides' =
  case slideAt (slideIndex index) slides' of
    Just slideData' ->
      let
        isActive = index == currentIdx
        thumbConfig = config.thumbnails
        widthPx = show (Device.unwrapPixel thumbConfig.width) <> "px"
        heightPx = show (Device.unwrapPixel thumbConfig.height) <> "px"
        borderWidthPx = show (Device.unwrapPixel thumbConfig.borderWidth) <> "px"
        borderColor = if isActive 
          then Color.rgbToRecord thumbConfig.borderColor
          else Color.rgbToRecord thumbConfig.inactiveBorderColor
        borderColorCss = "rgb(" <> show borderColor.r <> "," <> show borderColor.g <> "," <> show borderColor.b <> ")"
        opacity = if isActive then thumbConfig.activeOpacity else thumbConfig.opacity
        activeClass = if isActive then " carousel-thumbnail-active" else ""
        thumbnailStyles =
          [ Tuple "width" widthPx
          , Tuple "height" heightPx
          , Tuple "border" (borderWidthPx <> " solid " <> borderColorCss)
          , Tuple "opacity" (show opacity)
          , Tuple "cursor" "pointer"
          , Tuple "overflow" "hidden"
          , Tuple "transition" "opacity 0.2s ease, border-color 0.2s ease"
          ]
      in
        E.button_
          ([ E.class_ ("carousel-thumbnail" <> activeClass)
           , E.onClick (GoToSlide (slideIndex index))
           , E.ariaLabel ("Go to slide " <> show (index + 1))
           , E.attr "aria-current" (if isActive then "true" else "false")
           ] <> E.styles thumbnailStyles)
          [ renderThumbnailContent slideData' ]
    Nothing ->
      E.empty

-- | Render thumbnail content based on slide kind
renderThumbnailContent :: SlideData -> E.Element CarouselMsg
renderThumbnailContent slideData' =
  case slideData'.kind of
    ContentImage -> renderImageThumbnail slideData'
    ContentVideo -> renderVideoThumbnail slideData'
    _ -> renderPlaceholderThumbnail slideData'

-- | Render image thumbnail (scaled image)
renderImageThumbnail :: SlideData -> E.Element CarouselMsg
renderImageThumbnail slideData' =
  case slideData'.source of
    SourceUrl url ->
      E.img_
        ([ E.src url
         , E.alt slideData'.alt
         , E.class_ "carousel-thumbnail-image"
         ] <> E.styles
          [ Tuple "width" "100%"
          , Tuple "height" "100%"
          , Tuple "object-fit" "cover"
          ])
    SourceData dataUri ->
      E.img_
        ([ E.src dataUri
         , E.alt slideData'.alt
         , E.class_ "carousel-thumbnail-image"
         ] <> E.styles
          [ Tuple "width" "100%"
          , Tuple "height" "100%"
          , Tuple "object-fit" "cover"
          ])
    SourceInline _ ->
      renderPlaceholderThumbnail slideData'

-- | Render video thumbnail (video poster or play icon placeholder)
renderVideoThumbnail :: SlideData -> E.Element CarouselMsg
renderVideoThumbnail slideData' =
  E.div_
    ([ E.class_ "carousel-thumbnail-video" ] <> E.styles
      [ Tuple "width" "100%"
      , Tuple "height" "100%"
      , Tuple "display" "flex"
      , Tuple "align-items" "center"
      , Tuple "justify-content" "center"
      , Tuple "background-color" "#1f2937"
      ])
    [ E.div_
        [ E.class_ "carousel-thumbnail-play-icon" ]
        [ E.text "\x25B6" ]
    , E.span_
        [ E.class_ "carousel-thumbnail-video-label" ]
        [ E.text (maybe "Video" (\t -> t) slideData'.title) ]
    ]

-- | Render placeholder thumbnail for non-visual content
renderPlaceholderThumbnail :: SlideData -> E.Element CarouselMsg
renderPlaceholderThumbnail slideData' =
  let
    iconText = contentKindToIcon slideData'.kind
    labelText = maybe (contentKindToLabel slideData'.kind) (\t -> t) slideData'.title
  in
    E.div_
      ([ E.class_ "carousel-thumbnail-placeholder" ] <> E.styles
        [ Tuple "width" "100%"
        , Tuple "height" "100%"
        , Tuple "display" "flex"
        , Tuple "flex-direction" "column"
        , Tuple "align-items" "center"
        , Tuple "justify-content" "center"
        , Tuple "background-color" "#374151"
        , Tuple "color" "#d1d5db"
        , Tuple "font-size" "10px"
        ])
      [ E.div_
          [ E.class_ "carousel-thumbnail-icon" ]
          [ E.text iconText ]
      , E.span_
          [ E.class_ "carousel-thumbnail-label" ]
          [ E.text labelText ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // content icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get icon character for content kind
contentKindToIcon :: ContentKind -> String
contentKindToIcon ContentImage = "\x1F5BC"
contentKindToIcon ContentVideo = "\x25B6"
contentKindToIcon ContentAudio = "\x266B"
contentKindToIcon ContentEmbed = "\x1F310"
contentKindToIcon ContentText = "\x1F4DD"
contentKindToIcon ContentCard = "\x1F4C4"
contentKindToIcon ContentHTML = "</>"
contentKindToIcon ContentCanvas = "\x1F3A8"
contentKindToIcon ContentWebGL = "\x1F4BB"
contentKindToIcon ContentGame = "\x1F3AE"
contentKindToIcon ContentLiveData = "\x1F4CA"
contentKindToIcon ContentInteractive = "\x1F446"

-- | Get label for content kind
contentKindToLabel :: ContentKind -> String
contentKindToLabel ContentImage = "Image"
contentKindToLabel ContentVideo = "Video"
contentKindToLabel ContentAudio = "Audio"
contentKindToLabel ContentEmbed = "Embed"
contentKindToLabel ContentText = "Text"
contentKindToLabel ContentCard = "Card"
contentKindToLabel ContentHTML = "HTML"
contentKindToLabel ContentCanvas = "Canvas"
contentKindToLabel ContentWebGL = "WebGL"
contentKindToLabel ContentGame = "Game"
contentKindToLabel ContentLiveData = "Live"
contentKindToLabel ContentInteractive = "Interactive"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // utility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a SlideIndex from an Int
-- | Wraps the raw index value into the SlideIndex type
-- | Useful for external code that needs to construct slide indices
makeSlideIndex :: Int -> SlideIndex
makeSlideIndex = slideIndex
