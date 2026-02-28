-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // element // carousel // render // content
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Content — Slide content rendering for all content types.
-- |
-- | ## Design Philosophy
-- |
-- | Each ContentKind has a dedicated render function that produces
-- | appropriate HTML structure. Content renderers are pure functions
-- | from SlideData to Element.
-- |
-- | ## Content Types
-- |
-- | - Image: img with src/alt
-- | - Video: video element with source
-- | - Audio: audio element with visualization placeholder
-- | - Embed: iframe for YouTube/Vimeo/etc
-- | - Text: rich text block
-- | - Card: structured card layout
-- | - HTML: raw HTML (sanitized by runtime)
-- | - Canvas/WebGL/Game: placeholders for runtime
-- | - LiveData/Interactive: dynamic content placeholders
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Slide (SlideData, ContentSource)
-- | - Hydrogen.Render.Element

module Hydrogen.Element.Compound.Carousel.Render.Content
  ( -- * Main Content Renderer
    renderSlideContent
  , renderCaption
  
  -- * Individual Renderers
  , renderImageContent
  , renderVideoContent
  , renderAudioContent
  , renderEmbedContent
  , renderTextContent
  , renderCardContent
  , renderHTMLContent
  , renderCanvasContent
  , renderWebGLContent
  , renderGameContent
  , renderLiveDataContent
  , renderInteractiveContent
  
  -- * Helpers
  , getSourceText
  , guessVideoMimeType
  , guessAudioMimeType
  , isVideoEmbedUrl
  
  -- * Debug
  , debugSlideInfo
  , showContentKind
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Show
  , show
  , (<>)
  , (==)
  , (-)
  , (+)
  , (>)
  , (||)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing), maybe, fromMaybe)
import Data.String (drop, length, take) as String
import Data.String.Pattern (Pattern(Pattern))

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Carousel.Slide 
  ( SlideData
  , ContentSource
      ( SourceUrl
      , SourceInline
      , SourceData
      )
  )
import Hydrogen.Element.Compound.Carousel.Types 
  ( ContentKind
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
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // main content render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render slide content based on ContentKind
renderSlideContent :: forall msg. SlideData -> E.Element msg
renderSlideContent slideData' =
  E.div_
    [ E.class_ ("carousel-slide-content carousel-content-" <> show slideData'.kind) ]
    [ contentElement
    , renderCaption slideData'
    ]
  where
    contentElement = case slideData'.kind of
      ContentImage -> renderImageContent slideData'
      ContentVideo -> renderVideoContent slideData'
      ContentAudio -> renderAudioContent slideData'
      ContentEmbed -> renderEmbedContent slideData'
      ContentText -> renderTextContent slideData'
      ContentCard -> renderCardContent slideData'
      ContentHTML -> renderHTMLContent slideData'
      ContentCanvas -> renderCanvasContent slideData'
      ContentWebGL -> renderWebGLContent slideData'
      ContentGame -> renderGameContent slideData'
      ContentLiveData -> renderLiveDataContent slideData'
      ContentInteractive -> renderInteractiveContent slideData'

-- | Render optional caption
renderCaption :: forall msg. SlideData -> E.Element msg
renderCaption slideData' =
  case slideData'.caption of
    Just caption ->
      E.div_
        [ E.class_ "carousel-caption" ]
        [ E.text caption ]
    Nothing ->
      E.empty

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // image content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render image content
renderImageContent :: forall msg. SlideData -> E.Element msg
renderImageContent slideData' =
  case slideData'.source of
    SourceUrl url ->
      E.img_
        [ E.src url
        , E.alt slideData'.alt
        , E.class_ "carousel-image"
        ]
    SourceData dataUri ->
      E.img_
        [ E.src dataUri
        , E.alt slideData'.alt
        , E.class_ "carousel-image"
        ]
    SourceInline svgContent ->
      E.div_
        [ E.class_ "carousel-image carousel-svg-container" ]
        [ E.text svgContent ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // video content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render video content with controls
renderVideoContent :: forall msg. SlideData -> E.Element msg
renderVideoContent slideData' =
  case slideData'.source of
    SourceUrl url ->
      E.element "video"
        [ E.class_ "carousel-video"
        , E.attr "controls" "true"
        , E.attr "preload" "metadata"
        , E.ariaLabel slideData'.alt
        ]
        [ E.element "source"
            [ E.src url
            , E.attr "type" (guessVideoMimeType url)
            ]
            []
        , E.text "Your browser does not support video."
        ]
    _ ->
      E.div_
        [ E.class_ "carousel-video-placeholder" ]
        [ E.text slideData'.alt ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // audio content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render audio content with visualization placeholder
renderAudioContent :: forall msg. SlideData -> E.Element msg
renderAudioContent slideData' =
  E.div_
    [ E.class_ "carousel-audio-container" ]
    [ E.div_
        [ E.class_ "carousel-audio-visualization" ]
        []
    , case slideData'.source of
        SourceUrl url ->
          E.element "audio"
            [ E.class_ "carousel-audio"
            , E.attr "controls" "true"
            , E.ariaLabel slideData'.alt
            ]
            [ E.element "source"
                [ E.src url
                , E.attr "type" (guessAudioMimeType url)
                ]
                []
            ]
        _ ->
          E.empty
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // embed content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render embed content (iframe for YouTube, Vimeo, etc.)
renderEmbedContent :: forall msg. SlideData -> E.Element msg
renderEmbedContent slideData' =
  case slideData'.source of
    SourceUrl url ->
      let 
        embedClass = if isVideoEmbedUrl url 
          then "carousel-embed carousel-embed-video" 
          else "carousel-embed"
        allowAttr = if isVideoEmbedUrl url
          then "accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture"
          else "clipboard-write; encrypted-media"
      in
        E.div_
          [ E.class_ "carousel-embed-container" ]
          [ E.element "iframe"
              [ E.class_ embedClass
              , E.src url
              , E.attr "frameborder" "0"
              , E.attr "allowfullscreen" "true"
              , E.attr "allow" allowAttr
              , E.title slideData'.alt
              ]
              []
          ]
    _ ->
      E.div_
        [ E.class_ "carousel-embed-placeholder" ]
        [ E.text slideData'.alt ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render text content (rich text block)
renderTextContent :: forall msg. SlideData -> E.Element msg
renderTextContent slideData' =
  E.div_
    [ E.class_ "carousel-text" ]
    [ maybe E.empty (\t -> E.h2_ [ E.class_ "carousel-text-title" ] [ E.text t ]) slideData'.title
    , E.div_
        [ E.class_ "carousel-text-body" ]
        [ E.text (getSourceText slideData'.source) ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // card content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render card content (structured card)
renderCardContent :: forall msg. SlideData -> E.Element msg
renderCardContent slideData' =
  E.div_
    [ E.class_ "carousel-card" ]
    [ maybe E.empty (\t -> E.div_ [ E.class_ "carousel-card-header" ] [ E.text t ]) slideData'.title
    , E.div_
        [ E.class_ "carousel-card-body" ]
        [ E.text (getSourceText slideData'.source) ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // html content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render arbitrary HTML content
renderHTMLContent :: forall msg. SlideData -> E.Element msg
renderHTMLContent slideData' =
  E.div_
    [ E.class_ "carousel-html" ]
    [ E.text (getSourceText slideData'.source) ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // canvas content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render canvas placeholder (2D rendering handled by runtime)
renderCanvasContent :: forall msg. SlideData -> E.Element msg
renderCanvasContent slideData' =
  E.element "canvas"
    [ E.class_ "carousel-canvas"
    , E.attr "data-source" (getSourceText slideData'.source)
    , E.ariaLabel slideData'.alt
    ]
    []

-- | Render WebGL placeholder (3D rendering handled by runtime)
renderWebGLContent :: forall msg. SlideData -> E.Element msg
renderWebGLContent slideData' =
  E.element "canvas"
    [ E.class_ "carousel-webgl"
    , E.attr "data-source" (getSourceText slideData'.source)
    , E.ariaLabel slideData'.alt
    ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // game content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render game/simulation placeholder (handled by runtime)
renderGameContent :: forall msg. SlideData -> E.Element msg
renderGameContent slideData' =
  let 
    loadingMessage = fromMaybe "Loading interactive content..." slideData'.title
  in
    E.div_
      [ E.class_ "carousel-game"
      , E.attr "data-source" (getSourceText slideData'.source)
      , E.ariaLabel slideData'.alt
      ]
      [ E.div_
          [ E.class_ "carousel-game-loading" ]
          [ E.text loadingMessage ]
      ]

-- | Render live data content (updates handled by runtime)
renderLiveDataContent :: forall msg. SlideData -> E.Element msg
renderLiveDataContent slideData' =
  E.div_
    [ E.class_ "carousel-live-data"
    , E.attr "data-source" (getSourceText slideData'.source)
    ]
    [ E.div_
        [ E.class_ "carousel-live-data-display" ]
        [ E.text slideData'.alt ]
    ]

-- | Render interactive content placeholder
renderInteractiveContent :: forall msg. SlideData -> E.Element msg
renderInteractiveContent slideData' =
  E.div_
    [ E.class_ "carousel-interactive"
    , E.attr "data-source" (getSourceText slideData'.source)
    ]
    [ E.text slideData'.alt ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract text from content source
getSourceText :: ContentSource -> String
getSourceText (SourceUrl url) = url
getSourceText (SourceInline text) = text
getSourceText (SourceData data') = data'

-- | Guess video MIME type from URL
guessVideoMimeType :: String -> String
guessVideoMimeType url
  | endsWith ".mp4" url = "video/mp4"
  | endsWith ".webm" url = "video/webm"
  | endsWith ".ogg" url = "video/ogg"
  | endsWith ".mov" url = "video/quicktime"
  | otherwise = "video/mp4"

-- | Guess audio MIME type from URL
guessAudioMimeType :: String -> String
guessAudioMimeType url
  | endsWith ".mp3" url = "audio/mpeg"
  | endsWith ".wav" url = "audio/wav"
  | endsWith ".ogg" url = "audio/ogg"
  | endsWith ".m4a" url = "audio/mp4"
  | otherwise = "audio/mpeg"

-- | Check if string ends with suffix
endsWith :: String -> String -> Boolean
endsWith suffix str = 
  let strLen = String.length str
      suffixLen = String.length suffix
  in if suffixLen > strLen 
     then false
     else String.drop (strLen - suffixLen) str == suffix

-- | Check if URL is from a video platform
isVideoEmbedUrl :: String -> Boolean
isVideoEmbedUrl url = 
  containsSubstring (Pattern "youtube.com") url 
    || containsSubstring (Pattern "youtu.be") url
    || containsSubstring (Pattern "vimeo.com") url
    || containsSubstring (Pattern "twitch.tv") url

-- | Check if string contains a pattern
containsSubstring :: Pattern -> String -> Boolean
containsSubstring (Pattern needle) haystack =
  let needleLen = String.length needle
      haystackLen = String.length haystack
      maxIdx = haystackLen - needleLen
  in if needleLen > haystackLen
     then false
     else checkFrom 0 maxIdx
  where
    checkFrom :: Int -> Int -> Boolean
    checkFrom idx maxI
      | idx > maxI = false
      | String.take (String.length needle) (String.drop idx haystack) == needle = true
      | otherwise = checkFrom (idx + 1) maxI

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // debug
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate debug info for a slide (useful for development/logging)
-- | Uses Show constraint to format any showable content metadata
debugSlideInfo :: forall a. Show a => a -> SlideData -> String
debugSlideInfo metadata slideData' =
  "Slide[" <> showContentKind slideData'.kind <> "]: " 
    <> slideData'.alt 
    <> " (meta: " <> show metadata <> ")"

-- | Convert ContentKind to display string
showContentKind :: ContentKind -> String
showContentKind = show
