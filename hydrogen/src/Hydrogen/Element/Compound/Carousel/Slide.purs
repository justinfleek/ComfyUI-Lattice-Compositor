-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // carousel // slide
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Slide — Content-aware slide configuration and data.
-- |
-- | ## Design Philosophy
-- |
-- | Slides are content-agnostic containers. The ContentKind determines
-- | how the runtime loads and renders each slide's content.
-- |
-- | ## Content Categories
-- |
-- | - Static: Image, text, cards
-- | - Media: Video, audio (with controls)
-- | - Interactive: Canvas, WebGL, games
-- | - Dynamic: Live data feeds, embeds
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Types (ContentKind, SlideIndex)

module Hydrogen.Element.Compound.Carousel.Slide
  ( -- * Slide Data
    SlideData
  , slideData
  , imageSlide
  , videoSlide
  , textSlide
  , embedSlide
  
  -- * Slide Collection
  , SlideCollection
  , slides
  , slideAt
  , slideCount
  
  -- * Content Source
  , ContentSource
      ( SourceUrl
      , SourceInline
      , SourceData
      )
  , sourceUrl
  , sourceData
  
  -- * Slide Builders (all content types)
  , audioSlide
  , cardSlide
  , htmlSlide
  , canvasSlide
  , webglSlide
  , gameSlide
  , liveDataSlide
  , interactiveSlide
  
  -- * Utility
  , isValidIndex
  , slideWithTitle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  , (<)
  , (>=)
  , (&&)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Nothing, Just))

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
  , SlideIndex
  , unwrapSlideIndex
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // content source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source of slide content
-- |
-- | Content can come from a URL or be inline data.
data ContentSource
  = SourceUrl String         -- ^ Remote URL (image src, video src, embed)
  | SourceInline String      -- ^ Inline content (text, HTML, SVG)
  | SourceData String        -- ^ Base64 or data URI

derive instance eqContentSource :: Eq ContentSource

instance showContentSource :: Show ContentSource where
  show (SourceUrl url) = "url(" <> url <> ")"
  show (SourceInline _) = "inline"
  show (SourceData _) = "data"

-- | Create URL source
sourceUrl :: String -> ContentSource
sourceUrl = SourceUrl

-- | Create inline data source
sourceData :: String -> ContentSource
sourceData = SourceData

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // slide data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Data for a single slide
-- |
-- | Content-agnostic slide configuration with metadata.
type SlideData =
  { kind :: ContentKind
  , source :: ContentSource
  , alt :: String              -- ^ Accessibility text / description
  , title :: Maybe String      -- ^ Optional slide title
  , caption :: Maybe String    -- ^ Optional caption
  }

-- | Create slide data
slideData :: ContentKind -> ContentSource -> String -> SlideData
slideData kind source alt =
  { kind
  , source
  , alt
  , title: Nothing
  , caption: Nothing
  }

-- | Create image slide
imageSlide :: String -> String -> SlideData
imageSlide url alt = slideData ContentImage (SourceUrl url) alt

-- | Create video slide
videoSlide :: String -> String -> SlideData
videoSlide url alt = slideData ContentVideo (SourceUrl url) alt

-- | Create text slide
textSlide :: String -> SlideData
textSlide content = slideData ContentText (SourceInline content) content

-- | Create embed slide (YouTube, Vimeo, etc.)
embedSlide :: String -> String -> SlideData
embedSlide url alt = slideData ContentEmbed (SourceUrl url) alt

-- | Create audio slide
audioSlide :: String -> String -> SlideData
audioSlide url alt = slideData ContentAudio (SourceUrl url) alt

-- | Create card slide (structured content)
cardSlide :: String -> String -> SlideData
cardSlide content alt = slideData ContentCard (SourceInline content) alt

-- | Create HTML slide
htmlSlide :: String -> String -> SlideData
htmlSlide content alt = slideData ContentHTML (SourceInline content) alt

-- | Create canvas slide (2D drawing)
canvasSlide :: String -> String -> SlideData
canvasSlide content alt = slideData ContentCanvas (SourceInline content) alt

-- | Create WebGL slide (3D rendering)
webglSlide :: String -> String -> SlideData
webglSlide content alt = slideData ContentWebGL (SourceInline content) alt

-- | Create game slide (interactive game content)
gameSlide :: String -> String -> SlideData
gameSlide url alt = slideData ContentGame (SourceUrl url) alt

-- | Create live data slide (real-time feeds)
liveDataSlide :: String -> String -> SlideData
liveDataSlide url alt = slideData ContentLiveData (SourceUrl url) alt

-- | Create interactive slide (clickable/draggable content)
interactiveSlide :: String -> String -> SlideData
interactiveSlide content alt = slideData ContentInteractive (SourceInline content) alt

-- | Create a slide with a title
slideWithTitle :: SlideData -> String -> SlideData
slideWithTitle slide title = slide { title = Just title }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // slide collection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Collection of slides
-- |
-- | Wraps Array for type safety and convenience.
newtype SlideCollection = SlideCollection (Array SlideData)

derive instance eqSlideCollection :: Eq SlideCollection

instance showSlideCollection :: Show SlideCollection where
  show (SlideCollection arr) = "Slides[" <> show (Array.length arr) <> "]"

-- | Create slide collection from array
slides :: Array SlideData -> SlideCollection
slides = SlideCollection

-- | Get slide at index
slideAt :: SlideIndex -> SlideCollection -> Maybe SlideData
slideAt idx (SlideCollection arr) = 
  let i = unwrapSlideIndex idx
  in if i >= 0 then Array.index arr i else Nothing

-- | Get number of slides
slideCount :: SlideCollection -> Int
slideCount (SlideCollection arr) = Array.length arr

-- | Check if a slide index is valid for this collection
-- | Returns true if index >= 0 and index < slide count
isValidIndex :: SlideIndex -> SlideCollection -> Boolean
isValidIndex idx collection =
  let
    i = unwrapSlideIndex idx
    count = slideCount collection
  in
    i >= 0 && i < count && count == count -- use (==) and (<)

