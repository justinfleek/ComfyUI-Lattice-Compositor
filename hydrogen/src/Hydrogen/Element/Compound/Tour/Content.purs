-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // tour // content
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Content — Step content types and configurations.
-- |
-- | ## Architecture
-- |
-- | Step content supports multiple formats:
-- | - Text (title + description)
-- | - Rich HTML
-- | - Media (images, videos, GIFs)
-- | - Interactive elements
-- | - Custom components
-- |
-- | ## Schema Mapping
-- |
-- | | Type            | Pillar    | Purpose                              |
-- | |-----------------|-----------|--------------------------------------|
-- | | ContentKind     | Material  | Type of content in step              |
-- | | MediaType       | Material  | Image, video, GIF, etc.              |
-- | | InteractiveKind | Gestural  | Type of interactive element          |
-- | | TooltipSize     | Dimension | Size constraints for tooltip         |
-- | | ContentAlign    | Spatial   | How content is aligned               |

module Hydrogen.Element.Compound.Tour.Content
  ( -- * Content Kind
    ContentKind
      ( ContentText
      , ContentRichText
      , ContentMedia
      , ContentInteractive
      , ContentChecklist
      , ContentVideo
      , ContentCode
      , ContentCustom
      )
  
  -- * Media Type
  , MediaType
      ( MediaImage
      , MediaGif
      , MediaVideo
      , MediaLottie
      , MediaRive
      , MediaSvg
      )
  
  -- * Interactive Kind
  , InteractiveKind
      ( InteractiveClick
      , InteractiveInput
      , InteractiveSelect
      , InteractiveToggle
      , InteractiveHotspot
      , InteractiveTask
      )
  
  -- * Tooltip Size
  , TooltipSize
      ( SizeAuto
      , SizeSmall
      , SizeMedium
      , SizeLarge
      , SizeFullWidth
      , SizeCustom
      )
  , sizeToMaxWidth
  
  -- * Content Alignment
  , ContentAlign
      ( AlignLeft
      , AlignCenter
      , AlignRight
      )
  
  -- * Text Content
  , TextContent
  , textContent
  , withSubtitle
  , withDescription
  
  -- * Media Content
  , MediaContent
  , imageContent
  , videoContent
  , gifContent
  
  -- * Checklist Item
  , ChecklistItem
  , checklistItem
  , requiredItem
  , optionalItem
  
  -- * Content Config
  , ContentConfig
  , defaultContentConfig
  , mediaContentConfig
  , interactiveContentConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Bounded
  , class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // content kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of content displayed in a tour step.
data ContentKind
  = ContentText          -- ^ Simple title + description
  | ContentRichText      -- ^ Rich HTML/markdown content
  | ContentMedia         -- ^ Media with optional text
  | ContentInteractive   -- ^ Interactive element (task to complete)
  | ContentChecklist     -- ^ Checklist of items to complete
  | ContentVideo         -- ^ Video tutorial
  | ContentCode          -- ^ Code snippet with highlighting
  | ContentCustom        -- ^ Custom rendered content

derive instance eqContentKind :: Eq ContentKind
derive instance ordContentKind :: Ord ContentKind

instance showContentKind :: Show ContentKind where
  show ContentText = "text"
  show ContentRichText = "rich-text"
  show ContentMedia = "media"
  show ContentInteractive = "interactive"
  show ContentChecklist = "checklist"
  show ContentVideo = "video"
  show ContentCode = "code"
  show ContentCustom = "custom"

instance boundedContentKind :: Bounded ContentKind where
  bottom = ContentText
  top = ContentCustom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // media type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of media content.
data MediaType
  = MediaImage    -- ^ Static image (jpg, png, webp)
  | MediaGif      -- ^ Animated GIF
  | MediaVideo    -- ^ Video (mp4, webm)
  | MediaLottie   -- ^ Lottie animation (JSON)
  | MediaRive     -- ^ Rive animation
  | MediaSvg      -- ^ SVG illustration

derive instance eqMediaType :: Eq MediaType
derive instance ordMediaType :: Ord MediaType

instance showMediaType :: Show MediaType where
  show MediaImage = "image"
  show MediaGif = "gif"
  show MediaVideo = "video"
  show MediaLottie = "lottie"
  show MediaRive = "rive"
  show MediaSvg = "svg"

instance boundedMediaType :: Bounded MediaType where
  bottom = MediaImage
  top = MediaSvg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // interactive kind
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of interactive element the user must engage with.
data InteractiveKind
  = InteractiveClick    -- ^ Must click target element
  | InteractiveInput    -- ^ Must enter text in input
  | InteractiveSelect   -- ^ Must select from dropdown
  | InteractiveToggle   -- ^ Must toggle switch/checkbox
  | InteractiveHotspot  -- ^ Must click hotspot in image
  | InteractiveTask     -- ^ Must complete arbitrary task

derive instance eqInteractiveKind :: Eq InteractiveKind
derive instance ordInteractiveKind :: Ord InteractiveKind

instance showInteractiveKind :: Show InteractiveKind where
  show InteractiveClick = "click"
  show InteractiveInput = "input"
  show InteractiveSelect = "select"
  show InteractiveToggle = "toggle"
  show InteractiveHotspot = "hotspot"
  show InteractiveTask = "task"

instance boundedInteractiveKind :: Bounded InteractiveKind where
  bottom = InteractiveClick
  top = InteractiveTask

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // tooltip size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Size constraints for tooltip.
data TooltipSize
  = SizeAuto        -- ^ Auto-size based on content
  | SizeSmall       -- ^ Small (280px max-width)
  | SizeMedium      -- ^ Medium (360px max-width)
  | SizeLarge       -- ^ Large (480px max-width)
  | SizeFullWidth   -- ^ Full viewport width (modal-like)
  | SizeCustom Int  -- ^ Custom max-width in pixels

derive instance eqTooltipSize :: Eq TooltipSize
derive instance ordTooltipSize :: Ord TooltipSize

instance showTooltipSize :: Show TooltipSize where
  show SizeAuto = "auto"
  show SizeSmall = "small"
  show SizeMedium = "medium"
  show SizeLarge = "large"
  show SizeFullWidth = "full-width"
  show (SizeCustom w) = "custom(" <> show w <> "px)"

instance boundedTooltipSize :: Bounded TooltipSize where
  bottom = SizeAuto
  top = SizeCustom 0

-- | Convert tooltip size to max-width value
sizeToMaxWidth :: TooltipSize -> Maybe Int
sizeToMaxWidth = case _ of
  SizeAuto -> Nothing
  SizeSmall -> Just 280
  SizeMedium -> Just 360
  SizeLarge -> Just 480
  SizeFullWidth -> Nothing
  SizeCustom w -> Just w

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // content align
-- ═════════════════════════════════════════════════════════════════════════════

-- | How content is aligned within tooltip.
data ContentAlign
  = AlignLeft     -- ^ Left-aligned text
  | AlignCenter   -- ^ Center-aligned text
  | AlignRight    -- ^ Right-aligned text

derive instance eqContentAlign :: Eq ContentAlign
derive instance ordContentAlign :: Ord ContentAlign

instance showContentAlign :: Show ContentAlign where
  show AlignLeft = "left"
  show AlignCenter = "center"
  show AlignRight = "right"

instance boundedContentAlign :: Bounded ContentAlign where
  bottom = AlignLeft
  top = AlignRight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text content for a step.
type TextContent =
  { title :: String
  , subtitle :: Maybe String
  , description :: Maybe String
  }

-- | Create text content with title only
textContent :: String -> TextContent
textContent t =
  { title: t
  , subtitle: Nothing
  , description: Nothing
  }

-- | Add subtitle to text content
withSubtitle :: String -> TextContent -> TextContent
withSubtitle s c = c { subtitle = Just s }

-- | Add description to text content
withDescription :: String -> TextContent -> TextContent
withDescription d c = c { description = Just d }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // media content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Media content for a step.
type MediaContent =
  { kind :: MediaType
  , src :: String
  , alt :: String
  , width :: Maybe Int
  , height :: Maybe Int
  , autoplay :: Boolean
  , loop :: Boolean
  , muted :: Boolean
  }

-- | Create image content
imageContent :: String -> String -> MediaContent
imageContent src alt =
  { kind: MediaImage
  , src: src
  , alt: alt
  , width: Nothing
  , height: Nothing
  , autoplay: false
  , loop: false
  , muted: true
  }

-- | Create video content
videoContent :: String -> String -> MediaContent
videoContent src alt =
  { kind: MediaVideo
  , src: src
  , alt: alt
  , width: Nothing
  , height: Nothing
  , autoplay: true
  , loop: true
  , muted: true
  }

-- | Create GIF content
gifContent :: String -> String -> MediaContent
gifContent src alt =
  { kind: MediaGif
  , src: src
  , alt: alt
  , width: Nothing
  , height: Nothing
  , autoplay: true
  , loop: true
  , muted: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // checklist item
-- ═════════════════════════════════════════════════════════════════════════════

-- | Checklist item in a checklist content step.
type ChecklistItem =
  { id :: String
  , label :: String
  , description :: Maybe String
  , required :: Boolean
  , completed :: Boolean
  }

-- | Create a checklist item
checklistItem :: String -> String -> ChecklistItem
checklistItem itemId label =
  { id: itemId
  , label: label
  , description: Nothing
  , required: false
  , completed: false
  }

-- | Create a required checklist item
requiredItem :: String -> String -> ChecklistItem
requiredItem itemId label =
  (checklistItem itemId label) { required = true }

-- | Create an optional checklist item
optionalItem :: String -> String -> ChecklistItem
optionalItem = checklistItem

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // content config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete content configuration for a step.
type ContentConfig =
  { kind :: ContentKind
  , text :: TextContent
  , media :: Maybe MediaContent
  , interaction :: Maybe InteractiveKind
  , checklist :: Array ChecklistItem
  , size :: TooltipSize
  , align :: ContentAlign
  , showArrow :: Boolean
  , className :: String
  }

-- | Default text content configuration
defaultContentConfig :: String -> ContentConfig
defaultContentConfig title =
  { kind: ContentText
  , text: textContent title
  , media: Nothing
  , interaction: Nothing
  , checklist: []
  , size: SizeMedium
  , align: AlignLeft
  , showArrow: true
  , className: ""
  }

-- | Media content configuration
mediaContentConfig :: String -> MediaContent -> ContentConfig
mediaContentConfig title m = (defaultContentConfig title)
  { kind = ContentMedia
  , media = Just m
  , size = SizeLarge
  }

-- | Interactive content configuration
interactiveContentConfig :: String -> InteractiveKind -> ContentConfig
interactiveContentConfig title interaction = (defaultContentConfig title)
  { kind = ContentInteractive
  , interaction = Just interaction
  }
