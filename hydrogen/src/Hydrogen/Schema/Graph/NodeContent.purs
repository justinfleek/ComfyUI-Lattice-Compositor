-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // graph // node-content
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Graph NodeContent — Content model for nodes in hierarchical visualizations.
-- |
-- | ## Design Philosophy
-- |
-- | Nodes can contain arbitrary content. This module defines the content model:
-- | - **Slots**: Named regions where content appears (leading, main, trailing, etc.)
-- | - **Templates**: Pre-built content configurations (text, card, avatar, etc.)
-- | - **Renderers**: Functions that produce Element from node data
-- |
-- | ## Slot Architecture
-- |
-- | ```
-- | ┌─────────────────────────────────────────────────────────┐
-- | │ [Leading]  [Icon]  [Main Content]  [Trailing] [Actions]│
-- | │                    [Subtitle]                          │
-- | │                    [Below Content / Details]           │
-- | └─────────────────────────────────────────────────────────┘
-- | ```
-- |
-- | ## Content Types
-- |
-- | - TextOnly: Simple label
-- | - IconText: Icon + label (file explorer)
-- | - TitleSubtitle: Two-line text
-- | - Card: Multi-field card (org chart)
-- | - Avatar: Image with name (people)
-- | - Metric: Value with label (dashboards)
-- | - Custom: Arbitrary Element
-- |
-- | ## Dependencies
-- |
-- | - Prelude

module Hydrogen.Schema.Graph.NodeContent
  ( -- * Content Slots
    ContentSlot(..)
  , isLeadingSlot
  , isMainSlot
  , isTrailingSlot
  , slotPriority
  
  -- * Content Templates
  , ContentTemplate(..)
  , isTextTemplate
  , isCardTemplate
  , isCustomTemplate
  
  -- * Slot Content
  , SlotContent(..)
  , textContent
  , iconContent
  , badgeContent
  , actionContent
  , progressContent
  , customContent
  
  -- * Text Content
  , TextContent
  , simpleText
  , richText
  , editableText
  
  -- * Badge Content
  , BadgeContent
  , badgeCount
  , badgeStatus
  , badgeDot
  
  -- * Action Content
  , ActionContent
  , buttonAction
  , iconAction
  , menuAction
  
  -- * Progress Content
  , ProgressContent
  , progressBar
  , progressCircle
  , progressSparkline
  
  -- * Card Fields
  , CardField(..)
  , titleField
  , subtitleField
  , metadataField
  , imageField
  , avatarField
  
  -- * Node Shape
  , NodeShape(..)
  , isRectangle
  , isCircle
  , isDiamond
  
  -- * Node State Visual
  , NodeStateVisual
  , nodeStateVisual
  , defaultStateVisual
  , withHoverStyle
  , withSelectedStyle
  , withFocusStyle
  , withDisabledStyle
  
  -- * Content Config (Compound)
  , ContentConfig
  , contentConfig
  , textOnlyContent
  , iconTextContent
  , cardContent
  , avatarContent
  , metricContent
  , customContentConfig
  
  -- * Slot Layout
  , SlotLayout
  , slotLayout
  , horizontalSlots
  , verticalSlots
  , gridSlots
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , Ordering
  , (<>)
  , (==)
  , (<=)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // content slots
-- ═════════════════════════════════════════════════════════════════════════════

-- | Named regions within a node where content appears
data ContentSlot
  = SlotLeading      -- ^ Before main content (expand icon, checkbox)
  | SlotIcon         -- ^ Node icon area
  | SlotMain         -- ^ Primary content area
  | SlotSubtitle     -- ^ Secondary text below main
  | SlotTrailing     -- ^ After main content (badges, status)
  | SlotActions      -- ^ Action buttons (show on hover)
  | SlotBelow        -- ^ Content below the main row
  | SlotOverlay      -- ^ Overlaid on top of node
  | SlotBackground   -- ^ Behind all content

derive instance eqContentSlot :: Eq ContentSlot
derive instance ordContentSlot :: Ord ContentSlot

instance showContentSlot :: Show ContentSlot where
  show SlotLeading = "leading"
  show SlotIcon = "icon"
  show SlotMain = "main"
  show SlotSubtitle = "subtitle"
  show SlotTrailing = "trailing"
  show SlotActions = "actions"
  show SlotBelow = "below"
  show SlotOverlay = "overlay"
  show SlotBackground = "background"

isLeadingSlot :: ContentSlot -> Boolean
isLeadingSlot SlotLeading = true
isLeadingSlot _ = false

isMainSlot :: ContentSlot -> Boolean
isMainSlot SlotMain = true
isMainSlot _ = false

isTrailingSlot :: ContentSlot -> Boolean
isTrailingSlot SlotTrailing = true
isTrailingSlot _ = false

-- | Slot render priority (lower = rendered first)
slotPriority :: ContentSlot -> Int
slotPriority SlotBackground = 0
slotPriority SlotLeading = 1
slotPriority SlotIcon = 2
slotPriority SlotMain = 3
slotPriority SlotSubtitle = 4
slotPriority SlotTrailing = 5
slotPriority SlotActions = 6
slotPriority SlotBelow = 7
slotPriority SlotOverlay = 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // content templates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pre-built content configurations
data ContentTemplate
  = TemplateTextOnly         -- ^ Simple text label
  | TemplateIconText         -- ^ Icon + text (file explorer)
  | TemplateTitleSubtitle    -- ^ Title + subtitle
  | TemplateCard             -- ^ Multi-field card
  | TemplateAvatar           -- ^ Avatar + name
  | TemplateMetric           -- ^ Value + label
  | TemplateProgress         -- ^ Progress indicator
  | TemplateThumbnail        -- ^ Image thumbnail
  | TemplateCustom           -- ^ Custom Element

derive instance eqContentTemplate :: Eq ContentTemplate

instance showContentTemplate :: Show ContentTemplate where
  show TemplateTextOnly = "text-only"
  show TemplateIconText = "icon-text"
  show TemplateTitleSubtitle = "title-subtitle"
  show TemplateCard = "card"
  show TemplateAvatar = "avatar"
  show TemplateMetric = "metric"
  show TemplateProgress = "progress"
  show TemplateThumbnail = "thumbnail"
  show TemplateCustom = "custom"

isTextTemplate :: ContentTemplate -> Boolean
isTextTemplate TemplateTextOnly = true
isTextTemplate TemplateTitleSubtitle = true
isTextTemplate _ = false

isCardTemplate :: ContentTemplate -> Boolean
isCardTemplate TemplateCard = true
isCardTemplate _ = false

isCustomTemplate :: ContentTemplate -> Boolean
isCustomTemplate TemplateCustom = true
isCustomTemplate _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // slot content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content type that can appear in a slot
data SlotContent
  = ContentText TextContent
  | ContentIcon String              -- ^ Icon identifier
  | ContentBadge BadgeContent
  | ContentAction ActionContent
  | ContentProgress ProgressContent
  | ContentImage String             -- ^ Image URL
  | ContentCustom String            -- ^ Custom Element key

derive instance eqSlotContent :: Eq SlotContent

instance showSlotContent :: Show SlotContent where
  show (ContentText _) = "text"
  show (ContentIcon _) = "icon"
  show (ContentBadge _) = "badge"
  show (ContentAction _) = "action"
  show (ContentProgress _) = "progress"
  show (ContentImage _) = "image"
  show (ContentCustom _) = "custom"

-- | Create text slot content
textContent :: String -> SlotContent
textContent s = ContentText (simpleText s)

-- | Create icon slot content
iconContent :: String -> SlotContent
iconContent = ContentIcon

-- | Create badge slot content
badgeContent :: Int -> SlotContent
badgeContent n = ContentBadge (badgeCount n)

-- | Create action slot content
actionContent :: String -> String -> SlotContent
actionContent id label = ContentAction (buttonAction id label)

-- | Create progress slot content
progressContent :: Number -> SlotContent
progressContent pct = ContentProgress (progressBar pct)

-- | Create custom slot content
customContent :: String -> SlotContent
customContent = ContentCustom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text content with formatting options
type TextContent =
  { text :: String
  , editable :: Boolean
  , truncate :: Boolean
  , maxLines :: Int
  , highlight :: Maybe String    -- ^ Highlight matching text
  , fontWeight :: Maybe String
  , fontSize :: Maybe String
  , color :: Maybe String
  }

-- | Simple text content
simpleText :: String -> TextContent
simpleText s =
  { text: s
  , editable: false
  , truncate: true
  , maxLines: 1
  , highlight: Nothing
  , fontWeight: Nothing
  , fontSize: Nothing
  , color: Nothing
  }

-- | Rich text with styling
richText :: String -> String -> String -> TextContent
richText s weight size = (simpleText s)
  { fontWeight = Just weight
  , fontSize = Just size
  }

-- | Editable text
editableText :: String -> TextContent
editableText s = (simpleText s) { editable = true }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // badge content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Badge/indicator content
type BadgeContent =
  { badgeType :: String          -- ^ "count" | "status" | "dot"
  , value :: Maybe Int
  , status :: Maybe String       -- ^ "success" | "warning" | "error" | "info"
  , label :: Maybe String
  , color :: Maybe String
  , maxCount :: Int              -- ^ Show "99+" if exceeded
  }

-- | Count badge
badgeCount :: Int -> BadgeContent
badgeCount n =
  { badgeType: "count"
  , value: Just n
  , status: Nothing
  , label: Nothing
  , color: Nothing
  , maxCount: 99
  }

-- | Status badge
badgeStatus :: String -> String -> BadgeContent
badgeStatus status label =
  { badgeType: "status"
  , value: Nothing
  , status: Just status
  , label: Just label
  , color: Nothing
  , maxCount: 99
  }

-- | Simple dot badge
badgeDot :: String -> BadgeContent
badgeDot color =
  { badgeType: "dot"
  , value: Nothing
  , status: Nothing
  , label: Nothing
  , color: Just color
  , maxCount: 99
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // action content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Action button/menu content
type ActionContent =
  { actionType :: String         -- ^ "button" | "icon" | "menu"
  , actionId :: String
  , label :: Maybe String
  , icon :: Maybe String
  , disabled :: Boolean
  , tooltip :: Maybe String
  }

-- | Button action
buttonAction :: String -> String -> ActionContent
buttonAction id label =
  { actionType: "button"
  , actionId: id
  , label: Just label
  , icon: Nothing
  , disabled: false
  , tooltip: Nothing
  }

-- | Icon-only action
iconAction :: String -> String -> ActionContent
iconAction id icon =
  { actionType: "icon"
  , actionId: id
  , label: Nothing
  , icon: Just icon
  , disabled: false
  , tooltip: Nothing
  }

-- | Menu action
menuAction :: String -> String -> ActionContent
menuAction id label =
  { actionType: "menu"
  , actionId: id
  , label: Just label
  , icon: Just "more"
  , disabled: false
  , tooltip: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // progress content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress indicator content
type ProgressContent =
  { progressType :: String       -- ^ "bar" | "circle" | "sparkline"
  , value :: Number              -- ^ 0-100 percentage
  , showLabel :: Boolean
  , color :: Maybe String
  , secondaryColor :: Maybe String
  , sparklineData :: Array Number  -- ^ For sparkline type
  }

-- | Progress bar
progressBar :: Number -> ProgressContent
progressBar pct =
  { progressType: "bar"
  , value: pct
  , showLabel: true
  , color: Nothing
  , secondaryColor: Nothing
  , sparklineData: []
  }

-- | Circular progress
progressCircle :: Number -> ProgressContent
progressCircle pct = (progressBar pct) { progressType = "circle" }

-- | Sparkline chart
progressSparkline :: Array Number -> ProgressContent
progressSparkline data_ =
  { progressType: "sparkline"
  , value: 0.0
  , showLabel: false
  , color: Nothing
  , secondaryColor: Nothing
  , sparklineData: data_
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // card fields
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fields for card-style nodes
data CardField
  = FieldTitle String
  | FieldSubtitle String
  | FieldMetadata String String     -- ^ label, value
  | FieldImage String               -- ^ URL
  | FieldAvatar String String       -- ^ URL, name
  | FieldBadge BadgeContent
  | FieldProgress ProgressContent
  | FieldDivider
  | FieldSpacer Number

derive instance eqCardField :: Eq CardField

instance showCardField :: Show CardField where
  show (FieldTitle _) = "title"
  show (FieldSubtitle _) = "subtitle"
  show (FieldMetadata _ _) = "metadata"
  show (FieldImage _) = "image"
  show (FieldAvatar _ _) = "avatar"
  show (FieldBadge _) = "badge"
  show (FieldProgress _) = "progress"
  show FieldDivider = "divider"
  show (FieldSpacer _) = "spacer"

titleField :: String -> CardField
titleField = FieldTitle

subtitleField :: String -> CardField
subtitleField = FieldSubtitle

metadataField :: String -> String -> CardField
metadataField = FieldMetadata

imageField :: String -> CardField
imageField = FieldImage

avatarField :: String -> String -> CardField
avatarField = FieldAvatar

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // node shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual shape of the node container
data NodeShape
  = ShapeRectangle         -- ^ Standard rectangle
  | ShapeRoundedRect       -- ^ Rounded corners
  | ShapePill              -- ^ Fully rounded ends
  | ShapeCircle            -- ^ Circle (for radial)
  | ShapeEllipse           -- ^ Ellipse
  | ShapeDiamond           -- ^ Rotated square
  | ShapeHexagon           -- ^ Six-sided
  | ShapeOctagon           -- ^ Eight-sided
  | ShapeParallelogram     -- ^ Skewed rectangle
  | ShapeCylinder          -- ^ Database-style
  | ShapeDocument          -- ^ Document shape
  | ShapeCloud             -- ^ Cloud shape
  | ShapeCustomPath String -- ^ Custom SVG path

derive instance eqNodeShape :: Eq NodeShape

instance showNodeShape :: Show NodeShape where
  show ShapeRectangle = "rectangle"
  show ShapeRoundedRect = "rounded-rect"
  show ShapePill = "pill"
  show ShapeCircle = "circle"
  show ShapeEllipse = "ellipse"
  show ShapeDiamond = "diamond"
  show ShapeHexagon = "hexagon"
  show ShapeOctagon = "octagon"
  show ShapeParallelogram = "parallelogram"
  show ShapeCylinder = "cylinder"
  show ShapeDocument = "document"
  show ShapeCloud = "cloud"
  show (ShapeCustomPath _) = "custom"

isRectangle :: NodeShape -> Boolean
isRectangle ShapeRectangle = true
isRectangle ShapeRoundedRect = true
isRectangle _ = false

isCircle :: NodeShape -> Boolean
isCircle ShapeCircle = true
isCircle ShapeEllipse = true
isCircle _ = false

isDiamond :: NodeShape -> Boolean
isDiamond ShapeDiamond = true
isDiamond _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // node state visual
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual styling for different node states
type NodeStateVisual =
  { defaultBg :: Maybe String
  , defaultBorder :: Maybe String
  , hoverBg :: Maybe String
  , hoverBorder :: Maybe String
  , selectedBg :: Maybe String
  , selectedBorder :: Maybe String
  , focusBorder :: Maybe String
  , focusRing :: Maybe String
  , disabledOpacity :: Number
  , pressedScale :: Number
  }

-- | Create node state visual
nodeStateVisual :: NodeStateVisual
nodeStateVisual =
  { defaultBg: Nothing
  , defaultBorder: Nothing
  , hoverBg: Nothing
  , hoverBorder: Nothing
  , selectedBg: Nothing
  , selectedBorder: Nothing
  , focusBorder: Nothing
  , focusRing: Nothing
  , disabledOpacity: 0.5
  , pressedScale: 0.98
  }

-- | Default state visual
defaultStateVisual :: NodeStateVisual
defaultStateVisual = nodeStateVisual

-- | Set hover styles
withHoverStyle :: String -> String -> NodeStateVisual -> NodeStateVisual
withHoverStyle bg border v = v { hoverBg = Just bg, hoverBorder = Just border }

-- | Set selected styles
withSelectedStyle :: String -> String -> NodeStateVisual -> NodeStateVisual
withSelectedStyle bg border v = v { selectedBg = Just bg, selectedBorder = Just border }

-- | Set focus styles
withFocusStyle :: String -> String -> NodeStateVisual -> NodeStateVisual
withFocusStyle border ring v = v { focusBorder = Just border, focusRing = Just ring }

-- | Set disabled opacity
withDisabledStyle :: Number -> NodeStateVisual -> NodeStateVisual
withDisabledStyle opacity v = v { disabledOpacity = opacity }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // content config compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete content configuration for nodes
type ContentConfig =
  { template :: ContentTemplate
  , shape :: NodeShape
  , slots :: Array { slot :: ContentSlot, content :: SlotContent }
  , fields :: Array CardField        -- ^ For card template
  , stateVisual :: NodeStateVisual
  , padding :: Number
  , minWidth :: Maybe Number
  , maxWidth :: Maybe Number
  , aspectRatio :: Maybe Number
  }

-- | Create content config
contentConfig :: ContentTemplate -> NodeShape -> ContentConfig
contentConfig template shape =
  { template
  , shape
  , slots: []
  , fields: []
  , stateVisual: defaultStateVisual
  , padding: 8.0
  , minWidth: Nothing
  , maxWidth: Nothing
  , aspectRatio: Nothing
  }

-- | Text-only node content
textOnlyContent :: ContentConfig
textOnlyContent = contentConfig TemplateTextOnly ShapeRectangle

-- | Icon + text content (file explorer style)
iconTextContent :: ContentConfig
iconTextContent = contentConfig TemplateIconText ShapeRectangle

-- | Card content (org chart style)
cardContent :: ContentConfig
cardContent = (contentConfig TemplateCard ShapeRoundedRect)
  { padding = 16.0
  , minWidth = Just 200.0
  }

-- | Avatar + name content (people)
avatarContent :: ContentConfig
avatarContent = (contentConfig TemplateAvatar ShapeRoundedRect)
  { padding = 12.0 }

-- | Metric content (dashboards)
metricContent :: ContentConfig
metricContent = contentConfig TemplateMetric ShapeRoundedRect

-- | Custom Element content
customContentConfig :: ContentConfig
customContentConfig = contentConfig TemplateCustom ShapeRectangle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // slot layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout for slots within a node
type SlotLayout =
  { direction :: String          -- ^ "horizontal" | "vertical" | "grid"
  , gap :: Number
  , alignItems :: String         -- ^ "start" | "center" | "end" | "stretch"
  , justifyContent :: String     -- ^ "start" | "center" | "end" | "space-between"
  , wrap :: Boolean
  , gridColumns :: Int
  }

-- | Create slot layout
slotLayout :: String -> Number -> SlotLayout
slotLayout direction gap =
  { direction
  , gap
  , alignItems: "center"
  , justifyContent: "start"
  , wrap: false
  , gridColumns: 2
  }

-- | Horizontal slot layout
horizontalSlots :: SlotLayout
horizontalSlots = slotLayout "horizontal" 8.0

-- | Vertical slot layout
verticalSlots :: SlotLayout
verticalSlots = slotLayout "vertical" 4.0

-- | Grid slot layout
gridSlots :: Int -> SlotLayout
gridSlots cols = (slotLayout "grid" 8.0) { gridColumns = cols }
