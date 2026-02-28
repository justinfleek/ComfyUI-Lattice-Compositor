-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // element // chat-bubble
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ChatBubble — Schema-native chat message component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | Every visual property maps directly to atoms from the 12 pillars:
-- |
-- | - **Color**: Background, text, glow
-- | - **Geometry**: Border radius
-- | - **Elevation**: Shadow, z-index
-- | - **Dimension**: Padding, max width
-- | - **Typography**: Font styling (via TypeStyle)
-- |
-- | The **BrandSchema** defines what these atoms are for a given brand.
-- | This component just renders them faithfully.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property        | Pillar     | Type                    | CSS Output              |
-- | |-----------------|------------|-------------------------|-------------------------|
-- | | backgroundColor | Color      | Color.RGB               | background-color        |
-- | | textColor       | Color      | Color.RGB               | color                   |
-- | | borderRadius    | Geometry   | Geometry.Corners        | border-radius           |
-- | | shadow          | Elevation  | Shadow.LayeredShadow    | box-shadow              |
-- | | glow            | Color      | Color.Glow              | filter: drop-shadow     |
-- | | padding         | Dimension  | Device.Pixel            | padding                 |
-- | | maxWidth        | Dimension  | Device.Pixel            | max-width               |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.ChatBubble as ChatBubble
-- | import Hydrogen.Schema.Color as Color
-- | import Hydrogen.Schema.Geometry as Geometry
-- | import Hydrogen.Schema.Elevation.Shadow as Shadow
-- |
-- | -- Minimal usage
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.message "Hello, world!"
-- |   , ChatBubble.direction ChatBubble.Sent
-- |   ]
-- |
-- | -- With brand atoms
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.message "Hello!"
-- |   , ChatBubble.direction ChatBubble.Sent
-- |   , ChatBubble.backgroundColor brand.primary
-- |   , ChatBubble.textColor brand.onPrimary
-- |   , ChatBubble.borderRadius brand.bubbleRadius
-- |   , ChatBubble.shadow brand.bubbleShadow
-- |   , ChatBubble.glow brand.accentGlow
-- |   ]
-- |
-- | -- With status and metadata
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.message "Did you see the update?"
-- |   , ChatBubble.direction ChatBubble.Sent
-- |   , ChatBubble.timestamp "10:42 AM"
-- |   , ChatBubble.status ChatBubble.Delivered
-- |   ]
-- |
-- | -- Received message with avatar
-- | ChatBubble.chatBubble
-- |   [ ChatBubble.message "I'm doing great, thanks!"
-- |   , ChatBubble.direction ChatBubble.Received
-- |   , ChatBubble.sender "Alice"
-- |   , ChatBubble.avatarUrl "https://..."
-- |   , ChatBubble.backgroundColor (Color.rgb 241 245 249)
-- |   , ChatBubble.textColor (Color.rgb 15 23 42)
-- |   ]
-- | ```
-- |
-- | ## Companion Components
-- |
-- | - `chatContainer` — Wrapper for a list of chat bubbles
-- | - `typingIndicator` — Animated typing dots
-- | - `dateDivider` — Date separator between messages

module Hydrogen.Element.Compound.ChatBubble
  ( -- * Main Component
    chatBubble
  
  -- * Companion Components
  , chatContainer
  , typingIndicator
  , dateDivider
  
  -- * Types
  , Direction(Sent, Received)
  , Status(Sending, SentStatus, Delivered, Read, Failed)
  
  -- * Props
  , ChatBubbleProps
  , ChatBubbleProp
  , defaultProps
  
  -- * Content Props
  , message
  , direction
  , sender
  , avatarUrl
  , timestamp
  , status
  
  -- * Color Atoms
  , backgroundColor
  , textColor
  , senderTextColor
  , timestampTextColor
  , glow
  
  -- * Geometry Atoms
  , borderRadius
  
  -- * Elevation Atoms
  , shadow
  
  -- * Dimension Atoms
  , padding
  , maxWidth
  , avatarSize
  , gap
  
  -- * Behavior Props
  , showTail
  , onClick
  
  -- * Escape Hatch
  , extraAttributes
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.Glow as Glow
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Elevation.Shadow as Shadow
import Hydrogen.Schema.Dimension.Device as Device

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Message direction
-- |
-- | Determines alignment and default styling:
-- | - `Sent`: Right-aligned, typically brand primary color
-- | - `Received`: Left-aligned, typically neutral/muted color
data Direction
  = Sent
  | Received

derive instance eqDirection :: Eq Direction

instance showDirection :: Show Direction where
  show Sent = "sent"
  show Received = "received"

-- | Message delivery status (for sent messages)
-- |
-- | Visual indicator of message state:
-- | - `Sending`: Clock icon, message in transit
-- | - `SentStatus`: Single check, reached server
-- | - `Delivered`: Double check, reached recipient device
-- | - `Read`: Double check (colored), recipient viewed
-- | - `Failed`: Error indicator, delivery failed
data Status
  = Sending
  | SentStatus
  | Delivered
  | Read
  | Failed

derive instance eqStatus :: Eq Status

instance showStatus :: Show Status where
  show Sending = "sending"
  show SentStatus = "sent"
  show Delivered = "delivered"
  show Read = "read"
  show Failed = "failed"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | ChatBubble properties
-- |
-- | All visual properties accept concrete Schema atoms.
-- | `Maybe` indicates optional — `Nothing` uses inherited/default styles.
type ChatBubbleProps msg =
  { -- Content
    message :: String
  , direction :: Direction
  , sender :: Maybe String
  , avatarUrl :: Maybe String
  , timestamp :: Maybe String
  , status :: Maybe Status
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , senderTextColor :: Maybe Color.RGB
  , timestampTextColor :: Maybe Color.RGB
  , glow :: Maybe Glow.Glow
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Elevation atoms
  , shadow :: Maybe Shadow.LayeredShadow
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , maxWidth :: Maybe Device.Pixel
  , avatarSize :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  
  -- Behavior
  , showTail :: Boolean
  , onClick :: Maybe msg
  
  -- Escape hatch
  , extraAttributes :: Array (E.Attribute msg)
  }

-- | Property modifier
type ChatBubbleProp msg = ChatBubbleProps msg -> ChatBubbleProps msg

-- | Default properties
-- |
-- | Visual atoms default to `Nothing` (inherit from context/brand).
-- | This ensures the component works with any BrandSchema.
defaultProps :: forall msg. ChatBubbleProps msg
defaultProps =
  { message: ""
  , direction: Received
  , sender: Nothing
  , avatarUrl: Nothing
  , timestamp: Nothing
  , status: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , senderTextColor: Nothing
  , timestampTextColor: Nothing
  , glow: Nothing
  , borderRadius: Nothing
  , shadow: Nothing
  , padding: Nothing
  , maxWidth: Nothing
  , avatarSize: Nothing
  , gap: Nothing
  , showTail: true
  , onClick: Nothing
  , extraAttributes: []
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // prop builders: content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set message text
message :: forall msg. String -> ChatBubbleProp msg
message m props = props { message = m }

-- | Set message direction (Sent or Received)
direction :: forall msg. Direction -> ChatBubbleProp msg
direction d props = props { direction = d }

-- | Set sender name (for received messages)
sender :: forall msg. String -> ChatBubbleProp msg
sender s props = props { sender = Just s }

-- | Set avatar URL
avatarUrl :: forall msg. String -> ChatBubbleProp msg
avatarUrl url props = props { avatarUrl = Just url }

-- | Set timestamp text
timestamp :: forall msg. String -> ChatBubbleProp msg
timestamp t props = props { timestamp = Just t }

-- | Set delivery status (for sent messages)
status :: forall msg. Status -> ChatBubbleProp msg
status s props = props { status = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set bubble background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> ChatBubbleProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set message text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> ChatBubbleProp msg
textColor c props = props { textColor = Just c }

-- | Set sender name text color (Color.RGB atom)
senderTextColor :: forall msg. Color.RGB -> ChatBubbleProp msg
senderTextColor c props = props { senderTextColor = Just c }

-- | Set timestamp text color (Color.RGB atom)
timestampTextColor :: forall msg. Color.RGB -> ChatBubbleProp msg
timestampTextColor c props = props { timestampTextColor = Just c }

-- | Set glow effect (Color.Glow atom)
-- |
-- | Renders as CSS `filter: drop-shadow(...)`.
glow :: forall msg. Glow.Glow -> ChatBubbleProp msg
glow g props = props { glow = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Corners atom)
-- |
-- | Supports per-corner radius for chat bubble tail effects.
borderRadius :: forall msg. Geometry.Corners -> ChatBubbleProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: elevation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set box shadow (Shadow.LayeredShadow atom)
-- |
-- | Supports multiple shadow layers for depth effects.
shadow :: forall msg. Shadow.LayeredShadow -> ChatBubbleProp msg
shadow s props = props { shadow = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set bubble padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> ChatBubbleProp msg
padding p props = props { padding = Just p }

-- | Set maximum bubble width (Device.Pixel atom)
maxWidth :: forall msg. Device.Pixel -> ChatBubbleProp msg
maxWidth w props = props { maxWidth = Just w }

-- | Set avatar size (Device.Pixel atom)
avatarSize :: forall msg. Device.Pixel -> ChatBubbleProp msg
avatarSize s props = props { avatarSize = Just s }

-- | Set gap between avatar and bubble (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> ChatBubbleProp msg
gap g props = props { gap = Just g }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Show bubble tail pointer
showTail :: forall msg. Boolean -> ChatBubbleProp msg
showTail t props = props { showTail = t }

-- | Set click handler
onClick :: forall msg. msg -> ChatBubbleProp msg
onClick handler props = props { onClick = Just handler }

-- | Add extra attributes (escape hatch)
extraAttributes :: forall msg. Array (E.Attribute msg) -> ChatBubbleProp msg
extraAttributes attrs props = props { extraAttributes = props.extraAttributes <> attrs }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a chat bubble
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
-- | All visual properties come from Schema atoms passed via props.
chatBubble :: forall msg. Array (ChatBubbleProp msg) -> E.Element msg
chatBubble propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    isSent = props.direction == Sent
  in
    E.div_
      (wrapperAttrs isSent props)
      (wrapperChildren isSent props)

-- | Wrapper attributes (alignment)
wrapperAttrs :: forall msg. Boolean -> ChatBubbleProps msg -> Array (E.Attribute msg)
wrapperAttrs isSent props =
  let
    alignStyle = if isSent then "flex-end" else "flex-start"
    gapStyle = maybe "8px" show props.gap
  in
    [ E.style "display" "flex"
    , E.style "justify-content" alignStyle
    , E.style "align-items" "flex-end"
    , E.style "gap" gapStyle
    , E.style "margin-bottom" "8px"
    ]

-- | Wrapper children (avatar + bubble column)
wrapperChildren :: forall msg. Boolean -> ChatBubbleProps msg -> Array (E.Element msg)
wrapperChildren isSent props =
  let
    avatarEl = renderAvatar props
    bubbleColumn = renderBubbleColumn isSent props
  in
    if isSent
      then [ bubbleColumn ]  -- No avatar for sent messages
      else case props.avatarUrl of
        Just _ -> [ avatarEl, bubbleColumn ]
        Nothing -> [ bubbleColumn ]

-- | Render avatar image
renderAvatar :: forall msg. ChatBubbleProps msg -> E.Element msg
renderAvatar props =
  let
    size = maybe "32px" show props.avatarSize
    url = maybe "" (\u -> u) props.avatarUrl
    altText = maybe "Avatar" (\s -> s) props.sender
  in
    E.img_
      [ E.src url
      , E.alt altText
      , E.style "width" size
      , E.style "height" size
      , E.style "border-radius" "50%"
      , E.style "object-fit" "cover"
      , E.style "flex-shrink" "0"
      ]

-- | Render bubble column (sender + bubble + metadata)
renderBubbleColumn :: forall msg. Boolean -> ChatBubbleProps msg -> E.Element msg
renderBubbleColumn isSent props =
  let
    alignItems = if isSent then "flex-end" else "flex-start"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "align-items" alignItems
      ]
      [ renderSenderName isSent props
      , renderBubble isSent props
      ]

-- | Render sender name (for received messages)
renderSenderName :: forall msg. Boolean -> ChatBubbleProps msg -> E.Element msg
renderSenderName isSent props =
  if isSent
    then E.empty
    else case props.sender of
      Nothing -> E.empty
      Just name ->
        let
          colorStyle = maybe "inherit" Color.toLegacyCss props.senderTextColor
        in
          E.span_
            [ E.style "font-size" "12px"
            , E.style "font-weight" "500"
            , E.style "color" colorStyle
            , E.style "margin-bottom" "4px"
            ]
            [ E.text name ]

-- | Render the bubble itself
renderBubble :: forall msg. Boolean -> ChatBubbleProps msg -> E.Element msg
renderBubble isSent props =
  let
    -- Build styles from atoms
    bubbleStyles = buildBubbleStyles isSent props
    
    -- Click handler
    clickAttr = case props.onClick of
      Just handler -> [ E.onClick handler, E.style "cursor" "pointer" ]
      Nothing -> []
    
    -- All attributes
    allAttrs = bubbleStyles <> clickAttr <> props.extraAttributes
  in
    E.div_
      allAttrs
      [ renderMessageText props
      , renderMetadata isSent props
      ]

-- | Build bubble style attributes from Schema atoms
buildBubbleStyles :: forall msg. Boolean -> ChatBubbleProps msg -> Array (E.Attribute msg)
buildBubbleStyles isSent props =
  let
    -- Default colors based on direction (fallbacks if no atom provided)
    defaultBgColor = if isSent 
      then Color.rgb 59 130 246  -- Blue for sent
      else Color.rgb 241 245 249  -- Light gray for received
    
    defaultTextColor = if isSent
      then Color.rgb 255 255 255  -- White for sent
      else Color.rgb 15 23 42     -- Dark for received
    
    -- Apply atoms or defaults
    bgColor = maybe defaultBgColor (\c -> c) props.backgroundColor
    txtColor = maybe defaultTextColor (\c -> c) props.textColor
    
    -- Border radius (default: 16px with tail adjustment)
    defaultRadius = if isSent
      then Geometry.corners 
             (Geometry.px 16.0) 
             (Geometry.px 16.0) 
             (Geometry.px 4.0)   -- Bottom-right smaller for tail
             (Geometry.px 16.0)
      else Geometry.corners 
             (Geometry.px 16.0) 
             (Geometry.px 16.0) 
             (Geometry.px 16.0) 
             (Geometry.px 4.0)   -- Bottom-left smaller for tail
    
    radiusValue = maybe defaultRadius (\r -> r) props.borderRadius
    
    -- Padding (default: 12px 16px)
    paddingValue = maybe "12px 16px" (\p -> show p) props.padding
    
    -- Max width (default: 75%)
    maxWidthValue = maybe "75%" (\w -> show w) props.maxWidth
    
    -- Core styles
    coreStyles =
      [ E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "color" (Color.toLegacyCss txtColor)
      , E.style "border-radius" (Geometry.cornersToLegacyCss radiusValue)
      , E.style "padding" paddingValue
      , E.style "max-width" maxWidthValue
      , E.style "word-wrap" "break-word"
      , E.style "position" "relative"
      ]
    
    -- Shadow (if provided)
    shadowStyle = case props.shadow of
      Nothing -> []
      Just s -> 
        if Shadow.isNoShadow s
          then []
          else [ E.style "box-shadow" (Shadow.layeredToLegacyCss s) ]
    
    -- Glow (if provided, and not "off")
    glowStyle = case props.glow of
      Nothing -> []
      Just g -> 
        if Glow.isOff g
          then []
          else [ E.style "filter" (Glow.glowToCss g) ]
    
    -- Transition for hover effects (always enabled for interactivity)
    transitionStyle =
      [ E.style "transition" "transform 0.15s ease-out, filter 0.15s ease-out, box-shadow 0.15s ease-out"
      ]
  in
    coreStyles <> shadowStyle <> glowStyle <> transitionStyle

-- | Render message text
renderMessageText :: forall msg. ChatBubbleProps msg -> E.Element msg
renderMessageText props =
  E.p_
    [ E.style "margin" "0"
    , E.style "white-space" "pre-wrap"
    ]
    [ E.text props.message ]

-- | Render metadata row (timestamp + status)
renderMetadata :: forall msg. Boolean -> ChatBubbleProps msg -> E.Element msg
renderMetadata isSent props =
  case props.timestamp of
    Nothing -> E.empty
    Just ts ->
      let
        colorStyle = maybe "inherit" Color.toLegacyCss props.timestampTextColor
        defaultOpacity = "0.7"
      in
        E.div_
          [ E.style "display" "flex"
          , E.style "align-items" "center"
          , E.style "justify-content" "flex-end"
          , E.style "gap" "4px"
          , E.style "margin-top" "4px"
          , E.style "font-size" "11px"
          , E.style "color" colorStyle
          , E.style "opacity" defaultOpacity
          ]
          [ E.span_ [] [ E.text ts ]
          , renderStatusIcon isSent props
          ]

-- | Render status icon (for sent messages)
renderStatusIcon :: forall msg. Boolean -> ChatBubbleProps msg -> E.Element msg
renderStatusIcon isSent props =
  if not isSent
    then E.empty
    else case props.status of
      Nothing -> E.empty
      Just st -> statusToIcon st

-- | Convert status to SVG icon
statusToIcon :: forall msg. Status -> E.Element msg
statusToIcon Sending = clockIcon
statusToIcon SentStatus = singleCheckIcon
statusToIcon Delivered = doubleCheckIcon
statusToIcon Read = doubleCheckReadIcon
statusToIcon Failed = errorIcon

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // companion components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container for chat messages
-- |
-- | Provides proper spacing and scroll behavior.
chatContainer :: forall msg. Array (E.Attribute msg) -> Array (E.Element msg) -> E.Element msg
chatContainer attrs children =
  E.div_
    ( [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "padding" "16px"
      , E.style "overflow-y" "auto"
      ] <> attrs
    )
    children

-- | Typing indicator (three animated dots)
-- |
-- | Shows when someone is typing.
typingIndicator :: forall msg. E.Element msg
typingIndicator =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    , E.style "padding" "12px 16px"
    , E.style "background-color" "rgb(241, 245, 249)"
    , E.style "border-radius" "16px"
    , E.style "width" "fit-content"
    ]
    [ typingDot "0s"
    , typingDot "0.15s"
    , typingDot "0.3s"
    ]

-- | Single typing dot with animation delay
typingDot :: forall msg. String -> E.Element msg
typingDot delay =
  E.span_
    [ E.style "width" "8px"
    , E.style "height" "8px"
    , E.style "border-radius" "50%"
    , E.style "background-color" "rgb(148, 163, 184)"
    , E.style "animation" "typing-bounce 1s ease-in-out infinite"
    , E.style "animation-delay" delay
    ]
    []

-- | Date divider between message groups
dateDivider :: forall msg. String -> E.Element msg
dateDivider dateText =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "16px"
    , E.style "margin" "16px 0"
    ]
    [ dividerLine
    , E.span_
        [ E.style "font-size" "12px"
        , E.style "color" "rgb(148, 163, 184)"
        , E.style "white-space" "nowrap"
        ]
        [ E.text dateText ]
    , dividerLine
    ]

-- | Divider line element
dividerLine :: forall msg. E.Element msg
dividerLine =
  E.div_
    [ E.style "flex" "1"
    , E.style "height" "1px"
    , E.style "background-color" "rgb(226, 232, 240)"
    ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clock icon (sending status)
clockIcon :: forall msg. E.Element msg
clockIcon =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.svgElement "circle"
        [ E.attr "cx" "12"
        , E.attr "cy" "12"
        , E.attr "r" "10"
        ]
        []
    , E.svgElement "polyline"
        [ E.attr "points" "12 6 12 12 16 14" ]
        []
    ]

-- | Single check icon (sent status)
singleCheckIcon :: forall msg. E.Element msg
singleCheckIcon =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.svgElement "polyline"
        [ E.attr "points" "20 6 9 17 4 12" ]
        []
    ]

-- | Double check icon (delivered status)
doubleCheckIcon :: forall msg. E.Element msg
doubleCheckIcon =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    ]
    [ E.svgElement "path"
        [ E.attr "d" "M18 6L7 17l-4-4" ]
        []
    , E.svgElement "path"
        [ E.attr "d" "M22 10L11 21" ]
        []
    ]

-- | Double check icon in blue (read status)
doubleCheckReadIcon :: forall msg. E.Element msg
doubleCheckReadIcon =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "rgb(59, 130, 246)"
    , E.attr "stroke-width" "2"
    ]
    [ E.svgElement "path"
        [ E.attr "d" "M18 6L7 17l-4-4" ]
        []
    , E.svgElement "path"
        [ E.attr "d" "M22 10L11 21" ]
        []
    ]

-- | Error icon (failed status)
errorIcon :: forall msg. E.Element msg
errorIcon =
  E.svg_
    [ E.attr "width" "12"
    , E.attr "height" "12"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "rgb(239, 68, 68)"
    , E.attr "stroke-width" "2"
    ]
    [ E.svgElement "circle"
        [ E.attr "cx" "12"
        , E.attr "cy" "12"
        , E.attr "r" "10"
        ]
        []
    , E.svgElement "line"
        [ E.attr "x1" "15"
        , E.attr "y1" "9"
        , E.attr "x2" "9"
        , E.attr "y2" "15"
        ]
        []
    , E.svgElement "line"
        [ E.attr "x1" "9"
        , E.attr "y1" "9"
        , E.attr "x2" "15"
        , E.attr "y2" "15"
        ]
        []
    ]
