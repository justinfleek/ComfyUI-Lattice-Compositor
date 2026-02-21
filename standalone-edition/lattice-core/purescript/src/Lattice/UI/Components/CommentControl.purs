-- | Comment Control Component
-- |
-- | An expandable/collapsible comment section for template builders.
-- | Features:
-- | - Expand/collapse toggle
-- | - Auto-resizing textarea
-- | - Remove button with hover reveal
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/CommentControl.vue
module Lattice.UI.Components.CommentControl
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , TemplateComment
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls)

-- =============================================================================
--                                                                      // types
-- =============================================================================

type TemplateComment =
  { id :: String
  , text :: String
  }

type Input = TemplateComment

data Output
  = CommentUpdated String String  -- commentId, newText
  | CommentRemoved

data Query a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { comment :: TemplateComment
  , isExpanded :: Boolean
  , localText :: String
  }

data Action
  = Initialize
  | Receive Input
  | ToggleExpand
  | UpdateLocalText String
  | CommitText
  | Remove

type Slots = ()

-- =============================================================================
--                                                                  // component
-- =============================================================================

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { comment: input
  , isExpanded: true
  , localText: input.text
  }

-- =============================================================================
--                                                                     // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "comment-control" ]
    , HP.attr (HH.AttrName "style") (containerStyle state.isExpanded)
    ]
    [ renderHeader state
    , if state.isExpanded
        then renderBody state
        else HH.text ""
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "comment-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    , HE.onClick \_ -> ToggleExpand
    , ARIA.role "button"
    , HP.attr (HH.AttrName "aria-expanded") (if state.isExpanded then "true" else "false")
    , HP.tabIndex 0
    ]
    [ -- Comment icon
      HH.div [ cls [ "comment-icon" ], HP.attr (HH.AttrName "style") iconStyle ]
        [ HH.text "\x{1F4AC}" ]  -- Speech bubble emoji
    
    -- Label
    , HH.span [ cls [ "comment-label" ], HP.attr (HH.AttrName "style") labelStyle ]
        [ HH.text "Comment" ]
    
    -- Expand/collapse button
    , HH.button
        [ cls [ "btn-icon-tiny", "expand-btn" ]
        , HP.attr (HH.AttrName "style") btnIconStyle
        , HP.title (if state.isExpanded then "Collapse" else "Expand")
        , ARIA.label (if state.isExpanded then "Collapse comment" else "Expand comment")
        ]
        [ HH.span 
            [ HP.attr (HH.AttrName "style") (chevronStyle state.isExpanded) ]
            [ HH.text "\x{25BC}" ]  -- Down chevron
        ]
    
    -- Remove button
    , HH.button
        [ cls [ "btn-icon-tiny", "remove-btn" ]
        , HP.attr (HH.AttrName "style") removeBtnStyle
        , HP.title "Remove comment"
        , ARIA.label "Remove comment"
        , HE.onClick \e -> Remove
        ]
        [ HH.text "\x{00D7}" ]  -- Multiplication sign (x)
    ]

renderBody :: forall m. State -> H.ComponentHTML Action Slots m
renderBody state =
  HH.div
    [ cls [ "comment-body" ]
    , HP.attr (HH.AttrName "style") bodyStyle
    ]
    [ HH.textarea
        [ cls [ "comment-textarea" ]
        , HP.attr (HH.AttrName "style") textareaStyle
        , HP.placeholder "Add a note for template users..."
        , HP.value state.localText
        , HE.onValueInput UpdateLocalText
        , HE.onBlur \_ -> CommitText
        , ARIA.label "Comment text"
        ]
    ]

-- =============================================================================
--                                                                     // styles
-- =============================================================================

containerStyle :: Boolean -> String
containerStyle isExpanded =
  "background: var(--lattice-surface-2, #1A1A1A); " <>
  "border-radius: 4px; overflow: hidden; " <>
  "border: 1px solid " <> 
    (if isExpanded 
       then "var(--lattice-accent-muted, rgba(139, 92, 246, 0.2))"
       else "var(--lattice-border-subtle, #2A2A2A)") <> ";"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; padding: 8px 10px; " <>
  "cursor: pointer; gap: 8px; user-select: none;"

iconStyle :: String
iconStyle =
  "color: var(--lattice-accent, #8B5CF6); " <>
  "display: flex; align-items: center; justify-content: center; " <>
  "opacity: 0.8; font-size: 14px;"

labelStyle :: String
labelStyle =
  "flex: 1; font-size: 12px; font-weight: 500; " <>
  "color: var(--lattice-text-secondary, #9CA3AF); " <>
  "text-transform: uppercase; letter-spacing: 0.5px;"

btnIconStyle :: String
btnIconStyle =
  "width: 18px; height: 18px; padding: 0; " <>
  "background: none; border: none; " <>
  "color: var(--lattice-text-muted, #6B7280); " <>
  "cursor: pointer; display: flex; align-items: center; justify-content: center; " <>
  "border-radius: 2px; transition: all 0.15s ease;"

chevronStyle :: Boolean -> String
chevronStyle isExpanded =
  "display: inline-block; font-size: 10px; " <>
  "transition: transform 0.2s ease; " <>
  "transform: rotate(" <> (if isExpanded then "0deg" else "-90deg") <> ");"

removeBtnStyle :: String
removeBtnStyle =
  "width: 18px; height: 18px; padding: 0; " <>
  "background: none; border: none; " <>
  "color: var(--lattice-text-muted, #6B7280); " <>
  "cursor: pointer; display: flex; align-items: center; justify-content: center; " <>
  "border-radius: 2px; font-size: 14px; " <>
  "opacity: 0; transition: opacity 0.15s ease;"

bodyStyle :: String
bodyStyle =
  "padding: 0 10px 10px;"

textareaStyle :: String
textareaStyle =
  "width: 100%; min-height: 60px; padding: 8px 10px; " <>
  "background: var(--lattice-surface-0, #0A0A0A); " <>
  "border: 1px solid var(--lattice-border-subtle, #2A2A2A); " <>
  "border-radius: 3px; color: var(--lattice-text-primary, #E5E5E5); " <>
  "font-size: 12px; line-height: 1.5; resize: vertical; " <>
  "font-family: inherit;"

-- =============================================================================
--                                                                    // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    state <- H.get
    -- Only update if external text changed
    when (input.text /= state.comment.text) do
      H.modify_ _ { comment = input, localText = input.text }
  
  ToggleExpand -> H.modify_ \s -> s { isExpanded = not s.isExpanded }
  
  UpdateLocalText text -> H.modify_ _ { localText = text }
  
  CommitText -> do
    state <- H.get
    when (state.localText /= state.comment.text) do
      H.raise (CommentUpdated state.comment.id state.localText)
  
  Remove -> H.raise CommentRemoved
