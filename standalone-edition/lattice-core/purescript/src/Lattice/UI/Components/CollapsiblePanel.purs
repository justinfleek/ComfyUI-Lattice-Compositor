-- | Collapsible Panel Component
-- |
-- | A reusable collapsible/expandable panel with header and content sections.
-- | Supports animation, custom icons, and keyboard accessibility.
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/CollapsiblePanel.vue
module Lattice.UI.Components.CollapsiblePanel
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , CollapsibleConfig
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Web.UIEvent.KeyboardEvent as KE

import Lattice.UI.Core (cls)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type CollapsibleConfig =
  { title :: String
  , icon :: Maybe String
  , defaultExpanded :: Boolean
  , showBadge :: Maybe String
  , disabled :: Boolean
  }

type Input =
  { config :: CollapsibleConfig
  , content :: forall w i. Array (HH.HTML w i)
  }

data Output
  = Expanded
  | Collapsed

data Query a
  = SetExpanded Boolean a
  | Toggle a
  | GetExpanded (Boolean -> a)

type Slot id = H.Slot Query Output id

type State =
  { config :: CollapsibleConfig
  , isExpanded :: Boolean
  , instanceId :: String  -- Unique ID for ARIA associations
  }

data Action
  = Initialize
  | Receive Input
  | ToggleExpand
  | HandleKeyDown KE.KeyboardEvent

type Slots = ()

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { config: input.config
  , isExpanded: input.config.defaultExpanded
  , instanceId: "collapsible-" <> sanitizeTitle input.config.title
  }

-- | Convert title to a valid DOM ID
sanitizeTitle :: String -> String
sanitizeTitle = map \c -> if c == ' ' then '-' else c

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-collapsible" ]
    , HP.attr (HH.AttrName "style") collapsibleStyle
    , HP.attr (HH.AttrName "data-state") (if state.isExpanded then "open" else "closed")
    ]
    [ renderHeader state
    , renderContent state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  let
    headerId = state.instanceId <> "-header"
    contentId = state.instanceId <> "-content"
  in
  HH.div
    [ cls [ "lattice-collapsible-header" ]
    , HP.id headerId
    , HP.attr (HH.AttrName "style") (headerStyle state.config.disabled)
    , HP.attr (HH.AttrName "role") "button"
    , HP.tabIndex 0
    , ARIA.expanded (show state.isExpanded)
    , ARIA.controls contentId
    , ARIA.disabled (show state.config.disabled)
    , HP.attr (HH.AttrName "data-state") (if state.isExpanded then "open" else "closed")
    , HP.attr (HH.AttrName "data-disabled") (if state.config.disabled then "true" else "false")
    , HE.onClick \_ -> ToggleExpand
    , HE.onKeyDown HandleKeyDown
    ]
    [ -- Expand/collapse icon
      HH.span 
        [ cls [ "lattice-collapsible-chevron" ]
        , HP.attr (HH.AttrName "style") chevronStyle
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ] 
        [ HH.text (if state.isExpanded then "▼" else "►") ]
    
      -- Optional custom icon
    , case state.config.icon of
        Just iconText ->
          HH.span 
            [ cls [ "lattice-collapsible-icon" ]
            , HP.attr (HH.AttrName "style") iconStyle
            , HP.attr (HH.AttrName "aria-hidden") "true"
            ] 
            [ HH.text iconText ]
        Nothing -> HH.text ""
    
      -- Title
    , HH.span 
        [ cls [ "lattice-collapsible-title" ]
        , HP.attr (HH.AttrName "style") titleStyle
        ] 
        [ HH.text state.config.title ]
    
      -- Optional badge
    , case state.config.showBadge of
        Just badge ->
          HH.span 
            [ cls [ "lattice-collapsible-badge" ]
            , HP.attr (HH.AttrName "style") badgeStyle
            ] 
            [ HH.text badge ]
        Nothing -> HH.text ""
    ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  let
    headerId = state.instanceId <> "-header"
    contentId = state.instanceId <> "-content"
  in
  if state.isExpanded
    then
      HH.div
        [ cls [ "lattice-collapsible-content" ]
        , HP.attr (HH.AttrName "style") contentStyle
        , HP.id contentId
        , HP.attr (HH.AttrName "role") "region"
        , ARIA.labelledBy headerId
        , HP.attr (HH.AttrName "data-state") "open"
        ]
        [ HH.div [ cls [ "lattice-collapsible-inner" ], HP.attr (HH.AttrName "style") innerStyle ]
            [ -- Content is passed via slot/children pattern
              -- In Halogen, we'd typically use child components or render props
              HH.text "Content goes here"
            ]
        ]
    else HH.text ""

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // styles
-- ════════════════════════════════════════════════════════════════════════════

collapsibleStyle :: String
collapsibleStyle =
  "background: var(--lattice-surface-1); " <>
  "border-radius: var(--lattice-radius-md); " <>
  "overflow: hidden; " <>
  "border: 1px solid var(--lattice-border-subtle);"

headerStyle :: Boolean -> String
headerStyle disabled =
  "display: flex; align-items: center; gap: 8px; " <>
  "padding: 10px 12px; " <>
  "background: var(--lattice-surface-2); " <>
  "cursor: " <> (if disabled then "not-allowed" else "pointer") <> "; " <>
  "user-select: none; " <>
  "transition: background 0.15s ease; " <>
  "opacity: " <> (if disabled then "0.5" else "1") <> ";"

chevronStyle :: String
chevronStyle =
  "font-size: 10px; " <>
  "color: var(--lattice-text-muted); " <>
  "width: 12px; " <>
  "transition: transform 0.2s ease;"

iconStyle :: String
iconStyle =
  "font-size: 14px; " <>
  "color: var(--lattice-accent);"

titleStyle :: String
titleStyle =
  "flex: 1; " <>
  "font-size: 13px; " <>
  "font-weight: 500; " <>
  "color: var(--lattice-text-primary);"

badgeStyle :: String
badgeStyle =
  "padding: 2px 6px; " <>
  "font-size: 10px; " <>
  "font-weight: 600; " <>
  "background: var(--lattice-accent-muted); " <>
  "color: var(--lattice-accent); " <>
  "border-radius: 10px;"

contentStyle :: String
contentStyle =
  "overflow: hidden; " <>
  "animation: slideDown 0.2s ease-out;"

innerStyle :: String
innerStyle =
  "padding: 12px;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ { config = input.config }
  
  ToggleExpand -> do
    state <- H.get
    if state.config.disabled
      then pure unit
      else do
        let newExpanded = not state.isExpanded
        H.modify_ _ { isExpanded = newExpanded }
        H.raise (if newExpanded then Expanded else Collapsed)
  
  HandleKeyDown ke ->
    let key = KE.key ke
    in case key of
      "Enter" -> handleAction ToggleExpand
      " " -> handleAction ToggleExpand  -- Space
      _ -> pure unit

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  SetExpanded expanded next -> do
    state <- H.get
    let wasExpanded = state.isExpanded
    H.modify_ _ { isExpanded = expanded }
    when (wasExpanded /= expanded) do
      H.raise (if expanded then Expanded else Collapsed)
    pure (Just next)
  
  Toggle next -> do
    handleAction ToggleExpand
    pure (Just next)
  
  GetExpanded reply -> do
    state <- H.get
    pure (Just (reply state.isExpanded))
