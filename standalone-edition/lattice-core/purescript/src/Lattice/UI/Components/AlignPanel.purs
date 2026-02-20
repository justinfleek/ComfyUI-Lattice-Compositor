-- | Align Panel Component
-- |
-- | Layer alignment and distribution tools for precise positioning.
-- | Supports:
-- | - Align to composition or selection bounds
-- | - Horizontal/vertical alignment (left, center, right, top, center, bottom)
-- | - Distribute layers horizontally or vertically
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/AlignPanel.vue
module Lattice.UI.Components.AlignPanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , AlignTarget(..)
  , AlignDirection(..)
  , DistributeDirection(..)
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

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { selectedLayerCount :: Int
  }

data Output
  = AlignLayers AlignTarget AlignDirection
  | DistributeLayers DistributeDirection
  | TargetChanged AlignTarget

data Query a

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // align // types
-- ════════════════════════════════════════════════════════════════════════════

data AlignTarget
  = TargetComposition
  | TargetSelection

derive instance eqAlignTarget :: Eq AlignTarget

instance showAlignTarget :: Show AlignTarget where
  show = case _ of
    TargetComposition -> "composition"
    TargetSelection -> "selection"

data AlignDirection
  = AlignLeft
  | AlignCenterH
  | AlignRight
  | AlignTop
  | AlignCenterV
  | AlignBottom

derive instance eqAlignDirection :: Eq AlignDirection

instance showAlignDirection :: Show AlignDirection where
  show = case _ of
    AlignLeft -> "left"
    AlignCenterH -> "centerH"
    AlignRight -> "right"
    AlignTop -> "top"
    AlignCenterV -> "centerV"
    AlignBottom -> "bottom"

alignTitle :: AlignDirection -> String
alignTitle = case _ of
  AlignLeft -> "Align Left Edges"
  AlignCenterH -> "Align Horizontal Centers"
  AlignRight -> "Align Right Edges"
  AlignTop -> "Align Top Edges"
  AlignCenterV -> "Align Vertical Centers"
  AlignBottom -> "Align Bottom Edges"

data DistributeDirection
  = DistributeHorizontal
  | DistributeVertical

derive instance eqDistributeDirection :: Eq DistributeDirection

instance showDistributeDirection :: Show DistributeDirection where
  show = case _ of
    DistributeHorizontal -> "horizontal"
    DistributeVertical -> "vertical"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { selectedLayerCount :: Int
  , alignTarget :: AlignTarget
  }

data Action
  = Initialize
  | Receive Input
  | SetAlignTarget AlignTarget
  | DoAlign AlignDirection
  | DoDistribute DistributeDirection

type Slots = ()

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

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
  { selectedLayerCount: input.selectedLayerCount
  , alignTarget: TargetComposition
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-align-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , ARIA.label "Alignment Tools"
    ]
    [ renderHeader
    , renderContent state
    ]

renderHeader :: forall m. H.ComponentHTML Action Slots m
renderHeader =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span 
        [ cls [ "panel-title" ]
        , HP.attr (HH.AttrName "style") titleStyle
        ] 
        [ HH.text "Align" ]
    ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "panel-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ renderTargetSection state
    , renderAlignSection state
    , renderDistributeSection state
    , renderSelectionInfo state
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // target // section
-- ════════════════════════════════════════════════════════════════════════════

renderTargetSection :: forall m. State -> H.ComponentHTML Action Slots m
renderTargetSection state =
  HH.div
    [ cls [ "control-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div 
        [ cls [ "section-header" ]
        , HP.attr (HH.AttrName "style") sectionHeaderStyle
        ]
        [ HH.span 
            [ cls [ "section-title" ]
            , HP.id "align-target-label"
            ] 
            [ HH.text "Align Layers To" ]
        ]
    , HH.div 
        [ cls [ "align-target-toggle" ]
        , HP.attr (HH.AttrName "style") targetToggleStyle
        , HP.attr (HH.AttrName "role") "group"
        , ARIA.labelledBy "align-target-label"
        ]
        [ targetButton "Composition" TargetComposition state
        , targetButton "Selection" TargetSelection state
        ]
    ]

targetButton :: forall m. String -> AlignTarget -> State -> H.ComponentHTML Action Slots m
targetButton labelText target state =
  let isActive = target == state.alignTarget
  in
  HH.button
    [ cls [ "target-btn" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") (targetBtnStyle isActive)
    , HP.attr (HH.AttrName "title") ("Align layers to " <> show target <> " bounds")
    , ARIA.pressed (show isActive)
    , HP.attr (HH.AttrName "data-state") (if isActive then "active" else "inactive")
    , HE.onClick \_ -> SetAlignTarget target
    ]
    [ HH.text labelText ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // align // section
-- ════════════════════════════════════════════════════════════════════════════

renderAlignSection :: forall m. State -> H.ComponentHTML Action Slots m
renderAlignSection state =
  HH.div
    [ cls [ "control-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.span [ cls [ "section-title" ] ] [ HH.text "Align" ] ]
    , HH.div 
        [ cls [ "align-buttons" ]
        , HP.attr (HH.AttrName "style") alignButtonsStyle
        , HP.attr (HH.AttrName "role") "group"
        , ARIA.label "Alignment options"
        ]
        [ -- Horizontal alignment
          alignButton AlignLeft state
        , alignButton AlignCenterH state
        , alignButton AlignRight state
        
        , HH.div [ cls [ "separator" ], HP.attr (HH.AttrName "style") separatorStyle ] []
        
          -- Vertical alignment
        , alignButton AlignTop state
        , alignButton AlignCenterV state
        , alignButton AlignBottom state
        ]
    ]

alignButton :: forall m. AlignDirection -> State -> H.ComponentHTML Action Slots m
alignButton direction state =
  let canAlign = state.selectedLayerCount >= 1
  in
  HH.button
    [ cls [ "align-btn" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") alignBtnStyle
    , HP.disabled (not canAlign)
    , HP.attr (HH.AttrName "title") (alignTitle direction)
    , ARIA.label (alignTitle direction)
    , HE.onClick \_ -> DoAlign direction
    ]
    [ renderAlignIcon direction ]

renderAlignIcon :: forall m. AlignDirection -> H.ComponentHTML Action Slots m
renderAlignIcon direction =
  HH.div 
    [ cls [ "align-icon" ]
    , HP.attr (HH.AttrName "style") alignIconStyle
    , HP.attr (HH.AttrName "aria-hidden") "true"
    ]
    [ HH.text (alignIconChar direction) ]

alignIconChar :: AlignDirection -> String
alignIconChar = case _ of
  AlignLeft -> "⫷"
  AlignCenterH -> "⫶"
  AlignRight -> "⫸"
  AlignTop -> "⤒"
  AlignCenterV -> "⫿"
  AlignBottom -> "⤓"

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // distribute // section
-- ════════════════════════════════════════════════════════════════════════════

renderDistributeSection :: forall m. State -> H.ComponentHTML Action Slots m
renderDistributeSection state =
  HH.div
    [ cls [ "control-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.span [ cls [ "section-title" ] ] [ HH.text "Distribute" ] ]
    , HH.div 
        [ cls [ "align-buttons" ]
        , HP.attr (HH.AttrName "style") alignButtonsStyle
        , HP.attr (HH.AttrName "role") "group"
        , ARIA.label "Distribution options"
        ]
        [ distributeButton "Horizontal" DistributeHorizontal state
        , distributeButton "Vertical" DistributeVertical state
        ]
    ]

distributeButton :: forall m. String -> DistributeDirection -> State -> H.ComponentHTML Action Slots m
distributeButton labelText direction state =
  let canDistribute = state.selectedLayerCount >= 3
  in
  HH.button
    [ cls [ "align-btn", "wide" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") distributeBtnStyle
    , HP.disabled (not canDistribute)
    , HP.attr (HH.AttrName "title") ("Distribute " <> labelText <> "ly")
    , ARIA.label ("Distribute " <> labelText <> "ly")
    , HE.onClick \_ -> DoDistribute direction
    ]
    [ HH.div 
        [ cls [ "distribute-icon" ]
        , HP.attr (HH.AttrName "style") distributeIconStyle
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ]
        [ HH.text (distributeIconChar direction) ]
    , HH.span_ [ HH.text labelText ]
    ]

distributeIconChar :: DistributeDirection -> String
distributeIconChar = case _ of
  DistributeHorizontal -> "⫾"
  DistributeVertical -> "⫽"

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // selection // info
-- ════════════════════════════════════════════════════════════════════════════

renderSelectionInfo :: forall m. State -> H.ComponentHTML Action Slots m
renderSelectionInfo state =
  HH.div
    [ cls [ "selection-info" ]
    , HP.attr (HH.AttrName "style") selectionInfoStyle
    , HP.attr (HH.AttrName "role") "status"
    , ARIA.live "polite"
    ]
    [ HH.text (selectionText state.selectedLayerCount) ]

selectionText :: Int -> String
selectionText count
  | count == 0 = "No layers selected"
  | count == 1 = "1 layer selected"
  | otherwise = show count <> " layers selected"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // styles
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary);"

headerStyle :: String
headerStyle =
  "padding: 8px 12px; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

titleStyle :: String
titleStyle =
  "font-weight: 600; font-size: 12px;"

contentStyle :: String
contentStyle =
  "flex: 1; padding: 12px; overflow-y: auto;"

sectionStyle :: String
sectionStyle =
  "margin-bottom: 16px;"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "margin-bottom: 8px; font-size: 11px; font-weight: 600; " <>
  "color: var(--lattice-text-muted); text-transform: uppercase; letter-spacing: 0.5px;"

targetToggleStyle :: String
targetToggleStyle =
  "display: flex; gap: 4px;"

targetBtnStyle :: Boolean -> String
targetBtnStyle active =
  "flex: 1; padding: 6px 12px; border-radius: 4px; cursor: pointer; " <>
  "font-size: 12px; transition: all 0.15s; " <>
  "border: 1px solid " <> (if active then "var(--lattice-accent)" else "var(--lattice-border-default)") <> "; " <>
  "background: " <> (if active then "var(--lattice-accent)" else "var(--lattice-surface-2)") <> "; " <>
  "color: " <> (if active then "white" else "var(--lattice-text-muted)") <> ";"

alignButtonsStyle :: String
alignButtonsStyle =
  "display: flex; gap: 4px; flex-wrap: wrap;"

alignBtnStyle :: String
alignBtnStyle =
  "display: flex; align-items: center; justify-content: center; gap: 4px; " <>
  "width: 36px; height: 36px; padding: 0; " <>
  "border: 1px solid var(--lattice-border-default); border-radius: 4px; " <>
  "background: var(--lattice-surface-2); color: var(--lattice-text-muted); " <>
  "cursor: pointer; transition: all 0.15s;"

alignIconStyle :: String
alignIconStyle =
  "font-size: 16px;"

separatorStyle :: String
separatorStyle =
  "width: 1px; height: 28px; background: var(--lattice-border-default); margin: 4px;"

distributeBtnStyle :: String
distributeBtnStyle =
  "display: flex; align-items: center; justify-content: center; gap: 4px; " <>
  "flex: 1; height: 36px; padding: 8px 12px; " <>
  "border: 1px solid var(--lattice-border-default); border-radius: 4px; " <>
  "background: var(--lattice-surface-2); color: var(--lattice-text-muted); " <>
  "cursor: pointer; transition: all 0.15s; font-size: 11px;"

distributeIconStyle :: String
distributeIconStyle =
  "font-size: 14px;"

selectionInfoStyle :: String
selectionInfoStyle =
  "margin-top: 16px; padding: 8px; background: var(--lattice-surface-2); " <>
  "border-radius: 4px; font-size: 11px; color: var(--lattice-text-muted); text-align: center;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ { selectedLayerCount = input.selectedLayerCount }
  
  SetAlignTarget target -> do
    H.modify_ _ { alignTarget = target }
    H.raise (TargetChanged target)
  
  DoAlign direction -> do
    state <- H.get
    when (state.selectedLayerCount >= 1) do
      H.raise (AlignLayers state.alignTarget direction)
  
  DoDistribute direction -> do
    state <- H.get
    when (state.selectedLayerCount >= 3) do
      H.raise (DistributeLayers direction)
