-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                             PropertyLink.purs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | PropertyLink Component
-- |
-- | A drag-to-link property connector, supporting:
-- | - Drag from one property to another to create expression links
-- | - Visual feedback during drag (dashed line)
-- | - Drop target highlighting
-- | - Clear link button when linked
module Lattice.UI.Components.PropertyLink
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , PropertyPath
  , LinkTarget
  ) where

import Prelude

import Data.Int as Int
import Data.Maybe (Maybe(..), isJust)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Lattice.UI.Core (cls)
import Web.UIEvent.MouseEvent (MouseEvent)
import Web.UIEvent.MouseEvent as ME

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Property path like "transform.position.x" or "opacity"
type PropertyPath = String

-- | Link target identifying layer and property
type LinkTarget =
  { layerId :: String
  , property :: PropertyPath
  }

type Input =
  { layerId :: String
  , property :: PropertyPath
  , linkedTo :: Maybe LinkTarget
  }

data Output
  = LinkCreated LinkTarget
  | LinkCleared

data Query a

type Slot id = H.Slot Query Output id

type State =
  { layerId :: String
  , property :: PropertyPath
  , linkedTo :: Maybe LinkTarget
  , isDragging :: Boolean
  , dragStartX :: Number
  , dragStartY :: Number
  , dragEndX :: Number
  , dragEndY :: Number
  }

data Action
  = Initialize
  | Receive Input
  | StartDrag MouseEvent
  | ClearLink

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
  { layerId: input.layerId
  , property: input.property
  , linkedTo: input.linkedTo
  , isDragging: false
  , dragStartX: 0.0
  , dragStartY: 0.0
  , dragEndX: 0.0
  , dragEndY: 0.0
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-property-link-container" ]
    , HP.attr (HH.AttrName "style") containerStyle
    ]
    [ -- Link handle (drag source)
      HH.div
        [ cls [ "lattice-link-handle" ]
        , HP.attr (HH.AttrName "data-state") (linkHandleState state)
        , HP.attr (HH.AttrName "style") (handleStyle state)
        , HP.title (handleTitle state)
        , HE.onMouseDown StartDrag
        ]
        [ -- SVG icon
          HH.element (HH.ElemName "svg")
            [ HP.attr (HH.AttrName "viewBox") "0 0 16 16"
            , cls [ "lattice-link-icon" ]
            , HP.attr (HH.AttrName "style") iconStyle
            ]
            [ -- Center circle
              HH.element (HH.ElemName "circle")
                [ HP.attr (HH.AttrName "cx") "8"
                , HP.attr (HH.AttrName "cy") "8"
                , HP.attr (HH.AttrName "r") "3"
                , HP.attr (HH.AttrName "fill") "currentColor"
                ]
                []
              -- Rays (when not linked)
            , case state.linkedTo of
                Nothing ->
                  HH.element (HH.ElemName "path")
                    [ HP.attr (HH.AttrName "d") "M8 5 L8 2 M8 11 L8 14 M5 8 L2 8 M11 8 L14 8"
                    , HP.attr (HH.AttrName "stroke") "currentColor"
                    , HP.attr (HH.AttrName "stroke-width") "1.5"
                    , HP.attr (HH.AttrName "fill") "none"
                    ]
                    []
                Just _ ->
                  -- Arrow rays (when linked)
                  HH.element (HH.ElemName "path")
                    [ HP.attr (HH.AttrName "d") "M11 5 L14 2 M11 11 L14 14"
                    , HP.attr (HH.AttrName "stroke") "currentColor"
                    , HP.attr (HH.AttrName "stroke-width") "1.5"
                    , HP.attr (HH.AttrName "fill") "none"
                    ]
                    []
            ]
        ]
    
      -- Clear link button (shown when linked)
    , case state.linkedTo of
        Just _ ->
          HH.button
            [ cls [ "lattice-clear-link-btn" ]
            , HP.attr (HH.AttrName "style") clearBtnStyle
            , HP.title "Remove link"
            , HE.onClick (const ClearLink)
            ]
            [ HH.text "×" ]
        Nothing -> HH.text ""
    
      -- Drag line visualization would need portal/overlay
      -- In full implementation, this would be rendered at document level
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

containerStyle :: String
containerStyle =
  "display: inline-flex; align-items: center; gap: 4px;"

linkHandleState :: State -> String
linkHandleState state
  | state.isDragging = "dragging"
  | isJust state.linkedTo = "linked"
  | otherwise = "idle"

handleStyle :: State -> String
handleStyle state =
  let baseColor = case state.linkedTo of
        Just _ -> "var(--lattice-success)"
        Nothing -> if state.isDragging 
          then "var(--lattice-accent)" 
          else "var(--lattice-text-muted)"
      scale = if state.isDragging then "scale(1.2)" else "scale(1)"
  in "width: 16px; height: 16px; cursor: crosshair; " <>
     "color: " <> baseColor <> "; " <>
     "transition: color 0.15s, transform 0.15s; " <>
     "user-select: none; transform: " <> scale <> ";"

handleTitle :: State -> String
handleTitle state = case state.linkedTo of
  Just target -> "Linked to: " <> target.layerId <> "." <> target.property
  Nothing -> "Drag to link property"

iconStyle :: String
iconStyle =
  "width: 100%; height: 100%;"

clearBtnStyle :: String
clearBtnStyle =
  "width: 14px; height: 14px; padding: 0; border: none; " <>
  "background: var(--lattice-error); color: white; border-radius: 50%; " <>
  "font-size: 12px; line-height: 1; cursor: pointer; " <>
  "display: flex; align-items: center; justify-content: center;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input ->
    H.modify_ _
      { layerId = input.layerId
      , property = input.property
      , linkedTo = input.linkedTo
      }

  StartDrag event -> do
    let x = toNumber (ME.clientX event)
    let y = toNumber (ME.clientY event)
    H.modify_ _ 
      { isDragging = true
      , dragStartX = x
      , dragStartY = y
      , dragEndX = x
      , dragEndY = y
      }
    -- Full implementation would:
    -- 1. Add global mousemove/mouseup listeners
    -- 2. Find all elements with data-link-target attribute
    -- 3. Render drag line overlay
    -- 4. Highlight valid drop targets
    -- 5. On drop, emit LinkCreated with target

  ClearLink -> do
    H.modify_ _ { linkedTo = Nothing }
    H.raise LinkCleared

toNumber :: Int -> Number
toNumber = Int.toNumber
