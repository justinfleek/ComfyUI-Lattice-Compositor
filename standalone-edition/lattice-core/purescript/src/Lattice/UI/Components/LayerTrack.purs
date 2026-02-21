-- | LayerTrack Component
-- |
-- | Timeline track for a single layer showing:
-- | - Layer info sidebar (visibility, lock, name, type)
-- | - Duration bar with trim handles
-- | - Keyframe diamonds
module Lattice.UI.Components.LayerTrack
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  ) where

import Prelude

import Data.Array (filter, length)
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Keyframe representation
type KeyframeInfo =
  { id :: String
  , frame :: Int
  , propertyName :: String
  }

-- | Layer data needed for timeline display
type LayerInfo =
  { id :: String
  , name :: String
  , layerType :: String
  , visible :: Boolean
  , locked :: Boolean
  , startFrame :: Int
  , endFrame :: Int
  , labelColor :: String
  , keyframes :: Array KeyframeInfo
  }

type Input =
  { layer :: LayerInfo
  , frameCount :: Int
  , pixelsPerFrame :: Number
  , isSelected :: Boolean
  , selectedKeyframeIds :: Array String
  }

data Output
  = SelectLayer String
  | UpdateLayer String LayerUpdate
  | SelectKeyframe String

-- | Layer update payload
type LayerUpdate =
  { visible :: Maybe Boolean
  , locked :: Maybe Boolean
  , startFrame :: Maybe Int
  , endFrame :: Maybe Int
  }

data Query a

type Slot id = H.Slot Query Output id

type State =
  { layer :: LayerInfo
  , frameCount :: Int
  , pixelsPerFrame :: Number
  , isSelected :: Boolean
  , selectedKeyframeIds :: Array String
  , isTrimming :: Maybe TrimMode
  }

data TrimMode = TrimIn | TrimOut

derive instance eqTrimMode :: Eq TrimMode

data Action
  = Receive Input
  | HandleSelectLayer
  | HandleToggleVisibility
  | HandleToggleLock
  | HandleSelectKeyframe String
  | StartTrimIn
  | StartTrimOut

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { layer: input.layer
  , frameCount: input.frameCount
  , pixelsPerFrame: input.pixelsPerFrame
  , isSelected: input.isSelected
  , selectedKeyframeIds: input.selectedKeyframeIds
  , isTrimming: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls $ [ "lattice-layer-track" ] 
          <> (if state.isSelected then [ "selected" ] else [])
          <> (if state.layer.locked then [ "locked" ] else [])
          <> (if not state.layer.visible then [ "hidden" ] else [])
    , HP.attr (HH.AttrName "style") layerTrackStyle
    , HE.onClick \_ -> HandleSelectLayer
    ]
    [ -- Layer info sidebar
      renderLayerInfo state
    
      -- Timeline track area
    , renderTrackArea state
    ]

renderLayerInfo :: forall m. State -> H.ComponentHTML Action () m
renderLayerInfo state =
  HH.div
    [ cls [ "lattice-layer-info" ]
    , HP.attr (HH.AttrName "style") layerInfoStyle
    ]
    [ -- Visibility toggle
      HH.button
        [ cls [ "lattice-icon-btn", "visibility-btn" ]
        , HP.attr (HH.AttrName "data-state") (if state.layer.visible then "active" else "inactive")
        , HP.title (if state.layer.visible then "Hide layer" else "Show layer")
        , HE.onClick \_ -> HandleToggleVisibility
        ]
        [ HH.text (if state.layer.visible then "👁" else "○") ]
    
      -- Lock toggle
    , HH.button
        [ cls [ "lattice-icon-btn", "lock-btn" ]
        , HP.attr (HH.AttrName "data-state") (if state.layer.locked then "active" else "inactive")
        , HP.title (if state.layer.locked then "Unlock layer" else "Lock layer")
        , HE.onClick \_ -> HandleToggleLock
        ]
        [ HH.text (if state.layer.locked then "🔒" else "🔓") ]
    
      -- Layer name
    , HH.span
        [ cls [ "lattice-layer-name-track" ]
        , HP.title state.layer.name
        , HP.attr (HH.AttrName "style") layerNameStyle
        ]
        [ HH.text state.layer.name ]
    
      -- Layer type badge
    , HH.span
        [ cls [ "lattice-layer-type-badge" ]
        , HP.attr (HH.AttrName "style") layerTypeBadgeStyle
        ]
        [ HH.text state.layer.layerType ]
    ]

renderTrackArea :: forall m. State -> H.ComponentHTML Action () m
renderTrackArea state =
  let
    -- Calculate duration bar position and width
    inPercent = Int.toNumber state.layer.startFrame / Int.toNumber state.frameCount * 100.0
    outPercent = (Int.toNumber state.layer.endFrame + 1.0) / Int.toNumber state.frameCount * 100.0
    widthPercent = outPercent - inPercent
    hasKeyframes = length state.layer.keyframes > 0
  in
  HH.div
    [ cls [ "lattice-track-area" ]
    , HP.attr (HH.AttrName "style") trackAreaStyle
    ]
    [ -- Duration bar
      HH.div
        [ cls $ [ "lattice-duration-bar" ] 
              <> (if hasKeyframes then [ "has-keyframes" ] else [])
        , HP.attr (HH.AttrName "style") (durationBarStyle inPercent widthPercent state.layer.labelColor)
        ]
        [ -- Trim in handle
          HH.div
            [ cls [ "lattice-trim-handle", "trim-in" ]
            , HP.attr (HH.AttrName "style") trimHandleInStyle
            , HE.onMouseDown \_ -> StartTrimIn
            ]
            []
        
          -- Trim out handle
        , HH.div
            [ cls [ "lattice-trim-handle", "trim-out" ]
            , HP.attr (HH.AttrName "style") trimHandleOutStyle
            , HE.onMouseDown \_ -> StartTrimOut
            ]
            []
        ]
    
      -- Keyframe diamonds
    , HH.div [ cls [ "lattice-keyframes-layer" ] ]
          (map (renderKeyframeDiamond state) state.layer.keyframes)
    ]

renderKeyframeDiamond :: forall m. State -> KeyframeInfo -> H.ComponentHTML Action () m
renderKeyframeDiamond state kf =
  let
    positionPercent = Int.toNumber kf.frame / Int.toNumber state.frameCount * 100.0
    isKeySelected = kf.id `elem` state.selectedKeyframeIds
  in
  HH.div
    [ cls $ [ "lattice-keyframe-diamond" ] 
          <> (if isKeySelected then [ "selected" ] else [])
    , HP.attr (HH.AttrName "style") (keyframeDiamondStyle positionPercent)
    , HP.title ("Frame " <> show kf.frame)
    , HE.onClick \_ -> HandleSelectKeyframe kf.id
    ]
    []

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

elem :: forall a. Eq a => a -> Array a -> Boolean
elem x arr = length (filter (_ == x) arr) > 0

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

layerTrackStyle :: String
layerTrackStyle =
  "display: flex; " <>
  "height: 28px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #333); " <>
  "background: var(--lattice-surface-2, #252525); " <>
  "transition: background 0.1s;"

layerInfoStyle :: String
layerInfoStyle =
  "width: 180px; " <>
  "min-width: 180px; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 4px; " <>
  "padding: 0 8px; " <>
  "border-right: 1px solid var(--lattice-border-subtle, #333); " <>
  "background: var(--lattice-surface-3, #2a2a2a);"

layerNameStyle :: String
layerNameStyle =
  "flex: 1; " <>
  "font-size: 13px; " <>
  "white-space: nowrap; " <>
  "overflow: hidden; " <>
  "text-overflow: ellipsis; " <>
  "color: var(--lattice-text-primary, #e0e0e0);"

layerTypeBadgeStyle :: String
layerTypeBadgeStyle =
  "font-size: 11px; " <>
  "color: var(--lattice-text-muted, #666); " <>
  "text-transform: uppercase; " <>
  "padding: 2px 4px; " <>
  "background: var(--lattice-surface-4, #333); " <>
  "border-radius: 2px;"

trackAreaStyle :: String
trackAreaStyle =
  "flex: 1; " <>
  "position: relative; " <>
  "min-width: 0;"

durationBarStyle :: Number -> Number -> String -> String
durationBarStyle leftPct widthPct labelColor =
  "position: absolute; " <>
  "top: 4px; " <>
  "bottom: 4px; " <>
  "left: " <> show leftPct <> "%; " <>
  "width: " <> show widthPct <> "%; " <>
  "background: " <> labelColor <> "; " <>
  "border-radius: 3px; " <>
  "opacity: 0.7; " <>
  "transition: opacity 0.1s; " <>
  "cursor: move;"

trimHandleInStyle :: String
trimHandleInStyle =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "left: 0; " <>
  "width: 6px; " <>
  "cursor: ew-resize; " <>
  "background: transparent; " <>
  "border-radius: 3px 0 0 3px;"

trimHandleOutStyle :: String
trimHandleOutStyle =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "right: 0; " <>
  "width: 6px; " <>
  "cursor: ew-resize; " <>
  "background: transparent; " <>
  "border-radius: 0 3px 3px 0;"

keyframeDiamondStyle :: Number -> String
keyframeDiamondStyle leftPct =
  "position: absolute; " <>
  "top: 50%; " <>
  "left: " <> show leftPct <> "%; " <>
  "width: 8px; " <>
  "height: 8px; " <>
  "background: var(--lattice-warning, #ffc107); " <>
  "transform: translate(-50%, -50%) rotate(45deg); " <>
  "cursor: pointer; " <>
  "z-index: 2; " <>
  "transition: transform 0.1s, background 0.1s;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ _
      { layer = input.layer
      , frameCount = input.frameCount
      , pixelsPerFrame = input.pixelsPerFrame
      , isSelected = input.isSelected
      , selectedKeyframeIds = input.selectedKeyframeIds
      }
  
  HandleSelectLayer -> do
    state <- H.get
    H.raise (SelectLayer state.layer.id)
  
  HandleToggleVisibility -> do
    state <- H.get
    H.raise (UpdateLayer state.layer.id 
      { visible: Just (not state.layer.visible)
      , locked: Nothing
      , startFrame: Nothing
      , endFrame: Nothing
      })
  
  HandleToggleLock -> do
    state <- H.get
    H.raise (UpdateLayer state.layer.id
      { visible: Nothing
      , locked: Just (not state.layer.locked)
      , startFrame: Nothing
      , endFrame: Nothing
      })
  
  HandleSelectKeyframe kfId -> do
    H.raise (SelectKeyframe kfId)
  
  StartTrimIn -> do
    H.modify_ _ { isTrimming = Just TrimIn }
    -- Note: Actual trim handling would be at parent level
  
  StartTrimOut -> do
    H.modify_ _ { isTrimming = Just TrimOut }
    -- Note: Actual trim handling would be at parent level
