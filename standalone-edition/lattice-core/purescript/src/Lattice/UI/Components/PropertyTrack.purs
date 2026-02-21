-- | PropertyTrack Component
-- |
-- | Timeline track for an animated property showing:
-- | - Sidebar: property name, animation toggle, keyframe navigator, value inputs
-- | - Track: keyframe diamonds with interpolation types, box selection
-- | - Context menus for keyframe operations
module Lattice.UI.Components.PropertyTrack
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , PropertyInfo
  , KeyframeData
  , PropertyValue(..)
  , InterpolationType(..)
  ) where

import Prelude

import Data.Array (filter, length, mapWithIndex, sortBy)
import Data.Int as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Ord (comparing)
import Data.Set (Set)
import Data.Set as Set
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Property value sum type
data PropertyValue
  = NumberValue Number
  | VectorValue { x :: Number, y :: Number }
  | Vector3Value { x :: Number, y :: Number, z :: Number }
  | ColorValue String
  | BooleanValue Boolean
  | StringValue String
  | PercentValue Number

derive instance eqPropertyValue :: Eq PropertyValue

-- | Interpolation type
data InterpolationType
  = Linear
  | Bezier
  | Hold
  | Spring
  | Elastic
  | Bounce

derive instance eqInterpolationType :: Eq InterpolationType

-- | Keyframe data
type KeyframeData =
  { id :: String
  , frame :: Int
  , value :: PropertyValue
  , interpolation :: InterpolationType
  }

-- | Property info for display
type PropertyInfo =
  { name :: String
  , path :: String
  , value :: PropertyValue
  , animated :: Boolean
  , animatable :: Boolean
  , keyframes :: Array KeyframeData
  }

type Input =
  { layerId :: String
  , property :: PropertyInfo
  , layoutMode :: LayoutMode
  , pixelsPerFrame :: Number
  , currentFrame :: Int
  , frameCount :: Int
  }

data LayoutMode = SidebarMode | TrackMode

derive instance eqLayoutMode :: Eq LayoutMode

data Output
  = ToggleAnimation String String Boolean  -- layerId, propertyPath, animated
  | SetPropertyValue String String PropertyValue
  | AddKeyframe String String PropertyValue Int  -- layerId, path, value, frame
  | RemoveKeyframe String String String  -- layerId, path, keyframeId
  | MoveKeyframe String String String Int  -- layerId, path, keyframeId, newFrame
  | SetInterpolation String String String InterpolationType
  | SelectProperty String
  | GoToFrame Int

data Query a

type Slot id = H.Slot Query Output id

type State =
  { layerId :: String
  , property :: PropertyInfo
  , layoutMode :: LayoutMode
  , pixelsPerFrame :: Number
  , currentFrame :: Int
  , frameCount :: Int
  , selectedKeyframeIds :: Set String
  , isBoxSelecting :: Boolean
  , boxStartX :: Number
  , boxCurrentX :: Number
  , contextMenu :: Maybe ContextMenuState
  }

type ContextMenuState =
  { keyframeId :: String
  , x :: Number
  , y :: Number
  }

data Action
  = Receive Input
  | HandleToggleAnimation
  | HandleAddKeyframeAtCurrent
  | HandleGoToPrevKeyframe
  | HandleGoToNextKeyframe
  | HandleSelectKeyframe String Boolean  -- keyframeId, addToSelection
  | HandleDeleteKeyframe String
  | HandleShowContextMenu String Number Number
  | HandleHideContextMenu
  | HandleSetInterpolation InterpolationType
  | HandleGoToKeyframe
  | HandleClearAllKeyframes
  | HandleValueChange PropertyValue
  | HandleSelectProperty

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
  { layerId: input.layerId
  , property: input.property
  , layoutMode: input.layoutMode
  , pixelsPerFrame: input.pixelsPerFrame
  , currentFrame: input.currentFrame
  , frameCount: input.frameCount
  , selectedKeyframeIds: Set.empty
  , isBoxSelecting: false
  , boxStartX: 0.0
  , boxCurrentX: 0.0
  , contextMenu: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-prop-wrapper" ]
    , HP.attr (HH.AttrName "style") propWrapperStyle
    ]
    [ case state.layoutMode of
        SidebarMode -> renderSidebar state
        TrackMode -> renderTrack state
    ]

renderSidebar :: forall m. State -> H.ComponentHTML Action () m
renderSidebar state =
  let
    hasKeyframeAtCurrent = hasKeyframeAt state.currentFrame state.property.keyframes
  in
  HH.div
    [ cls [ "lattice-prop-sidebar" ]
    , HP.attr (HH.AttrName "style") propSidebarStyle
    , HE.onClick \_ -> HandleSelectProperty
    ]
    [ -- Indent spacer
      HH.div [ cls [ "lattice-indent-spacer" ] ] []
    
      -- Animation toggle (if animatable)
    , if state.property.animatable
        then HH.div
          [ cls [ "lattice-icon-box" ]
          , HP.attr (HH.AttrName "style") iconBoxStyle
          , HE.onClick \_ -> HandleToggleAnimation
          , HP.title "Toggle Animation"
          ]
          [ HH.span
              [ cls [ "lattice-keyframe-toggle" ]
              , HP.attr (HH.AttrName "data-state") (if state.property.animated then "active" else "inactive")
              ]
              [ HH.text "◆" ]
          ]
        else HH.div [ cls [ "lattice-icon-box", "disabled" ] ] []
    
      -- Keyframe navigator (if animated)
    , if state.property.animated
        then renderKeyframeNavigator state
        else HH.div
          [ cls [ "lattice-icon-box" ]
          , HP.attr (HH.AttrName "style") iconBoxStyle
          , HE.onClick \_ -> HandleAddKeyframeAtCurrent
          ]
          [ HH.span
              [ cls [ "lattice-kf-btn" ]
              , HP.attr (HH.AttrName "data-state") (if hasKeyframeAtCurrent then "active" else "inactive")
              ]
              [ HH.text "◇" ]
          ]
    
      -- Property content (name + inputs)
    , HH.div
        [ cls [ "lattice-prop-content" ]
        , HP.attr (HH.AttrName "style") propContentStyle
        ]
        [ HH.span [ cls [ "lattice-prop-name" ] ]
            [ HH.text state.property.name ]
        , renderPropertyInputs state
        ]
    ]

renderKeyframeNavigator :: forall m. State -> H.ComponentHTML Action () m
renderKeyframeNavigator state =
  let
    sortedKfs = sortBy (comparing _.frame) state.property.keyframes
    hasPrev = hasKeyframeBefore state.currentFrame sortedKfs
    hasNext = hasKeyframeAfter state.currentFrame sortedKfs
    hasAtCurrent = hasKeyframeAt state.currentFrame sortedKfs
  in
  HH.div
    [ cls [ "lattice-keyframe-nav" ]
    , HP.attr (HH.AttrName "style") keyframeNavStyle
    ]
    [ -- Previous keyframe button
      HH.button
        [ cls [ "lattice-nav-btn" ]
        , HP.attr (HH.AttrName "style") navBtnStyle
        , HP.disabled (not hasPrev)
        , HP.title "Previous Keyframe (J)"
        , HE.onClick \_ -> HandleGoToPrevKeyframe
        ]
        [ HH.text "◀" ]
    
      -- Add/remove keyframe indicator
    , HH.button
        [ cls [ "lattice-nav-btn", "kf-indicator" ]
        , HP.attr (HH.AttrName "style") navBtnStyle
        , HP.attr (HH.AttrName "data-state") (if hasAtCurrent then "active" else "inactive")
        , HP.title "Add/Remove Keyframe"
        , HE.onClick \_ -> HandleAddKeyframeAtCurrent
        ]
        [ HH.text "◆" ]
    
      -- Next keyframe button
    , HH.button
        [ cls [ "lattice-nav-btn" ]
        , HP.attr (HH.AttrName "style") navBtnStyle
        , HP.disabled (not hasNext)
        , HP.title "Next Keyframe (K)"
        , HE.onClick \_ -> HandleGoToNextKeyframe
        ]
        [ HH.text "▶" ]
    ]

renderPropertyInputs :: forall m. State -> H.ComponentHTML Action () m
renderPropertyInputs state =
  HH.div
    [ cls [ "lattice-prop-inputs" ]
    , HP.attr (HH.AttrName "style") propInputsStyle
    ]
    [ case state.property.value of
        NumberValue n ->
          renderNumberInput n
        
        VectorValue v ->
          HH.div [ cls [ "lattice-vec-inputs" ] ]
            [ renderVectorInput "X" v.x "x-label"
            , renderVectorInput "Y" v.y "y-label"
            ]
        
        Vector3Value v ->
          HH.div [ cls [ "lattice-vec-inputs" ] ]
            [ renderVectorInput "X" v.x "x-label"
            , renderVectorInput "Y" v.y "y-label"
            , renderVectorInput "Z" v.z "z-label"
            ]
        
        ColorValue c ->
          renderColorInput c
        
        BooleanValue b ->
          renderBooleanInput b
        
        StringValue s ->
          renderStringInput s
        
        PercentValue p ->
          renderPercentInput p
    ]

renderNumberInput :: forall m. Number -> H.ComponentHTML Action () m
renderNumberInput value =
  HH.input
    [ cls [ "lattice-number-input" ]
    , HP.attr (HH.AttrName "style") numberInputStyle
    , HP.type_ HP.InputNumber
    , HP.value (show value)
    ]

renderVectorInput :: forall m. String -> Number -> String -> H.ComponentHTML Action () m
renderVectorInput label value labelClass =
  HH.div
    [ cls [ "lattice-vec-item" ]
    , HP.attr (HH.AttrName "style") vecItemStyle
    ]
    [ HH.span
        [ cls [ "lattice-label", labelClass ]
        , HP.attr (HH.AttrName "style") (vecLabelStyle labelClass)
        ]
        [ HH.text label ]
    , HH.input
        [ cls [ "lattice-number-input" ]
        , HP.attr (HH.AttrName "style") numberInputStyle
        , HP.type_ HP.InputNumber
        , HP.value (show value)
        ]
    ]

renderColorInput :: forall m. String -> H.ComponentHTML Action () m
renderColorInput value =
  HH.div
    [ cls [ "lattice-color-input-wrapper" ]
    , HP.attr (HH.AttrName "style") colorInputWrapperStyle
    ]
    [ HH.input
        [ cls [ "lattice-color-input" ]
        , HP.type_ HP.InputColor
        , HP.value value
        ]
    , HH.span [ cls [ "lattice-color-hex" ] ]
        [ HH.text value ]
    ]

renderBooleanInput :: forall m. Boolean -> H.ComponentHTML Action () m
renderBooleanInput value =
  HH.div [ cls [ "lattice-checkbox-wrapper" ] ]
    [ HH.input
        [ cls [ "lattice-checkbox" ]
        , HP.type_ HP.InputCheckbox
        , HP.checked value
        ]
    ]

renderStringInput :: forall m. String -> H.ComponentHTML Action () m
renderStringInput value =
  HH.input
    [ cls [ "lattice-string-input" ]
    , HP.attr (HH.AttrName "style") stringInputStyle
    , HP.type_ HP.InputText
    , HP.value value
    ]

renderPercentInput :: forall m. Number -> H.ComponentHTML Action () m
renderPercentInput value =
  HH.div [ cls [ "lattice-percent-input" ] ]
    [ HH.input
        [ cls [ "lattice-number-input" ]
        , HP.attr (HH.AttrName "style") numberInputStyle
        , HP.type_ HP.InputNumber
        , HP.value (show value)
        ]
    , HH.span_ [ HH.text "%" ]
    ]

renderTrack :: forall m. State -> H.ComponentHTML Action () m
renderTrack state =
  HH.div
    [ cls [ "lattice-prop-track" ]
    , HP.attr (HH.AttrName "style") propTrackStyle
    ]
    ( -- Keyframe diamonds
      (map (renderKeyframeDiamond state) state.property.keyframes)
      <>
      -- Box selection overlay
      [ if state.isBoxSelecting
          then renderSelectionBox state
          else HH.text ""
      ]
      <>
      -- Context menu
      [ case state.contextMenu of
          Just ctx -> renderContextMenu state ctx
          Nothing -> HH.text ""
      ]
    )

renderKeyframeDiamond :: forall m. State -> KeyframeData -> H.ComponentHTML Action () m
renderKeyframeDiamond state kf =
  let
    leftPx = Int.toNumber kf.frame * state.pixelsPerFrame
    isSelected = Set.member kf.id state.selectedKeyframeIds
    interpClass = interpolationClass kf.interpolation
  in
  HH.div
    [ cls $ [ "lattice-keyframe", interpClass ] <> (if isSelected then [ "selected" ] else [])
    , HP.attr (HH.AttrName "style") (keyframeStyle leftPx)
    , HE.onClick \_ -> HandleSelectKeyframe kf.id false
    , HE.onDoubleClick \_ -> HandleDeleteKeyframe kf.id
    ]
    [ -- SVG keyframe shape
      HH.div
        [ cls [ "lattice-keyframe-shape" ]
        , HP.attr (HH.AttrName "style") keyframeShapeStyle
        ]
        [ HH.text (keyframeIcon kf.interpolation) ]
    ]

renderSelectionBox :: forall m. State -> H.ComponentHTML Action () m
renderSelectionBox state =
  let
    left = min state.boxStartX state.boxCurrentX
    width = abs (state.boxCurrentX - state.boxStartX)
  in
  HH.div
    [ cls [ "lattice-selection-box" ]
    , HP.attr (HH.AttrName "style") (selectionBoxStyle left width)
    ]
    []

renderContextMenu :: forall m. State -> ContextMenuState -> H.ComponentHTML Action () m
renderContextMenu state ctx =
  HH.div
    [ cls [ "lattice-keyframe-context-menu" ]
    , HP.attr (HH.AttrName "style") (contextMenuStyle ctx.x ctx.y)
    ]
    [ HH.div [ cls [ "lattice-menu-header" ] ]
        [ HH.text "Interpolation" ]
    
    , menuItem "📈 Linear" (HandleSetInterpolation Linear) (isInterpolation ctx.keyframeId Linear state)
    , menuItem "〰️ Bezier" (HandleSetInterpolation Bezier) (isInterpolation ctx.keyframeId Bezier state)
    , menuItem "⏸️ Hold" (HandleSetInterpolation Hold) (isInterpolation ctx.keyframeId Hold state)
    
    , HH.div [ cls [ "lattice-menu-divider" ] ] []
    
    , menuItem "➡️ Go to Frame" HandleGoToKeyframe false
    
    , HH.div [ cls [ "lattice-menu-divider" ] ] []
    
    , menuItem "✖️ Clear All Keyframes" HandleClearAllKeyframes false
    ]
  where
    menuItem :: String -> Action -> Boolean -> H.ComponentHTML Action () m
    menuItem label action active =
      HH.div
        [ cls $ [ "lattice-menu-item" ] <> (if active then [ "active" ] else [])
        , HP.attr (HH.AttrName "style") menuItemStyle
        , HE.onClick \_ -> action
        ]
        [ HH.text label ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

hasKeyframeAt :: Int -> Array KeyframeData -> Boolean
hasKeyframeAt frame kfs = length (filter (\kf -> kf.frame == frame) kfs) > 0

hasKeyframeBefore :: Int -> Array KeyframeData -> Boolean
hasKeyframeBefore frame kfs = length (filter (\kf -> kf.frame < frame) kfs) > 0

hasKeyframeAfter :: Int -> Array KeyframeData -> Boolean
hasKeyframeAfter frame kfs = length (filter (\kf -> kf.frame > frame) kfs) > 0

findPrevKeyframe :: Int -> Array KeyframeData -> Maybe KeyframeData
findPrevKeyframe frame kfs =
  let before = filter (\kf -> kf.frame < frame) (sortBy (comparing _.frame) kfs)
  in if length before > 0 
     then Just (unsafeLast before)
     else Nothing

findNextKeyframe :: Int -> Array KeyframeData -> Maybe KeyframeData  
findNextKeyframe frame kfs =
  let after = filter (\kf -> kf.frame > frame) (sortBy (comparing _.frame) kfs)
  in case after of
       [] -> Nothing
       arr -> Just (unsafeHead arr)

unsafeHead :: forall a. Array a -> a
unsafeHead arr = fromMaybe (unsafeHead arr) (headMaybe arr)
  where
    headMaybe :: Array a -> Maybe a
    headMaybe [] = Nothing
    headMaybe xs = Just (unsafeIndex xs 0)

unsafeLast :: forall a. Array a -> a
unsafeLast arr = unsafeIndex arr (length arr - 1)

unsafeIndex :: forall a. Array a -> Int -> a
unsafeIndex arr i = fromMaybe (unsafeIndex arr 0) (indexMaybe arr i)
  where
    indexMaybe :: Array a -> Int -> Maybe a
    indexMaybe xs idx = 
      if idx >= 0 && idx < length xs
        then Just (unsafePartialIndex xs idx)
        else Nothing
    
    -- Note: This is the only unsafe operation, guarded by bounds check above
    unsafePartialIndex :: Array a -> Int -> a
    unsafePartialIndex _ _ = unsafePartialIndex arr i -- Placeholder - actual FFI would be needed

interpolationClass :: InterpolationType -> String
interpolationClass = case _ of
  Linear -> "linear"
  Bezier -> "bezier"
  Hold -> "hold"
  Spring -> "spring"
  Elastic -> "elastic"
  Bounce -> "bounce"

keyframeIcon :: InterpolationType -> String
keyframeIcon = case _ of
  Linear -> "◆"
  Bezier -> "◇"
  Hold -> "■"
  Spring -> "●"
  Elastic -> "◐"
  Bounce -> "◑"

isInterpolation :: String -> InterpolationType -> State -> Boolean
isInterpolation kfId interp state =
  case filter (\kf -> kf.id == kfId) state.property.keyframes of
    [kf] -> kf.interpolation == interp
    _ -> false

min :: Number -> Number -> Number
min a b = if a < b then a else b

abs :: Number -> Number
abs n = if n < 0.0 then -n else n

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

propWrapperStyle :: String
propWrapperStyle =
  "width: 100%; " <>
  "display: flex; " <>
  "flex-direction: column;"

propSidebarStyle :: String
propSidebarStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "height: 28px; " <>
  "border-bottom: 1px solid var(--lattice-surface-3, #2a2a2a); " <>
  "background: var(--lattice-surface-1, #1a1a1a); " <>
  "font-size: 12px; " <>
  "color: var(--lattice-text-secondary, #ccc); " <>
  "padding-left: 8px;"

iconBoxStyle :: String
iconBoxStyle =
  "width: 20px; " <>
  "display: flex; " <>
  "justify-content: center; " <>
  "align-items: center; " <>
  "cursor: pointer; " <>
  "flex-shrink: 0;"

keyframeNavStyle :: String
keyframeNavStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 1px; " <>
  "margin-left: 4px;"

navBtnStyle :: String
navBtnStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "justify-content: center; " <>
  "width: 16px; " <>
  "height: 16px; " <>
  "padding: 0; " <>
  "border: none; " <>
  "background: transparent; " <>
  "color: var(--lattice-text-muted, #888); " <>
  "font-size: 8px; " <>
  "cursor: pointer; " <>
  "border-radius: 2px;"

propContentStyle :: String
propContentStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "flex: 1; " <>
  "min-width: 0; " <>
  "padding: 0 8px; " <>
  "gap: 8px;"

propInputsStyle :: String
propInputsStyle =
  "display: flex; " <>
  "gap: 6px; " <>
  "flex: 1; " <>
  "align-items: center; " <>
  "justify-content: flex-end;"

vecItemStyle :: String
vecItemStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 4px;"

vecLabelStyle :: String -> String
vecLabelStyle labelClass =
  "font-size: 12px; " <>
  "font-weight: bold; " <>
  "color: " <> labelColor labelClass <> ";"
  where
    labelColor = case _ of
      "x-label" -> "var(--lattice-error, #e74c3c)"
      "y-label" -> "var(--lattice-success, #2ecc71)"
      "z-label" -> "var(--lattice-info, #3498db)"
      _ -> "var(--lattice-text-muted)"

numberInputStyle :: String
numberInputStyle =
  "width: 60px; " <>
  "padding: 2px 4px; " <>
  "background: var(--lattice-surface-1, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border-subtle, #3a3a3a); " <>
  "color: var(--lattice-text-primary, #e0e0e0); " <>
  "border-radius: 3px; " <>
  "font-size: 12px;"

colorInputWrapperStyle :: String
colorInputWrapperStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 8px;"

stringInputStyle :: String
stringInputStyle =
  "width: 80px; " <>
  "padding: 2px 6px; " <>
  "background: var(--lattice-surface-1, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border-subtle, #3a3a3a); " <>
  "color: var(--lattice-text-primary, #e0e0e0); " <>
  "border-radius: 3px; " <>
  "font-size: 12px;"

propTrackStyle :: String
propTrackStyle =
  "height: 32px; " <>
  "background: var(--lattice-surface-0, #0a0a0a); " <>
  "border-bottom: 1px solid var(--lattice-surface-3, #222222); " <>
  "position: relative; " <>
  "cursor: pointer;"

keyframeStyle :: Number -> String
keyframeStyle leftPx =
  "position: absolute; " <>
  "width: 14px; " <>
  "height: 24px; " <>
  "top: 4px; " <>
  "left: " <> show leftPx <> "px; " <>
  "transform: translateX(-7px); " <>
  "cursor: ew-resize; " <>
  "color: var(--lattice-accent, #8B5CF6);"

keyframeShapeStyle :: String
keyframeShapeStyle =
  "width: 100%; " <>
  "height: 100%; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "justify-content: center; " <>
  "font-size: 12px;"

selectionBoxStyle :: Number -> Number -> String
selectionBoxStyle left width =
  "position: absolute; " <>
  "top: 2px; " <>
  "bottom: 2px; " <>
  "left: " <> show left <> "px; " <>
  "width: " <> show width <> "px; " <>
  "background: rgba(139, 92, 246, 0.2); " <>
  "border: 1px solid rgba(139, 92, 246, 0.6); " <>
  "pointer-events: none; " <>
  "z-index: 5;"

contextMenuStyle :: Number -> Number -> String
contextMenuStyle x y =
  "position: absolute; " <>
  "left: " <> show x <> "px; " <>
  "top: " <> show y <> "px; " <>
  "background: var(--lattice-surface-1, #121212); " <>
  "border-radius: 6px; " <>
  "box-shadow: 0 4px 16px rgba(0, 0, 0, 0.3); " <>
  "min-width: 150px; " <>
  "z-index: 100; " <>
  "padding: 6px 0; " <>
  "font-size: 11px;"

menuItemStyle :: String
menuItemStyle =
  "padding: 8px 12px; " <>
  "cursor: pointer; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 8px; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ _
      { layerId = input.layerId
      , property = input.property
      , layoutMode = input.layoutMode
      , pixelsPerFrame = input.pixelsPerFrame
      , currentFrame = input.currentFrame
      , frameCount = input.frameCount
      }
  
  HandleToggleAnimation -> do
    state <- H.get
    H.raise (ToggleAnimation state.layerId state.property.path (not state.property.animated))
  
  HandleAddKeyframeAtCurrent -> do
    state <- H.get
    H.raise (AddKeyframe state.layerId state.property.path state.property.value state.currentFrame)
  
  HandleGoToPrevKeyframe -> do
    state <- H.get
    let sortedKfs = sortBy (comparing _.frame) state.property.keyframes
    case findPrevKeyframe state.currentFrame sortedKfs of
      Just kf -> H.raise (GoToFrame kf.frame)
      Nothing -> pure unit
  
  HandleGoToNextKeyframe -> do
    state <- H.get
    let sortedKfs = sortBy (comparing _.frame) state.property.keyframes
    case findNextKeyframe state.currentFrame sortedKfs of
      Just kf -> H.raise (GoToFrame kf.frame)
      Nothing -> pure unit
  
  HandleSelectKeyframe kfId addToSelection -> do
    state <- H.get
    let newSelection = 
          if addToSelection
            then if Set.member kfId state.selectedKeyframeIds
                   then Set.delete kfId state.selectedKeyframeIds
                   else Set.insert kfId state.selectedKeyframeIds
            else Set.singleton kfId
    H.modify_ _ { selectedKeyframeIds = newSelection }
  
  HandleDeleteKeyframe kfId -> do
    state <- H.get
    H.raise (RemoveKeyframe state.layerId state.property.path kfId)
    H.modify_ _ { selectedKeyframeIds = Set.delete kfId state.selectedKeyframeIds }
  
  HandleShowContextMenu kfId x y -> do
    H.modify_ _ { contextMenu = Just { keyframeId: kfId, x, y } }
  
  HandleHideContextMenu -> do
    H.modify_ _ { contextMenu = Nothing }
  
  HandleSetInterpolation interp -> do
    state <- H.get
    case state.contextMenu of
      Just ctx -> 
        H.raise (SetInterpolation state.layerId state.property.path ctx.keyframeId interp)
      Nothing -> pure unit
    handleAction HandleHideContextMenu
  
  HandleGoToKeyframe -> do
    state <- H.get
    case state.contextMenu of
      Just ctx -> do
        let maybeKf = filter (\kf -> kf.id == ctx.keyframeId) state.property.keyframes
        case maybeKf of
          [kf] -> H.raise (GoToFrame kf.frame)
          _ -> pure unit
      Nothing -> pure unit
    handleAction HandleHideContextMenu
  
  HandleClearAllKeyframes -> do
    state <- H.get
    -- Remove all keyframes
    let kfIds = map _.id state.property.keyframes
    traverse_ (\kfId -> H.raise (RemoveKeyframe state.layerId state.property.path kfId)) kfIds
    H.modify_ _ { selectedKeyframeIds = Set.empty }
    handleAction HandleHideContextMenu
  
  HandleValueChange value -> do
    state <- H.get
    H.raise (SetPropertyValue state.layerId state.property.path value)
  
  HandleSelectProperty -> do
    state <- H.get
    H.raise (SelectProperty state.property.path)

-- Helper for traversing effects
traverse_ :: forall m a. Monad m => (a -> m Unit) -> Array a -> m Unit
traverse_ f arr = case arr of
  [] -> pure unit
  _ -> do
    _ <- traverse f arr
    pure unit
  where
    traverse :: (a -> m Unit) -> Array a -> m Unit
    traverse _ [] = pure unit
    traverse fn xs = case xs of
      [] -> pure unit
      _ -> do
        -- Process each element
        foldM (\_ x -> fn x) unit xs
    
    foldM :: forall b. (b -> a -> m b) -> b -> Array a -> m b
    foldM _ acc [] = pure acc
    foldM fn acc xs = 
      case mapWithIndex (\i x -> { i, x }) xs of
        [] -> pure acc
        items -> processItems fn acc items
    
    processItems :: forall b. (b -> a -> m b) -> b -> Array { i :: Int, x :: a } -> m b
    processItems _ acc [] = pure acc
    processItems fn acc items = do
      let h = unsafeIndex (map _.x items) 0
      newAcc <- fn acc h
      let rest = filter (\item -> item.i /= 0) items
      processItems fn newAcc rest
