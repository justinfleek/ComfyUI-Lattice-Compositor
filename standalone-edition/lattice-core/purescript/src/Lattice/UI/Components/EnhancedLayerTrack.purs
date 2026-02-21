-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // enhanced-layer-track
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Full-featured timeline layer track with:
-- | - Sidebar mode: AV features, layer info, switches, parent linking
-- | - Track mode: duration bar with trim handles, waveform for audio layers
-- | - Expandable property groups (Transform, Material Options, et al.)
-- | - Context menu for layer operations
-- | - Color picker for layer labels
-- | - Drag-drop reordering
-- | - Layer bar drag/resize with snap-to-playhead
-- |
-- | System F/Omega: EnhancedLayerTrack = Component Input Output State Action
-- |
module Lattice.UI.Components.EnhancedLayerTrack
  ( component
  , module Lattice.UI.Components.EnhancedLayerTrack.Types
  ) where

import Prelude

import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.Query.Event as HQE
import Web.Event.Event (stopPropagation)
import Web.HTML as HTML
import Web.HTML.Window as Window
import Web.UIEvent.MouseEvent as ME
import Web.UIEvent.MouseEvent.EventTypes as MET

import Lattice.UI.Components.EnhancedLayerTrack.Types
import Lattice.UI.Components.EnhancedLayerTrack.Snap
  ( getSnapTargets
  , snapToNearest
  , snapTolerance
  , intAbs
  , clampInt
  , roundToInt
  )
import Lattice.UI.Components.EnhancedLayerTrack.Render (render)

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // component
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
  { layer: input.layer
  , layoutMode: input.layoutMode
  , isExpanded: input.isExpanded
  , isSelected: input.isSelected
  , frameCount: input.frameCount
  , pixelsPerFrame: input.pixelsPerFrame
  , availableParents: input.availableParents
  , hasAudioCapability: input.hasAudioCapability
  -- ── snap targets ─────────────────────────────────────────────────────────
  , allLayers: input.allLayers
  , currentFrame: input.currentFrame
  , markers: input.markers
  -- ── ui state ─────────────────────────────────────────────────────────────
  , expandedGroups: Set.fromFoldable ["Transform", "Text", "More Options"]
  , isRenaming: false
  , renameValue: ""
  , isDragTarget: false
  , showColorPicker: false
  , colorPickerPos: { x: 0.0, y: 0.0 }
  , contextMenu: Nothing
  -- ── drag/resize state ────────────────────────────────────────────────────
  , dragMode: NotDragging
  , dragStartX: 0.0
  , dragStartInPoint: 0
  , dragStartOutPoint: 0
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- subscribe to global mouse events for drag tracking
    win <- liftEffect HTML.window
    void $ H.subscribe $ HQE.eventListener
      MET.mousemove
      (Window.toEventTarget win)
      (ME.fromEvent >>> map OnGlobalMouseMove)
    void $ H.subscribe $ HQE.eventListener
      MET.mouseup
      (Window.toEventTarget win)
      (ME.fromEvent >>> map OnGlobalMouseUp)
  
  Receive input -> do
    H.modify_ _
      { layer = input.layer
      , layoutMode = input.layoutMode
      , isExpanded = input.isExpanded
      , isSelected = input.isSelected
      , frameCount = input.frameCount
      , pixelsPerFrame = input.pixelsPerFrame
      , availableParents = input.availableParents
      , hasAudioCapability = input.hasAudioCapability
      , allLayers = input.allLayers
      , currentFrame = input.currentFrame
      , markers = input.markers
      }
  
  -- ── selection ────────────────────────────────────────────────────────────
  HandleSelectLayer -> do
    state <- H.get
    H.raise (SelectLayer state.layer.id)
  
  HandleToggleExpand -> do
    state <- H.get
    H.raise (ToggleExpand state.layer.id (not state.isExpanded))
  
  HandleToggleGroup groupName -> do
    state <- H.get
    let newGroups = 
          if Set.member groupName state.expandedGroups
            then Set.delete groupName state.expandedGroups
            else Set.insert groupName state.expandedGroups
    H.modify_ _ { expandedGroups = newGroups }
  
  -- ── av features ──────────────────────────────────────────────────────────
  HandleToggleVisibility -> do
    state <- H.get
    H.raise (UpdateLayerVisibility state.layer.id (not state.layer.visible))
  
  HandleToggleAudio -> do
    state <- H.get
    H.raise (UpdateLayerAudio state.layer.id (not state.layer.audioEnabled))
  
  HandleToggleIsolate -> do
    state <- H.get
    H.raise (UpdateLayerIsolate state.layer.id (not state.layer.isolate))
  
  HandleToggleLock -> do
    state <- H.get
    H.raise (UpdateLayerLocked state.layer.id (not state.layer.locked))
  
  -- ── switches ─────────────────────────────────────────────────────────────
  HandleToggleMinimized -> do
    state <- H.get
    H.raise (UpdateLayerMinimized state.layer.id (not state.layer.minimized))
  
  HandleToggleFlattenTransform -> do
    state <- H.get
    H.raise (UpdateLayerFlattenTransform state.layer.id (not state.layer.flattenTransform))
  
  HandleToggleQuality -> do
    state <- H.get
    let newQuality = if state.layer.quality == "best" then "draft" else "best"
    H.raise (UpdateLayerQuality state.layer.id newQuality)
  
  HandleToggleEffects -> do
    state <- H.get
    H.raise (UpdateLayerEffectsEnabled state.layer.id (not state.layer.effectsEnabled))
  
  HandleToggleFrameBlend -> do
    state <- H.get
    H.raise (UpdateLayerFrameBlending state.layer.id (not state.layer.frameBlending))
  
  HandleToggleMotionBlur -> do
    state <- H.get
    H.raise (UpdateLayerMotionBlur state.layer.id (not state.layer.motionBlur))
  
  HandleToggleEffectLayer -> do
    state <- H.get
    H.raise (UpdateLayerEffectLayer state.layer.id (not state.layer.effectLayer))
  
  HandleToggle3D -> do
    state <- H.get
    H.raise (UpdateLayer3D state.layer.id (not state.layer.threeD))
  
  -- ── parenting ────────────────────────────────────────────────────────────
  HandleSetParent parentId -> do
    state <- H.get
    H.raise (UpdateLayerParent state.layer.id parentId)
  
  -- ── color picker ─────────────────────────────────────────────────────────
  HandleShowColorPicker x y -> do
    H.modify_ _ { showColorPicker = true, colorPickerPos = { x, y } }
  
  HandleHideColorPicker -> do
    H.modify_ _ { showColorPicker = false }
  
  HandleSetLabelColor color -> do
    state <- H.get
    H.raise (UpdateLayerLabelColor state.layer.id color)
    H.modify_ _ { showColorPicker = false }
  
  -- ── renaming ─────────────────────────────────────────────────────────────
  HandleStartRename -> do
    state <- H.get
    H.modify_ _ { isRenaming = true, renameValue = state.layer.name }
    handleAction HandleHideContextMenu
  
  HandleRenameInput val -> do
    H.modify_ _ { renameValue = val }
  
  HandleFinishRename -> do
    state <- H.get
    when (state.renameValue /= "") do
      H.raise (RenameLayer state.layer.id state.renameValue)
    H.modify_ _ { isRenaming = false, renameValue = "" }
  
  HandleCancelRename -> do
    H.modify_ _ { isRenaming = false, renameValue = "" }
  
  -- ── context menu ─────────────────────────────────────────────────────────
  HandleShowContextMenu x y -> do
    H.modify_ _ { contextMenu = Just { x, y } }
  
  HandleHideContextMenu -> do
    H.modify_ _ { contextMenu = Nothing }
  
  HandleDuplicate -> do
    state <- H.get
    H.raise (DuplicateLayer state.layer.id)
    handleAction HandleHideContextMenu
  
  HandleDelete -> do
    state <- H.get
    H.raise (DeleteLayer state.layer.id)
    handleAction HandleHideContextMenu
  
  HandleNest -> do
    state <- H.get
    H.raise (NestLayer state.layer.id)
    handleAction HandleHideContextMenu
  
  HandleConvertToSplines -> do
    state <- H.get
    H.raise (ConvertToSplines state.layer.id)
    handleAction HandleHideContextMenu
  
  HandleResetTransform -> do
    state <- H.get
    H.raise (ResetTransform state.layer.id)
  
  -- ── drag/drop for layer reordering ───────────────────────────────────────
  HandleReorderDragStart -> do
    pure unit  -- parent handles actual drag data
  
  HandleReorderDragOver -> do
    H.modify_ _ { isDragTarget = true }
  
  HandleReorderDragLeave -> do
    H.modify_ _ { isDragTarget = false }
  
  HandleReorderDrop draggedLayerId -> do
    state <- H.get
    H.modify_ _ { isDragTarget = false }
    when (draggedLayerId /= state.layer.id) do
      H.raise (ReorderLayer draggedLayerId state.layer.index)
  
  -- ── double-click actions ─────────────────────────────────────────────────
  HandleDoubleClick -> do
    state <- H.get
    if state.layer.layerType == "nestedComp"
      then H.raise (EnterNestedComp state.layer.id)
      else handleAction HandleStartRename
  
  -- ── layer bar drag/resize ────────────────────────────────────────────────
  StartBarDrag event -> do
    state <- H.get
    when (not state.layer.locked) do
      let x = Int.toNumber (ME.clientX event)
      H.modify_ _
        { dragMode = DraggingBar
        , dragStartX = x
        , dragStartInPoint = state.layer.inPoint
        , dragStartOutPoint = state.layer.outPoint
        }
  
  StartResizeLeft event -> do
    state <- H.get
    when (not state.layer.locked) do
      let x = Int.toNumber (ME.clientX event)
      H.modify_ _
        { dragMode = ResizingLeft
        , dragStartX = x
        , dragStartInPoint = state.layer.inPoint
        }
      liftEffect $ stopPropagation (ME.toEvent event)
  
  StartResizeRight event -> do
    state <- H.get
    when (not state.layer.locked) do
      let x = Int.toNumber (ME.clientX event)
      H.modify_ _
        { dragMode = ResizingRight
        , dragStartX = x
        , dragStartOutPoint = state.layer.outPoint
        }
      liftEffect $ stopPropagation (ME.toEvent event)
  
  OnGlobalMouseMove event -> do
    state <- H.get
    case state.dragMode of
      NotDragging -> pure unit
      DraggingBar -> handleBarDrag state event
      ResizingLeft -> handleResizeLeft state event
      ResizingRight -> handleResizeRight state event
  
  OnGlobalMouseUp _ -> do
    state <- H.get
    when (state.dragMode /= NotDragging) do
      H.modify_ _ { dragMode = NotDragging }

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // drag // handlers
-- ════════════════════════════════════════════════════════════════════════════

handleBarDrag :: forall m. MonadAff m => State -> ME.MouseEvent -> H.HalogenM State Action () Output m Unit
handleBarDrag state event = do
  let
    currentX = Int.toNumber (ME.clientX event)
    dx = currentX - state.dragStartX
    framesDelta = roundToInt (dx / state.pixelsPerFrame)
    duration = state.dragStartOutPoint - state.dragStartInPoint
    
    rawInPoint = state.dragStartInPoint + framesDelta
    rawOutPoint = rawInPoint + duration
    
    -- apply snap if Shift key is held
    shiftHeld = ME.shiftKey event
    targets = if shiftHeld then getSnapTargets state else []
    
    snappedIn = if shiftHeld then snapToNearest rawInPoint targets else rawInPoint
    snappedOut = if shiftHeld then snapToNearest rawOutPoint targets else rawOutPoint
    
    -- prefer snapping whichever edge is closer
    inDist = intAbs (snappedIn - rawInPoint)
    outDist = intAbs (snappedOut - rawOutPoint)
    
    { newIn, newOut } = 
      if shiftHeld && inDist <= outDist && inDist <= snapTolerance
        then { newIn: snappedIn, newOut: snappedIn + duration }
      else if shiftHeld && outDist <= snapTolerance
        then { newIn: snappedOut - duration, newOut: snappedOut }
      else { newIn: rawInPoint, newOut: rawOutPoint }
    
    -- clamp to valid range
    clampedIn = 
      if newIn < 0 then 0
      else if newOut >= state.frameCount then state.frameCount - 1 - duration
      else newIn
    clampedOut = clampedIn + duration
  
  when (clampedIn /= state.layer.inPoint || clampedOut /= state.layer.outPoint) do
    H.raise (UpdateLayerTiming state.layer.id clampedIn clampedOut)

handleResizeLeft :: forall m. MonadAff m => State -> ME.MouseEvent -> H.HalogenM State Action () Output m Unit
handleResizeLeft state event = do
  let
    currentX = Int.toNumber (ME.clientX event)
    dx = currentX - state.dragStartX
    framesDelta = roundToInt (dx / state.pixelsPerFrame)
    
    rawInPoint = state.dragStartInPoint + framesDelta
    
    shiftHeld = ME.shiftKey event
    targets = if shiftHeld then getSnapTargets state else []
    snappedIn = if shiftHeld then snapToNearest rawInPoint targets else rawInPoint
    
    clampedIn = clampInt 0 (state.layer.outPoint - 1) snappedIn
  
  when (clampedIn /= state.layer.inPoint) do
    H.raise (UpdateLayerTiming state.layer.id clampedIn state.layer.outPoint)

handleResizeRight :: forall m. MonadAff m => State -> ME.MouseEvent -> H.HalogenM State Action () Output m Unit
handleResizeRight state event = do
  let
    currentX = Int.toNumber (ME.clientX event)
    dx = currentX - state.dragStartX
    framesDelta = roundToInt (dx / state.pixelsPerFrame)
    
    rawOutPoint = state.dragStartOutPoint + framesDelta
    
    shiftHeld = ME.shiftKey event
    targets = if shiftHeld then getSnapTargets state else []
    snappedOut = if shiftHeld then snapToNearest rawOutPoint targets else rawOutPoint
    
    clampedOut = clampInt (state.layer.inPoint + 1) (state.frameCount - 1) snappedOut
  
  when (clampedOut /= state.layer.outPoint) do
    H.raise (UpdateLayerTiming state.layer.id state.layer.inPoint clampedOut)
