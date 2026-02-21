-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Assets Panel Component
-- |
-- | Asset management panel with tabbed interface for:
-- | - Materials (PBR material library with presets)
-- | - SVG (imported vector graphics and logos)
-- | - Meshes (3D mesh particles for particle systems)
-- | - Sprites (sprite sheets for animated textures)
-- | - Environment (HDR environment maps)
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/AssetsPanel.vue
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.AssetsPanel
  ( component
  , module Types
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Web.Event.Event as Event
import Web.HTML as HTML
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window as Window
import Web.UIEvent.KeyboardEvent as KE

import Lattice.UI.Utils (getElementById)

import Lattice.UI.Components.AssetsPanel.Types
  ( Input
  , Output(..)
  , Query(..)
  , Slot
  , AssetTab(..)
  , Material
  , SvgDocument
  , MeshSource(..)
  , MeshParticle
  , SpriteSheet
  , State
  , Action(..)
  , Slots
  , allTabs
  ) as Types
import Lattice.UI.Components.AssetsPanel.Types
  ( Input
  , Output(..)
  , Query(..)
  , State
  , Action(..)
  , Slots
  , AssetTab(..)
  , allTabs
  )
import Lattice.UI.Components.AssetsPanel.Render (render)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
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
  { activeTab: TabMaterials
  , materials: input.materials
  , svgDocuments: input.svgDocuments
  , meshParticles: input.meshParticles
  , spriteSheets: input.spriteSheets
  , selectedMaterialId: Nothing
  , selectedSvgId: Nothing
  , selectedMeshId: Nothing
  , selectedSpriteId: Nothing
  , selectedPreset: ""
  , isLoading: false
  , lastError: Nothing
  , baseId: "lattice-assets"
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ 
      { materials = input.materials
      , svgDocuments = input.svgDocuments
      , meshParticles = input.meshParticles
      , spriteSheets = input.spriteSheets
      }
  
  SetActiveTab tab -> do
    H.modify_ _ { activeTab = tab }
    H.raise (TabChanged tab)
  
  HandleTabKeyDown currentIdx ke -> do
    state <- H.get
    let
      key = KE.key ke
      tabCount = Array.length allTabs
      
      nextIdx = case key of
        "ArrowRight" -> Just ((currentIdx + 1) `mod` tabCount)
        "ArrowLeft" -> Just ((currentIdx - 1 + tabCount) `mod` tabCount)
        "Home" -> Just 0
        "End" -> Just (tabCount - 1)
        _ -> Nothing

    for_ nextIdx \idx -> do
      liftEffect $ Event.preventDefault (KE.toEvent ke)
      case Array.index allTabs idx of
        Just tab -> do
          doc <- liftEffect $ HTML.window >>= Window.document
          let tabId = state.baseId <> "-tab-" <> show tab
          mEl <- liftEffect $ getElementById tabId doc
          for_ mEl \el -> liftEffect $ HTMLElement.focus el
          handleAction (SetActiveTab tab)
        Nothing -> pure unit
  
  SelectMaterial id -> do
    H.modify_ _ { selectedMaterialId = Just id }
    H.raise (MaterialSelected id)
  
  CreateMaterial -> do
    H.raise (MaterialCreated "new-material")
  
  DeleteMaterial id -> do
    state <- H.get
    when (state.selectedMaterialId == Just id) do
      H.modify_ _ { selectedMaterialId = Nothing }
    H.raise (MaterialDeleted id)
  
  SetMaterialPreset preset -> do
    H.modify_ _ { selectedPreset = preset }
    when (preset /= "") do
      H.raise (MaterialCreated preset)
      H.modify_ _ { selectedPreset = "" }
  
  SelectSvg id -> do
    H.modify_ _ { selectedSvgId = Just id }
    H.raise (SvgSelected id)
  
  DeleteSvg id -> do
    state <- H.get
    when (state.selectedSvgId == Just id) do
      H.modify_ _ { selectedSvgId = Nothing }
    H.raise (SvgDeleted id)
  
  CreateLayersFromSvgAction id -> do
    H.raise (CreateLayersFromSvg id)
  
  RegisterSvgAsMeshAction id -> do
    H.raise (RegisterSvgAsMesh id)
    H.modify_ _ { activeTab = TabMeshes }
  
  SelectMesh id -> do
    H.modify_ _ { selectedMeshId = Just id }
    H.raise (MeshSelected id)
  
  DeleteMesh id -> do
    state <- H.get
    when (state.selectedMeshId == Just id) do
      H.modify_ _ { selectedMeshId = Nothing }
    H.raise (MeshDeleted id)
  
  UseMeshAsEmitterAction id -> do
    H.raise (UseMeshAsEmitter id)
  
  SelectSprite id -> do
    H.modify_ _ { selectedSpriteId = Just id }
    H.raise (SpriteSelected id)
  
  DeleteSprite id -> do
    state <- H.get
    when (state.selectedSpriteId == Just id) do
      H.modify_ _ { selectedSpriteId = Nothing }
    H.raise (SpriteDeleted id)
  
  OpenSpriteImport -> do
    H.raise ImportSpriteSheet
  
  ClearError -> do
    H.modify_ _ { lastError = Nothing }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  SetTab tab next -> do
    handleAction (SetActiveTab tab)
    pure (Just next)
  
  RefreshAssets next -> do
    -- parent would typically refresh via input props
    pure (Just next)
  
  GetSelectedMaterial reply -> do
    state <- H.get
    pure (Just (reply state.selectedMaterialId))
