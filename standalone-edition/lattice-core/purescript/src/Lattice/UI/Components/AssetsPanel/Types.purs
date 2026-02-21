-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Assets Panel Types
-- |
-- | Type definitions for the asset management panel.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.AssetsPanel.Types
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
    -- helpers
  , allTabs
  , tabLabel
  , tabIcon
  , tabTooltip
  , materialPresets
  , meshSourceIcon
  , meshSourceLabel
  , findSelected
  , formatNumber
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Halogen as H
import Web.UIEvent.KeyboardEvent as KE

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // input // output
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { materials :: Array Material
  , svgDocuments :: Array SvgDocument
  , meshParticles :: Array MeshParticle
  , spriteSheets :: Array SpriteSheet
  }

data Output
  = MaterialSelected String
  | MaterialCreated String
  | MaterialDeleted String
  | SvgSelected String
  | SvgDeleted String
  | CreateLayersFromSvg String
  | RegisterSvgAsMesh String
  | MeshSelected String
  | MeshDeleted String
  | UseMeshAsEmitter String
  | SpriteSelected String
  | SpriteDeleted String
  | ImportSpriteSheet
  | TabChanged AssetTab

data Query a
  = SetTab AssetTab a
  | RefreshAssets a
  | GetSelectedMaterial (Maybe String -> a)

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // asset types
-- ════════════════════════════════════════════════════════════════════════════

data AssetTab
  = TabMaterials
  | TabSvg
  | TabMeshes
  | TabSprites
  | TabEnvironment

derive instance eqAssetTab :: Eq AssetTab

instance showAssetTab :: Show AssetTab where
  show = case _ of
    TabMaterials -> "materials"
    TabSvg -> "svg"
    TabMeshes -> "meshes"
    TabSprites -> "sprites"
    TabEnvironment -> "environment"

allTabs :: Array AssetTab
allTabs = [ TabMaterials, TabSvg, TabMeshes, TabSprites, TabEnvironment ]

tabLabel :: AssetTab -> String
tabLabel = case _ of
  TabMaterials -> "Materials"
  TabSvg -> "SVG"
  TabMeshes -> "Meshes"
  TabSprites -> "Sprites"
  TabEnvironment -> "Env"

tabIcon :: AssetTab -> String
tabIcon = case _ of
  TabMaterials -> "[M]"
  TabSvg -> "[S]"
  TabMeshes -> "[X]"
  TabSprites -> "[P]"
  TabEnvironment -> "[E]"

tabTooltip :: AssetTab -> String
tabTooltip = case _ of
  TabMaterials -> "PBR Materials"
  TabSvg -> "SVG Logos & Shapes"
  TabMeshes -> "Mesh Particles"
  TabSprites -> "Sprite Sheets"
  TabEnvironment -> "Environment Map"

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // asset records
-- ════════════════════════════════════════════════════════════════════════════

type Material =
  { id :: String
  , name :: String
  , color :: String
  , previewUrl :: Maybe String
  }

type SvgDocument =
  { id :: String
  , name :: String
  , pathCount :: Int
  }

data MeshSource
  = MeshPrimitive
  | MeshSvg
  | MeshCustom

derive instance eqMeshSource :: Eq MeshSource

type MeshParticle =
  { id :: String
  , name :: String
  , source :: MeshSource
  , vertexCount :: Int
  , boundingRadius :: Number
  }

type SpriteSheet =
  { id :: String
  , name :: String
  , textureUrl :: String
  , totalFrames :: Int
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { activeTab :: AssetTab
  , materials :: Array Material
  , svgDocuments :: Array SvgDocument
  , meshParticles :: Array MeshParticle
  , spriteSheets :: Array SpriteSheet
  , selectedMaterialId :: Maybe String
  , selectedSvgId :: Maybe String
  , selectedMeshId :: Maybe String
  , selectedSpriteId :: Maybe String
  , selectedPreset :: String
  , isLoading :: Boolean
  , lastError :: Maybe String
  , baseId :: String
  }

data Action
  = Initialize
  | Receive Input
  | SetActiveTab AssetTab
  | HandleTabKeyDown Int KE.KeyboardEvent
  | SelectMaterial String
  | CreateMaterial
  | DeleteMaterial String
  | SetMaterialPreset String
  | SelectSvg String
  | DeleteSvg String
  | CreateLayersFromSvgAction String
  | RegisterSvgAsMeshAction String
  | SelectMesh String
  | DeleteMesh String
  | UseMeshAsEmitterAction String
  | SelectSprite String
  | DeleteSprite String
  | OpenSpriteImport
  | ClearError

type Slots = ()

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // material presets
-- ════════════════════════════════════════════════════════════════════════════

materialPresets :: Array String
materialPresets =
  [ "chrome"
  , "gold"
  , "silver"
  , "copper"
  , "brass"
  , "glass"
  , "plastic"
  , "rubber"
  , "wood"
  , "concrete"
  , "emissive"
  , "holographic"
  ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

meshSourceIcon :: MeshSource -> String
meshSourceIcon = case _ of
  MeshPrimitive -> "[P]"
  MeshSvg -> "[V]"
  MeshCustom -> "[C]"

meshSourceLabel :: MeshSource -> String
meshSourceLabel = case _ of
  MeshPrimitive -> "primitive"
  MeshSvg -> "svg"
  MeshCustom -> "custom"

findSelected :: forall a. Maybe String -> Array { id :: String | a } -> Maybe { id :: String | a }
findSelected mId items =
  case mId of
    Nothing -> Nothing
    Just id -> Array.find (\item -> item.id == id) items

formatNumber :: Number -> String
formatNumber n = show n
