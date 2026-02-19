-- | Lattice.Services.Export.MeshDeform - Mesh deform export
-- |
-- | Pure request types for mesh deformation data export.
-- | All actual rendering is done by the Haskell backend via Bridge.
-- |
-- | Export functions for mesh deformation data to AI video generation tools:
-- | - Wan-Move/ATI: Pin trajectories as point tracks
-- | - ControlNet: Overlap pin depth maps
-- | - TTM: Motion masks from deformed mesh
-- |
-- | Source: ui/src/services/export/meshDeformExport.ts

module Lattice.Services.Export.MeshDeform
  ( -- * Types
    MeshDepthFormat(..)
  , CompositionInfo
  , WarpPinType(..)
  , WarpPin
  , MeshFromAlphaResult
  , PinMetadata
  , DepthExportFrame
  , MaskExportFrame
    -- * Request Types
  , MeshDeformRequest(..)
    -- * Request Builders
  , mkExportPinsRequest
  , mkExportDepthRequest
  , mkExportMaskRequest
    -- * Pure Computations
  , exportPinsAsTrajectoryWithMetadata
  , isTrackable
  , pinToMetadata
  , pinTypeToString
  , formatToString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)

import Lattice.Services.Export.Types (WanMoveTrajectory)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Depth buffer format
data MeshDepthFormat
  = DepthUint8
  | DepthUint16
  | DepthFloat32

derive instance Generic MeshDepthFormat _
instance Show MeshDepthFormat where show = genericShow
instance Eq MeshDepthFormat where eq = genericEq
instance EncodeJson MeshDepthFormat where
  encodeJson = genericEncodeJson

-- | Composition info for export
type CompositionInfo =
  { width :: Int
  , height :: Int
  , frameRate :: Int
  }

-- | Warp pin types
data WarpPinType
  = PinPosition
  | PinAdvanced
  | PinBend
  | PinRotation
  | PinStarch
  | PinOverlap

derive instance Generic WarpPinType _
instance Show WarpPinType where show = genericShow
instance Eq WarpPinType where eq = genericEq
instance EncodeJson WarpPinType where
  encodeJson = genericEncodeJson

-- | Warp pin
type WarpPin =
  { id :: String
  , name :: String
  , type :: WarpPinType
  , position :: { x :: Number, y :: Number }
  }

-- | Mesh from alpha result
type MeshFromAlphaResult =
  { triangles :: Array Int
  , triangleCount :: Int
  , vertexCount :: Int
  }

-- | Pin metadata for export
type PinMetadata =
  { id :: String
  , name :: String
  , type :: String
  }

-- | Depth export frame
type DepthExportFrame =
  { frame :: Int
  , depthData :: String    -- Base64 encoded depth buffer
  }

-- | Mask export frame
type MaskExportFrame =
  { frame :: Int
  , maskData :: String     -- Base64 encoded mask data
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Request Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Mesh deform request - sent to Haskell backend
data MeshDeformRequest
  = ExportPinsAsTrajectoryRequest
      { pins :: Array WarpPin
      , frameRange :: { startFrame :: Int, endFrame :: Int }
      , composition :: CompositionInfo
      }
  | ExportPinPositionsPerFrameRequest
      { pins :: Array WarpPin
      , frameRange :: { startFrame :: Int, endFrame :: Int }
      , frameRate :: Int
      }
  | ExportOverlapAsDepthRequest
      { mesh :: MeshFromAlphaResult
      , vertexData :: String     -- Base64 encoded vertex data
      , pins :: Array WarpPin
      , frame :: Int
      , width :: Int
      , height :: Int
      , format :: MeshDepthFormat
      }
  | ExportOverlapDepthSequenceRequest
      { mesh :: MeshFromAlphaResult
      , vertexDataPerFrame :: Array String  -- Base64 encoded per frame
      , pins :: Array WarpPin
      , frameRange :: { startFrame :: Int, endFrame :: Int }
      , width :: Int
      , height :: Int
      , format :: MeshDepthFormat
      }
  | ExportDeformedMeshMaskRequest
      { mesh :: MeshFromAlphaResult
      , vertexData :: String     -- Base64 encoded vertex data
      , width :: Int
      , height :: Int
      }
  | ExportMeshMaskSequenceRequest
      { mesh :: MeshFromAlphaResult
      , vertexDataPerFrame :: Array String
      , frameRange :: { startFrame :: Int, endFrame :: Int }
      , width :: Int
      , height :: Int
      }

derive instance Generic MeshDeformRequest _
instance Show MeshDeformRequest where show = genericShow
instance EncodeJson MeshDeformRequest where
  encodeJson = genericEncodeJson

-- ────────────────────────────────────────────────────────────────────────────
-- Request Builders
-- ────────────────────────────────────────────────────────────────────────────

-- | Create pin trajectory export request
mkExportPinsRequest
  :: Array WarpPin
  -> { startFrame :: Int, endFrame :: Int }
  -> CompositionInfo
  -> MeshDeformRequest
mkExportPinsRequest pins frameRange composition =
  ExportPinsAsTrajectoryRequest { pins, frameRange, composition }

-- | Create depth export request
mkExportDepthRequest
  :: MeshFromAlphaResult
  -> String
  -> Array WarpPin
  -> Int
  -> Int
  -> Int
  -> MeshDepthFormat
  -> MeshDeformRequest
mkExportDepthRequest mesh vertexData pins frame width height format =
  ExportOverlapAsDepthRequest
    { mesh, vertexData, pins, frame, width, height, format }

-- | Create mask export request
mkExportMaskRequest
  :: MeshFromAlphaResult
  -> String
  -> Int
  -> Int
  -> MeshDeformRequest
mkExportMaskRequest mesh vertexData width height =
  ExportDeformedMeshMaskRequest { mesh, vertexData, width, height }

-- ────────────────────────────────────────────────────────────────────────────
-- Pure Computations
-- ────────────────────────────────────────────────────────────────────────────

-- | Export pins with metadata (pure computation for metadata generation)
exportPinsAsTrajectoryWithMetadata
  :: Array WarpPin
  -> { trajectory :: WanMoveTrajectory, pinMetadata :: Array PinMetadata }
exportPinsAsTrajectoryWithMetadata pins =
  let
    trackablePins = Array.filter isTrackable pins
    metadata = map pinToMetadata trackablePins
    -- The actual trajectory computation is done by the backend
    -- This just returns the metadata portion
  in
    { trajectory:
        { width: 0      -- Set by backend
        , height: 0     -- Set by backend
        , frameCount: 0 -- Set by backend
        , tracks: []    -- Computed by backend
        }
    , pinMetadata: metadata
    }

-- | Check if pin is trackable
isTrackable :: WarpPin -> Boolean
isTrackable pin = case pin.type of
  PinPosition -> true
  PinAdvanced -> true
  PinBend -> true
  PinRotation -> true
  _ -> false

-- | Convert pin to metadata
pinToMetadata :: WarpPin -> PinMetadata
pinToMetadata pin =
  { id: pin.id
  , name: pin.name
  , type: pinTypeToString pin.type
  }

-- | Pin type to string
pinTypeToString :: WarpPinType -> String
pinTypeToString = case _ of
  PinPosition -> "position"
  PinAdvanced -> "advanced"
  PinBend -> "bend"
  PinRotation -> "rotation"
  PinStarch -> "starch"
  PinOverlap -> "overlap"

-- | Format to string
formatToString :: MeshDepthFormat -> String
formatToString = case _ of
  DepthUint8 -> "uint8"
  DepthUint16 -> "uint16"
  DepthFloat32 -> "float32"
