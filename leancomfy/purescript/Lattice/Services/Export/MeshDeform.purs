-- | Lattice.Services.Export.MeshDeform - Mesh deform export
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
    -- * Pin Trajectory Export
  , exportPinsAsTrajectory
  , exportPinsAsTrajectoryWithMetadata
  , exportPinPositionsPerFrame
    -- * Depth Export
  , DepthBuffer
  , DeformedVertices
  , exportOverlapAsDepth
  , depthBufferToImageData
  , exportOverlapDepthSequence
    -- * Mask Export
  , ImageDataHandle
  , exportDeformedMeshMask
  , exportDeformedMeshMaskBinary
  , exportMeshMaskSequence
  ) where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)
import Data.Int (toNumber)

import Lattice.Services.Export.Types (WanMoveTrajectory)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Depth buffer format
data MeshDepthFormat
  = DepthUint8
  | DepthUint16
  | DepthFloat32

derive instance Generic MeshDepthFormat _
instance Show MeshDepthFormat where show = genericShow
instance Eq MeshDepthFormat where eq = genericEq

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
  , depth :: DepthBuffer
  }

-- | Mask export frame
type MaskExportFrame =
  { frame :: Int
  , mask :: ImageDataHandle
  }

--------------------------------------------------------------------------------
-- FFI Types
--------------------------------------------------------------------------------

-- | Opaque depth buffer handle
foreign import data DepthBuffer :: Type

-- | Opaque ImageData handle
foreign import data ImageDataHandle :: Type

-- | Opaque deformed vertices handle
foreign import data DeformedVertices :: Type

--------------------------------------------------------------------------------
-- Pin Trajectory Export
--------------------------------------------------------------------------------

-- | Export pins as trajectory (pure computation, delegates to FFI for interpolation)
foreign import exportPinsAsTrajectoryImpl
  :: Array WarpPin
  -> { startFrame :: Int, endFrame :: Int }
  -> CompositionInfo
  -> Effect WanMoveTrajectory

exportPinsAsTrajectory
  :: Array WarpPin
  -> { startFrame :: Int, endFrame :: Int }
  -> CompositionInfo
  -> Effect WanMoveTrajectory
exportPinsAsTrajectory = exportPinsAsTrajectoryImpl

-- | Export pins with metadata
exportPinsAsTrajectoryWithMetadata
  :: Array WarpPin
  -> { startFrame :: Int, endFrame :: Int }
  -> CompositionInfo
  -> Effect { trajectory :: WanMoveTrajectory, pinMetadata :: Array PinMetadata }
exportPinsAsTrajectoryWithMetadata pins frameRange composition = do
  trajectory <- exportPinsAsTrajectory pins frameRange composition
  let
    trackablePins = Array.filter isTrackable pins
    metadata = map pinToMetadata trackablePins
  pure { trajectory, pinMetadata: metadata }

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

-- | Export pin positions per frame
foreign import exportPinPositionsPerFrameImpl
  :: Array WarpPin
  -> { startFrame :: Int, endFrame :: Int }
  -> Int  -- frameRate
  -> Effect (Array { frame :: Int, positions :: Array { id :: String, x :: Number, y :: Number } })

exportPinPositionsPerFrame
  :: Array WarpPin
  -> { startFrame :: Int, endFrame :: Int }
  -> Int
  -> Effect (Array { frame :: Int, positions :: Array { id :: String, x :: Number, y :: Number } })
exportPinPositionsPerFrame = exportPinPositionsPerFrameImpl

--------------------------------------------------------------------------------
-- Depth Export
--------------------------------------------------------------------------------

-- | Export overlap pins as depth map
foreign import exportOverlapAsDepthImpl
  :: MeshFromAlphaResult
  -> DeformedVertices
  -> Array WarpPin
  -> Int  -- frame
  -> Int  -- width
  -> Int  -- height
  -> String  -- format
  -> Effect DepthBuffer

exportOverlapAsDepth
  :: MeshFromAlphaResult
  -> DeformedVertices
  -> Array WarpPin
  -> Int
  -> Int
  -> Int
  -> MeshDepthFormat
  -> Effect DepthBuffer
exportOverlapAsDepth mesh vertices pins frame width height format =
  exportOverlapAsDepthImpl mesh vertices pins frame width height (formatToString format)

-- | Format to string
formatToString :: MeshDepthFormat -> String
formatToString = case _ of
  DepthUint8 -> "uint8"
  DepthUint16 -> "uint16"
  DepthFloat32 -> "float32"

-- | Convert depth buffer to ImageData
foreign import depthBufferToImageData :: DepthBuffer -> Int -> Int -> Effect ImageDataHandle

-- | Export depth sequence
foreign import exportOverlapDepthSequenceImpl
  :: MeshFromAlphaResult
  -> Array DeformedVertices
  -> Array WarpPin
  -> { startFrame :: Int, endFrame :: Int }
  -> Int  -- width
  -> Int  -- height
  -> String  -- format
  -> Effect (Array DepthExportFrame)

exportOverlapDepthSequence
  :: MeshFromAlphaResult
  -> Array DeformedVertices
  -> Array WarpPin
  -> { startFrame :: Int, endFrame :: Int }
  -> Int
  -> Int
  -> MeshDepthFormat
  -> Effect (Array DepthExportFrame)
exportOverlapDepthSequence mesh verticesPerFrame pins frameRange width height format =
  exportOverlapDepthSequenceImpl mesh verticesPerFrame pins frameRange width height (formatToString format)

--------------------------------------------------------------------------------
-- Mask Export
--------------------------------------------------------------------------------

-- | Export deformed mesh as mask
foreign import exportDeformedMeshMask
  :: MeshFromAlphaResult
  -> DeformedVertices
  -> Int  -- width
  -> Int  -- height
  -> Effect ImageDataHandle

-- | Export mesh mask as binary
foreign import exportDeformedMeshMaskBinary
  :: MeshFromAlphaResult
  -> DeformedVertices
  -> Int  -- width
  -> Int  -- height
  -> Effect DepthBuffer  -- Actually Uint8Array

-- | Export mask sequence
foreign import exportMeshMaskSequenceImpl
  :: MeshFromAlphaResult
  -> Array DeformedVertices
  -> { startFrame :: Int, endFrame :: Int }
  -> Int  -- width
  -> Int  -- height
  -> Effect (Array MaskExportFrame)

exportMeshMaskSequence
  :: MeshFromAlphaResult
  -> Array DeformedVertices
  -> { startFrame :: Int, endFrame :: Int }
  -> Int
  -> Int
  -> Effect (Array MaskExportFrame)
exportMeshMaskSequence = exportMeshMaskSequenceImpl
