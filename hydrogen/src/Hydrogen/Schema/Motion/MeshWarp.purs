-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // motion // mesh-warp
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mesh warp deformation types for vector skinning-style animation.
-- |
-- | Provides organic animation by manipulating control pins on a triangulated
-- | mesh overlay. Each pin influences nearby vertices with configurable falloff.
-- |
-- | ## Architecture
-- |
-- | Mirrors `Lattice.MeshWarp` from the Haskell backend.
-- |
-- | ## Pin Types
-- |
-- | - Position: Move mesh vertices by animating position
-- | - Rotation: Rotate around fixed point (legacy, prefer Bend)
-- | - Starch: Define rigid areas that resist deformation
-- | - Overlap: Control depth/z-order during deformation
-- | - Bend: Rotation + scale at joints
-- | - Advanced: Full transform control

module Hydrogen.Schema.Motion.MeshWarp
  ( -- * Enumerations
    WarpPinType(..)
  , warpPinTypeToString
  , warpPinTypeFromString
  , warpPinTypeUsesPosition
  , warpPinTypeUsesRotation
  , warpPinTypeUsesScale
  , warpPinTypeUsesStiffness
  , warpPinTypeUsesOverlap
  , warpPinTypeDefaultStiffness
  
  , WarpWeightMethod(..)
  , warpWeightMethodToString
  , warpWeightMethodFromString
  
  -- * Warp Pin
  , WarpPin(..)
  , WarpPinId(..)
  , mkWarpPinId
  , defaultWarpPin
  
  -- * Warp Pin Rest State
  , WarpPinRestState(..)
  , mkWarpPinRestState
  
  -- * Warp Mesh
  , WarpMesh(..)
  , mkWarpMesh
  , warpMeshVertexCount
  , warpMeshIsDirty
  , warpMeshMarkDirty
  , warpMeshMarkClean
  
  -- * Deformation Result
  , DeformedControlPoint(..)
  , WarpDeformationResult(..)
  
  -- * Weight Options
  , WarpWeightOptions(..)
  , defaultWarpWeightOptions
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Motion.Layer (LayerId)
import Hydrogen.Schema.Motion.Property (AnimatablePropertyId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // warp // pin // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of warp pin controlling how it deforms the mesh.
-- |
-- | Each pin type enables different properties for animation:
-- | - Position pins move vertices
-- | - Starch pins create rigid areas
-- | - Bend pins allow rotation and scale at joints
data WarpPinType
  = WPTPosition   -- ^ Move mesh vertices by animating position
  | WPTRotation   -- ^ Rotate around fixed point (legacy, prefer Bend)
  | WPTStarch     -- ^ Define rigid areas that resist deformation
  | WPTOverlap    -- ^ Control depth/z-order during deformation
  | WPTBend       -- ^ Rotation + scale at joints
  | WPTAdvanced   -- ^ Full transform control

derive instance eqWarpPinType :: Eq WarpPinType
derive instance ordWarpPinType :: Ord WarpPinType

instance showWarpPinType :: Show WarpPinType where
  show WPTPosition = "WPTPosition"
  show WPTRotation = "WPTRotation"
  show WPTStarch = "WPTStarch"
  show WPTOverlap = "WPTOverlap"
  show WPTBend = "WPTBend"
  show WPTAdvanced = "WPTAdvanced"

-- | Convert pin type to display string.
warpPinTypeToString :: WarpPinType -> String
warpPinTypeToString WPTPosition = "position"
warpPinTypeToString WPTRotation = "rotation"
warpPinTypeToString WPTStarch = "starch"
warpPinTypeToString WPTOverlap = "overlap"
warpPinTypeToString WPTBend = "bend"
warpPinTypeToString WPTAdvanced = "advanced"

-- | Parse pin type from string.
warpPinTypeFromString :: String -> Maybe WarpPinType
warpPinTypeFromString "position" = Just WPTPosition
warpPinTypeFromString "rotation" = Just WPTRotation
warpPinTypeFromString "starch" = Just WPTStarch
warpPinTypeFromString "overlap" = Just WPTOverlap
warpPinTypeFromString "bend" = Just WPTBend
warpPinTypeFromString "advanced" = Just WPTAdvanced
warpPinTypeFromString _ = Nothing

-- | Check if pin type uses position animation.
warpPinTypeUsesPosition :: WarpPinType -> Boolean
warpPinTypeUsesPosition WPTPosition = true
warpPinTypeUsesPosition WPTAdvanced = true
warpPinTypeUsesPosition _ = false

-- | Check if pin type uses rotation animation.
warpPinTypeUsesRotation :: WarpPinType -> Boolean
warpPinTypeUsesRotation WPTRotation = true
warpPinTypeUsesRotation WPTBend = true
warpPinTypeUsesRotation WPTAdvanced = true
warpPinTypeUsesRotation _ = false

-- | Check if pin type uses scale animation.
warpPinTypeUsesScale :: WarpPinType -> Boolean
warpPinTypeUsesScale WPTBend = true
warpPinTypeUsesScale WPTAdvanced = true
warpPinTypeUsesScale _ = false

-- | Check if pin type uses stiffness.
warpPinTypeUsesStiffness :: WarpPinType -> Boolean
warpPinTypeUsesStiffness WPTStarch = true
warpPinTypeUsesStiffness _ = false

-- | Check if pin type uses overlap depth.
warpPinTypeUsesOverlap :: WarpPinType -> Boolean
warpPinTypeUsesOverlap WPTOverlap = true
warpPinTypeUsesOverlap _ = false

-- | Get default stiffness for pin type.
-- | Starch pins default to maximum stiffness (1.0), others to none (0.0).
warpPinTypeDefaultStiffness :: WarpPinType -> Number
warpPinTypeDefaultStiffness WPTStarch = 1.0
warpPinTypeDefaultStiffness _ = 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // warp // weight // method
-- ═════════════════════════════════════════════════════════════════════════════

-- | Method for calculating pin influence weights on mesh vertices.
data WarpWeightMethod
  = WWMInverseDistance  -- ^ Standard 1/d^n falloff
  | WWMHeatDiffusion    -- ^ Heat equation simulation
  | WWMRadialBasis      -- ^ RBF interpolation
  | WWMBounded          -- ^ Bounded biharmonic weights

derive instance eqWarpWeightMethod :: Eq WarpWeightMethod
derive instance ordWarpWeightMethod :: Ord WarpWeightMethod

instance showWarpWeightMethod :: Show WarpWeightMethod where
  show WWMInverseDistance = "WWMInverseDistance"
  show WWMHeatDiffusion = "WWMHeatDiffusion"
  show WWMRadialBasis = "WWMRadialBasis"
  show WWMBounded = "WWMBounded"

-- | Convert weight method to display string.
warpWeightMethodToString :: WarpWeightMethod -> String
warpWeightMethodToString WWMInverseDistance = "inverse-distance"
warpWeightMethodToString WWMHeatDiffusion = "heat-diffusion"
warpWeightMethodToString WWMRadialBasis = "radial-basis"
warpWeightMethodToString WWMBounded = "bounded"

-- | Parse weight method from string.
warpWeightMethodFromString :: String -> Maybe WarpWeightMethod
warpWeightMethodFromString "inverse-distance" = Just WWMInverseDistance
warpWeightMethodFromString "heat-diffusion" = Just WWMHeatDiffusion
warpWeightMethodFromString "radial-basis" = Just WWMRadialBasis
warpWeightMethodFromString "bounded" = Just WWMBounded
warpWeightMethodFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // warp // pin // id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a warp pin.
newtype WarpPinId = WarpPinId String

derive instance eqWarpPinId :: Eq WarpPinId
derive instance ordWarpPinId :: Ord WarpPinId

instance showWarpPinId :: Show WarpPinId where
  show (WarpPinId s) = "(WarpPinId " <> show s <> ")"

-- | Smart constructor for WarpPinId.
-- | Returns Nothing for empty strings.
mkWarpPinId :: String -> Maybe WarpPinId
mkWarpPinId "" = Nothing
mkWarpPinId s = Just (WarpPinId s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // warp // pin
-- ═════════════════════════════════════════════════════════════════════════════

-- | A control pin for mesh warp deformation.
-- |
-- | Pins are placed on the mesh and animated to deform the underlying geometry.
-- | The pin's position, rotation, and scale are stored as AnimatablePropertyIds
-- | referencing external property tracks.
type WarpPin =
  { id :: WarpPinId
  , name :: String
  , pinType :: WarpPinType
  , positionPropId :: AnimatablePropertyId    -- ^ AnimatableProperty ID for position
  , radius :: Number                          -- ^ Influence radius in pixels (positive)
  , stiffness :: Number                       -- ^ Stiffness/rigidity (0-1)
  , rotationPropId :: AnimatablePropertyId    -- ^ AnimatableProperty ID for rotation
  , scalePropId :: AnimatablePropertyId       -- ^ AnimatableProperty ID for scale
  , depth :: Number                           -- ^ Pin depth/priority
  , selected :: Boolean
  , inFrontPropId :: Maybe AnimatablePropertyId  -- ^ AnimatableProperty ID for overlap depth
  }

-- | Default warp pin configuration.
-- |
-- | Creates a position pin with standard radius and no stiffness.
defaultWarpPin 
  :: WarpPinId 
  -> AnimatablePropertyId 
  -> AnimatablePropertyId 
  -> AnimatablePropertyId 
  -> WarpPin
defaultWarpPin pinId posProp rotProp scaleProp =
  { id: pinId
  , name: "Pin"
  , pinType: WPTPosition
  , positionPropId: posProp
  , radius: 50.0
  , stiffness: 0.0
  , rotationPropId: rotProp
  , scalePropId: scaleProp
  , depth: 0.0
  , selected: false
  , inFrontPropId: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // warp // pin // rest // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Initial/rest state of a pin before animation.
-- |
-- | Stores the original transform values for computing deltas.
type WarpPinRestState =
  { id :: WarpPinId
  , positionX :: Number
  , positionY :: Number
  , rotation :: Number
  , scale :: Number
  , inFront :: Maybe Number
  }

-- | Create a pin rest state at origin with identity transform.
mkWarpPinRestState :: WarpPinId -> WarpPinRestState
mkWarpPinRestState pinId =
  { id: pinId
  , positionX: 0.0
  , positionY: 0.0
  , rotation: 0.0
  , scale: 1.0
  , inFront: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // warp // mesh
-- ═════════════════════════════════════════════════════════════════════════════

-- | A triangulated mesh for warp deformation.
-- |
-- | The mesh is generated from the layer's shape and subdivided into triangles.
-- | Pin weights are computed per-vertex to enable smooth deformation.
type WarpMesh =
  { layerId :: LayerId
  , pins :: Array WarpPin
  , triangulation :: Array Int               -- ^ Triangle indices (triplets)
  , weights :: Array Number                  -- ^ Pin influence weights per vertex
  , originalVertices :: Array Number         -- ^ Original vertex positions (x,y pairs)
  , pinRestStates :: Array WarpPinRestState
  , vertexCount :: Int
  , dirty :: Boolean                         -- ^ Needs recalculation
  }

-- | Create an empty warp mesh for a layer.
mkWarpMesh :: LayerId -> WarpMesh
mkWarpMesh lid =
  { layerId: lid
  , pins: []
  , triangulation: []
  , weights: []
  , originalVertices: []
  , pinRestStates: []
  , vertexCount: 0
  , dirty: false
  }

-- | Get the vertex count of the mesh.
warpMeshVertexCount :: WarpMesh -> Int
warpMeshVertexCount mesh = mesh.vertexCount

-- | Check if mesh needs recalculation.
warpMeshIsDirty :: WarpMesh -> Boolean
warpMeshIsDirty mesh = mesh.dirty

-- | Mark mesh as needing recalculation.
warpMeshMarkDirty :: WarpMesh -> WarpMesh
warpMeshMarkDirty mesh = mesh { dirty = true }

-- | Mark mesh as up-to-date.
warpMeshMarkClean :: WarpMesh -> WarpMesh
warpMeshMarkClean mesh = mesh { dirty = false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // deformation // result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Control point with bezier handles for path reconstruction.
-- |
-- | After deformation, paths need their control points and handles
-- | transformed to maintain smooth curves.
type DeformedControlPoint =
  { x :: Number
  , y :: Number
  , inHandleX :: Number
  , inHandleY :: Number
  , outHandleX :: Number
  , outHandleY :: Number
  }

-- | Result of deforming a mesh.
-- |
-- | Contains both the deformed vertex positions and the reconstructed
-- | control points for any bezier paths in the original shape.
type WarpDeformationResult =
  { vertices :: Array Number         -- ^ Deformed vertex positions (x,y pairs)
  , controlPoints :: Array DeformedControlPoint
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // weight // options
-- ═════════════════════════════════════════════════════════════════════════════

-- | Options for calculating pin influence weights.
type WarpWeightOptions =
  { method :: WarpWeightMethod
  , falloffPower :: Number          -- ^ Falloff power for inverse-distance (typically 2)
  , normalize :: Boolean            -- ^ Whether to normalize weights to sum to 1
  , minWeight :: Number             -- ^ Minimum weight threshold (non-negative)
  }

-- | Default weight options using inverse-distance with power 2.
defaultWarpWeightOptions :: WarpWeightOptions
defaultWarpWeightOptions =
  { method: WWMInverseDistance
  , falloffPower: 2.0
  , normalize: true
  , minWeight: 0.001
  }
