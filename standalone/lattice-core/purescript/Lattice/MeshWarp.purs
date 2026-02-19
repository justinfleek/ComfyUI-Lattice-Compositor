-- | Lattice.MeshWarp - Mesh warp deformation types
-- |
-- | Source: lattice-core/lean/Lattice/MeshWarp.lean
-- |
-- | Provides vector skinning-style deformation for spline layers,
-- | allowing organic animation by manipulating control pins.

module Lattice.MeshWarp
  ( WarpPinType(..)
  , WarpWeightMethod(..)
  , WarpPin
  , WarpPinRestState
  , WarpMesh
  , DeformedControlPoint
  , WarpDeformationResult
  , WarpWeightOptions
  , warpPinTypeUsesPosition
  , warpPinTypeUsesRotation
  , warpPinTypeUsesScale
  , warpPinTypeUsesStiffness
  , warpPinTypeUsesOverlap
  , warpPinTypeDefaultStiffness
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Pin Type Enum
--------------------------------------------------------------------------------

-- | Type of warp pin
data WarpPinType
  = WPTPosition   -- Deform pin: Move mesh vertices by animating position
  | WPTRotation   -- Rotation pin: Rotate around fixed point (legacy)
  | WPTStarch     -- Stiffness pin: Define rigid areas
  | WPTOverlap    -- Overlap pin: Control depth/z-order
  | WPTBend       -- Bend pin: Rotation + scale at joints
  | WPTAdvanced   -- Advanced pin: Full transform control

derive instance Eq WarpPinType
derive instance Generic WarpPinType _
instance Show WarpPinType where show = genericShow

--------------------------------------------------------------------------------
-- Weight Method Enum
--------------------------------------------------------------------------------

-- | Method for calculating pin influence weights
data WarpWeightMethod
  = WWMInverseDistance  -- Standard 1/d^n falloff
  | WWMHeatDiffusion    -- Heat equation simulation
  | WWMRadialBasis      -- RBF interpolation
  | WWMBounded          -- Bounded biharmonic weights

derive instance Eq WarpWeightMethod
derive instance Generic WarpWeightMethod _
instance Show WarpWeightMethod where show = genericShow

--------------------------------------------------------------------------------
-- Warp Pin
--------------------------------------------------------------------------------

-- | A control pin for mesh warp deformation
type WarpPin =
  { id        :: NonEmptyString
  , name      :: NonEmptyString
  , pinType   :: WarpPinType
  , position  :: NonEmptyString  -- AnimatableProperty ID for position
  , radius    :: PositiveFloat   -- Influence radius in pixels
  , stiffness :: UnitFloat       -- Stiffness/rigidity (0-1)
  , rotation  :: NonEmptyString  -- AnimatableProperty ID for rotation
  , scale     :: NonEmptyString  -- AnimatableProperty ID for scale
  , depth     :: FiniteFloat     -- Pin depth/priority
  , selected  :: Boolean
  , inFront   :: Maybe NonEmptyString  -- AnimatableProperty ID for overlap depth
  }

--------------------------------------------------------------------------------
-- Pin Rest State
--------------------------------------------------------------------------------

-- | Initial/rest state of a pin (before animation)
type WarpPinRestState =
  { pinId     :: NonEmptyString
  , positionX :: FiniteFloat
  , positionY :: FiniteFloat
  , rotation  :: FiniteFloat
  , scale     :: FiniteFloat
  , inFront   :: Maybe FiniteFloat
  }

--------------------------------------------------------------------------------
-- Warp Mesh
--------------------------------------------------------------------------------

-- | A triangulated mesh for warp deformation
type WarpMesh =
  { layerId          :: NonEmptyString
  , pins             :: Array WarpPin
  , triangulation    :: Array Int           -- Triangle indices (triplets)
  , weights          :: Array FiniteFloat   -- Pin influence weights per vertex
  , originalVertices :: Array FiniteFloat   -- Original vertex positions
  , pinRestStates    :: Array WarpPinRestState
  , vertexCount      :: Int
  , dirty            :: Boolean
  }

--------------------------------------------------------------------------------
-- Deformation Result
--------------------------------------------------------------------------------

-- | Control point with handles (for path reconstruction)
type DeformedControlPoint =
  { x          :: FiniteFloat
  , y          :: FiniteFloat
  , inHandleX  :: FiniteFloat
  , inHandleY  :: FiniteFloat
  , outHandleX :: FiniteFloat
  , outHandleY :: FiniteFloat
  }

-- | Result of deforming a mesh
type WarpDeformationResult =
  { vertices      :: Array FiniteFloat
  , controlPoints :: Array DeformedControlPoint
  }

--------------------------------------------------------------------------------
-- Weight Options
--------------------------------------------------------------------------------

-- | Options for weight calculation
type WarpWeightOptions =
  { method       :: WarpWeightMethod
  , falloffPower :: PositiveFloat     -- Falloff power for inverse-distance (typically 2)
  , normalize    :: Boolean           -- Whether to normalize weights to sum to 1
  , minWeight    :: NonNegativeFloat  -- Minimum weight threshold
  }

--------------------------------------------------------------------------------
-- Pin Type Helpers
--------------------------------------------------------------------------------

-- | Check if pin type uses position animation
warpPinTypeUsesPosition :: WarpPinType -> Boolean
warpPinTypeUsesPosition WPTPosition = true
warpPinTypeUsesPosition WPTAdvanced = true
warpPinTypeUsesPosition _           = false

-- | Check if pin type uses rotation animation
warpPinTypeUsesRotation :: WarpPinType -> Boolean
warpPinTypeUsesRotation WPTRotation = true
warpPinTypeUsesRotation WPTBend     = true
warpPinTypeUsesRotation WPTAdvanced = true
warpPinTypeUsesRotation _           = false

-- | Check if pin type uses scale animation
warpPinTypeUsesScale :: WarpPinType -> Boolean
warpPinTypeUsesScale WPTBend     = true
warpPinTypeUsesScale WPTAdvanced = true
warpPinTypeUsesScale _           = false

-- | Check if pin type uses stiffness
warpPinTypeUsesStiffness :: WarpPinType -> Boolean
warpPinTypeUsesStiffness WPTStarch = true
warpPinTypeUsesStiffness _         = false

-- | Check if pin type uses overlap depth
warpPinTypeUsesOverlap :: WarpPinType -> Boolean
warpPinTypeUsesOverlap WPTOverlap = true
warpPinTypeUsesOverlap _          = false

-- | Get default stiffness for pin type
warpPinTypeDefaultStiffness :: WarpPinType -> Number
warpPinTypeDefaultStiffness WPTStarch = 1.0
warpPinTypeDefaultStiffness _         = 0.0
