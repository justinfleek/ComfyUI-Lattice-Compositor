{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.MeshWarp
Description : Mesh warp deformation types
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/MeshWarp.lean

Provides vector skinning-style deformation for spline layers,
allowing organic animation by manipulating control pins.
-}

module Lattice.MeshWarp
  ( -- * Enumerations
    WarpPinType(..)
  , WarpWeightMethod(..)
    -- * Warp Pin
  , WarpPin(..)
  , WarpPinRestState(..)
    -- * Warp Mesh
  , WarpMesh(..)
    -- * Deformation
  , DeformedControlPoint(..)
  , WarpDeformationResult(..)
    -- * Options
  , WarpWeightOptions(..)
    -- * Pin Type Helpers
  , warpPinTypeUsesPosition
  , warpPinTypeUsesRotation
  , warpPinTypeUsesScale
  , warpPinTypeUsesStiffness
  , warpPinTypeUsesOverlap
  , warpPinTypeDefaultStiffness
  ) where

import GHC.Generics (Generic)
import Data.Vector (Vector)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Pin Type Enum
--------------------------------------------------------------------------------

-- | Type of warp pin
data WarpPinType
  = WPTPosition   -- ^ Deform pin: Move mesh vertices by animating position
  | WPTRotation   -- ^ Rotation pin: Rotate around fixed point (legacy, use 'bend')
  | WPTStarch     -- ^ Stiffness pin: Define rigid areas that resist deformation
  | WPTOverlap    -- ^ Overlap pin: Control depth/z-order during deformation
  | WPTBend       -- ^ Bend pin: Rotation + scale at joints
  | WPTAdvanced   -- ^ Advanced pin: Full transform control
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Weight Method Enum
--------------------------------------------------------------------------------

-- | Method for calculating pin influence weights
data WarpWeightMethod
  = WWMInverseDistance  -- ^ Standard 1/d^n falloff
  | WWMHeatDiffusion    -- ^ Heat equation simulation
  | WWMRadialBasis      -- ^ RBF interpolation
  | WWMBounded          -- ^ Bounded biharmonic weights
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Warp Pin
--------------------------------------------------------------------------------

-- | A control pin for mesh warp deformation
data WarpPin = WarpPin
  { wpId        :: !NonEmptyString
  , wpName      :: !NonEmptyString
  , wpPinType   :: !WarpPinType
  , wpPosition  :: !NonEmptyString  -- ^ AnimatableProperty ID for position
  , wpRadius    :: !PositiveFloat   -- ^ Influence radius in pixels
  , wpStiffness :: !UnitFloat       -- ^ Stiffness/rigidity (0-1)
  , wpRotation  :: !NonEmptyString  -- ^ AnimatableProperty ID for rotation
  , wpScale     :: !NonEmptyString  -- ^ AnimatableProperty ID for scale
  , wpDepth     :: !FiniteFloat     -- ^ Pin depth/priority
  , wpSelected  :: !Bool
  , wpInFront   :: !(Maybe NonEmptyString)  -- ^ AnimatableProperty ID for overlap depth
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Pin Rest State
--------------------------------------------------------------------------------

-- | Initial/rest state of a pin (before animation)
data WarpPinRestState = WarpPinRestState
  { wprsId        :: !NonEmptyString
  , wprsPositionX :: !FiniteFloat
  , wprsPositionY :: !FiniteFloat
  , wprsRotation  :: !FiniteFloat
  , wprsScale     :: !FiniteFloat
  , wprsInFront   :: !(Maybe FiniteFloat)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Warp Mesh
--------------------------------------------------------------------------------

-- | A triangulated mesh for warp deformation
data WarpMesh = WarpMesh
  { wmLayerId          :: !NonEmptyString
  , wmPins             :: !(Vector WarpPin)
  , wmTriangulation    :: !(Vector Int)           -- ^ Triangle indices (triplets)
  , wmWeights          :: !(Vector FiniteFloat)   -- ^ Pin influence weights per vertex
  , wmOriginalVertices :: !(Vector FiniteFloat)   -- ^ Original vertex positions
  , wmPinRestStates    :: !(Vector WarpPinRestState)
  , wmVertexCount      :: !Int
  , wmDirty            :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Deformation Result
--------------------------------------------------------------------------------

-- | Control point with handles (for path reconstruction)
data DeformedControlPoint = DeformedControlPoint
  { dcpX          :: !FiniteFloat
  , dcpY          :: !FiniteFloat
  , dcpInHandleX  :: !FiniteFloat
  , dcpInHandleY  :: !FiniteFloat
  , dcpOutHandleX :: !FiniteFloat
  , dcpOutHandleY :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

-- | Result of deforming a mesh
data WarpDeformationResult = WarpDeformationResult
  { wdrVertices      :: !(Vector FiniteFloat)
  , wdrControlPoints :: !(Vector DeformedControlPoint)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Weight Options
--------------------------------------------------------------------------------

-- | Options for weight calculation
data WarpWeightOptions = WarpWeightOptions
  { wwoMethod       :: !WarpWeightMethod
  , wwoFalloffPower :: !PositiveFloat     -- ^ Falloff power for inverse-distance (typically 2)
  , wwoNormalize    :: !Bool              -- ^ Whether to normalize weights to sum to 1
  , wwoMinWeight    :: !NonNegativeFloat  -- ^ Minimum weight threshold
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Pin Type Helpers
--------------------------------------------------------------------------------

-- | Check if pin type uses position animation
warpPinTypeUsesPosition :: WarpPinType -> Bool
warpPinTypeUsesPosition WPTPosition = True
warpPinTypeUsesPosition WPTAdvanced = True
warpPinTypeUsesPosition _           = False

-- | Check if pin type uses rotation animation
warpPinTypeUsesRotation :: WarpPinType -> Bool
warpPinTypeUsesRotation WPTRotation = True
warpPinTypeUsesRotation WPTBend     = True
warpPinTypeUsesRotation WPTAdvanced = True
warpPinTypeUsesRotation _           = False

-- | Check if pin type uses scale animation
warpPinTypeUsesScale :: WarpPinType -> Bool
warpPinTypeUsesScale WPTBend     = True
warpPinTypeUsesScale WPTAdvanced = True
warpPinTypeUsesScale _           = False

-- | Check if pin type uses stiffness
warpPinTypeUsesStiffness :: WarpPinType -> Bool
warpPinTypeUsesStiffness WPTStarch = True
warpPinTypeUsesStiffness _         = False

-- | Check if pin type uses overlap depth
warpPinTypeUsesOverlap :: WarpPinType -> Bool
warpPinTypeUsesOverlap WPTOverlap = True
warpPinTypeUsesOverlap _          = False

-- | Get default stiffness for pin type
warpPinTypeDefaultStiffness :: WarpPinType -> Double
warpPinTypeDefaultStiffness WPTStarch = 1.0
warpPinTypeDefaultStiffness _         = 0.0
