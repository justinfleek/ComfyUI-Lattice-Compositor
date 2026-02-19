{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Particles
Description : Particle system types
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/Particles.lean
Consolidated from Particles/* submodules.
-}

module Lattice.Particles
  ( -- * Enumerations
    EmitterShape(..)
  , BoundaryBehavior(..)
  , ParticleShape(..)
  , ParticleBlendMode(..)
  , BuiltinShape(..)
  , ParticleTextureType(..)
  , ParticleFalloff(..)
  , SPHPreset(..)
  , SpringStructureType(..)
  , SpritePlayMode(..)
  , SplineEmitMode(..)
  , DepthMode(..)
  , MaskChannel(..)
  , SubEmitterTrigger(..)
  , AudioFeatureName(..)
  , AudioTargetType(..)
  , AudioCurveType(..)
  , AudioTriggerMode(..)
  , ModulationProperty(..)
  , AudioMappingParameter(..)
  , MeshMode(..)
  , MeshGeometry(..)
  , FloorBehavior(..)
    -- * Core Types
  , ParticleVec3(..)
  , ParticleEmitterConfig(..)
  , ParticleRenderOptions(..)
  , ParticleModulationConfig(..)
  , ParticleLayerData(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Emitter Shapes
--------------------------------------------------------------------------------

data EmitterShape
  = ESPoint | ESLine | ESCircle | ESBox | ESSphere | ESRing | ESSpline
  | ESDepthMap | ESMask | ESCone | ESImage | ESDepthEdge | ESMesh
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Boundary Behaviors
--------------------------------------------------------------------------------

data BoundaryBehavior = BBBounce | BBKill | BBWrap | BBStick | BBNone
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Particle Shape
--------------------------------------------------------------------------------

data ParticleShape = PSCircle | PSSquare | PSTriangle | PSStar
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Blend Mode
--------------------------------------------------------------------------------

data ParticleBlendMode = PBMNormal | PBMAdditive | PBMMultiply | PBMScreen
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Builtin Shapes
--------------------------------------------------------------------------------

data BuiltinShape = BSCircle | BSSquare | BSStar | BSSpark | BSSmoke
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Texture Types
--------------------------------------------------------------------------------

data ParticleTextureType = PTTBuiltin | PTTImage | PTTGenerated | PTTExtracted
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Falloff
--------------------------------------------------------------------------------

data ParticleFalloff = PFLinear | PFQuadratic | PFConstant
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- SPH Preset
--------------------------------------------------------------------------------

data SPHPreset = SPHWater | SPHHoney | SPHLava | SPHGas | SPHCustom
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Spring Structure Type
--------------------------------------------------------------------------------

data SpringStructureType = SSTCloth | SSTRope | SSTSoftbody | SSTCustom
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Sprite Play Mode
--------------------------------------------------------------------------------

data SpritePlayMode = SPMLoop | SPMOnce | SPMPingpong | SPMRandom
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Spline Emit Mode
--------------------------------------------------------------------------------

data SplineEmitMode
  = SEMUniform | SEMRandom | SEMStart | SEMEnd | SEMSequential
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Depth Mode
--------------------------------------------------------------------------------

data DepthMode = DMNearWhite | DMNearBlack
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Mask Channel
--------------------------------------------------------------------------------

data MaskChannel = MCLuminance | MCAlpha | MCRed | MCGreen | MCBlue
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Sub Emitter Trigger
--------------------------------------------------------------------------------

data SubEmitterTrigger = SETDeath
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Audio Features
--------------------------------------------------------------------------------

data AudioFeatureName
  = AFNAmplitude | AFNBass | AFNMid | AFNHigh | AFNBeat
  | AFNSpectralCentroid | AFNRMS | AFNOnsets
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Audio Target
--------------------------------------------------------------------------------

data AudioTargetType = ATTEmitter | ATTSystem | ATTForceField
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Audio Curve
--------------------------------------------------------------------------------

data AudioCurveType = ACTLinear | ACTExponential | ACTLogarithmic | ACTStep
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Audio Trigger Mode
--------------------------------------------------------------------------------

data AudioTriggerMode = ATMContinuous | ATMOnThreshold | ATMOnBeat
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Modulation Property
--------------------------------------------------------------------------------

data ModulationProperty
  = MPSize | MPSpeed | MPOpacity | MPColorR | MPColorG | MPColorB
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Audio Mapping Parameter
--------------------------------------------------------------------------------

data AudioMappingParameter
  = AMPEmissionRate | AMPSpeed | AMPSize | AMPGravity | AMPWindStrength
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Mesh Mode
--------------------------------------------------------------------------------

data MeshMode = MMMBillboard | MMMMesh
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Mesh Geometry
--------------------------------------------------------------------------------

data MeshGeometry
  = MGCube | MGSphere | MGCylinder | MGCone | MGTorus | MGCustom
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Floor Behavior
--------------------------------------------------------------------------------

data FloorBehavior = FBNone | FBBounce | FBStick | FBKill
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Core Types
--------------------------------------------------------------------------------

data ParticleVec3 = ParticleVec3
  { pv3X :: !FiniteFloat
  , pv3Y :: !FiniteFloat
  , pv3Z :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

data ParticleEmitterConfig = ParticleEmitterConfig
  { pecId               :: !NonEmptyString
  , pecName             :: !NonEmptyString
  , pecEnabled          :: !Bool
  , pecShape            :: !EmitterShape
  , pecPosition         :: !ParticleVec3
  , pecEmissionRate     :: !PositiveFloat
  , pecMaxParticles     :: !Int
  , pecLifespanMin      :: !PositiveFloat
  , pecLifespanMax      :: !PositiveFloat
  , pecSpeedMin         :: !NonNegativeFloat
  , pecSpeedMax         :: !NonNegativeFloat
  , pecDirection        :: !ParticleVec3
  , pecSpread           :: !FiniteFloat  -- Degrees
  , pecSizeMin          :: !PositiveFloat
  , pecSizeMax          :: !PositiveFloat
  , pecColorStart       :: !Text  -- Hex color
  , pecColorEnd         :: !Text  -- Hex color
  , pecOpacityStart     :: !UnitFloat
  , pecOpacityEnd       :: !UnitFloat
  , pecGravity          :: !ParticleVec3
  , pecBoundaryBehavior :: !BoundaryBehavior
  } deriving stock (Eq, Show, Generic)

data ParticleRenderOptions = ParticleRenderOptions
  { proShape          :: !ParticleShape
  , proBlendMode      :: !ParticleBlendMode
  , proSortByDepth    :: !Bool
  , proDepthWrite     :: !Bool
  , proTextureType    :: !ParticleTextureType
  , proBuiltinShape   :: !(Maybe BuiltinShape)
  , proTextureAssetId :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

data ParticleModulationConfig = ParticleModulationConfig
  { pmcId       :: !NonEmptyString
  , pmcEnabled  :: !Bool
  , pmcProperty :: !ModulationProperty
  , pmcCurve    :: !(Vector (FiniteFloat, FiniteFloat))  -- (time, value) pairs
  } deriving stock (Eq, Show, Generic)

data ParticleLayerData = ParticleLayerData
  { pldEmitters       :: !(Vector ParticleEmitterConfig)
  , pldRenderOptions  :: !ParticleRenderOptions
  , pldModulations    :: !(Vector ParticleModulationConfig)
  , pldExportEnabled  :: !Bool
  , pldExportFormat   :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)
