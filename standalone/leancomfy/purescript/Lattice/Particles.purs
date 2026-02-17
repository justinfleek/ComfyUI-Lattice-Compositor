-- | Lattice.Particles - Particle system types
-- |
-- | Source: leancomfy/lean/Lattice/Particles.lean
-- | Consolidated from Particles/* submodules.

module Lattice.Particles
  ( EmitterShape(..)
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
  , ParticleVec3
  , ParticleEmitterConfig
  , ParticleRenderOptions
  , ParticleModulationConfig
  , ParticleLayerData
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data EmitterShape
  = ESPoint | ESLine | ESCircle | ESBox | ESSphere | ESRing | ESSpline
  | ESDepthMap | ESMask | ESCone | ESImage | ESDepthEdge | ESMesh

derive instance Eq EmitterShape
derive instance Generic EmitterShape _
instance Show EmitterShape where show = genericShow

data BoundaryBehavior = BBBounce | BBKill | BBWrap | BBStick | BBNone

derive instance Eq BoundaryBehavior
derive instance Generic BoundaryBehavior _
instance Show BoundaryBehavior where show = genericShow

data ParticleShape = PSCircle | PSSquare | PSTriangle | PSStar

derive instance Eq ParticleShape
derive instance Generic ParticleShape _
instance Show ParticleShape where show = genericShow

data ParticleBlendMode = PBMNormal | PBMAdditive | PBMMultiply | PBMScreen

derive instance Eq ParticleBlendMode
derive instance Generic ParticleBlendMode _
instance Show ParticleBlendMode where show = genericShow

data BuiltinShape = BSCircle | BSSquare | BSStar | BSSpark | BSSmoke

derive instance Eq BuiltinShape
derive instance Generic BuiltinShape _
instance Show BuiltinShape where show = genericShow

data ParticleTextureType = PTTBuiltin | PTTImage | PTTGenerated | PTTExtracted

derive instance Eq ParticleTextureType
derive instance Generic ParticleTextureType _
instance Show ParticleTextureType where show = genericShow

data ParticleFalloff = PFLinear | PFQuadratic | PFConstant

derive instance Eq ParticleFalloff
derive instance Generic ParticleFalloff _
instance Show ParticleFalloff where show = genericShow

data SPHPreset = SPHWater | SPHHoney | SPHLava | SPHGas | SPHCustom

derive instance Eq SPHPreset
derive instance Generic SPHPreset _
instance Show SPHPreset where show = genericShow

data SpringStructureType = SSTCloth | SSTRope | SSTSoftbody | SSTCustom

derive instance Eq SpringStructureType
derive instance Generic SpringStructureType _
instance Show SpringStructureType where show = genericShow

data SpritePlayMode = SPMLoop | SPMOnce | SPMPingpong | SPMRandom

derive instance Eq SpritePlayMode
derive instance Generic SpritePlayMode _
instance Show SpritePlayMode where show = genericShow

data SplineEmitMode
  = SEMUniform | SEMRandom | SEMStart | SEMEnd | SEMSequential

derive instance Eq SplineEmitMode
derive instance Generic SplineEmitMode _
instance Show SplineEmitMode where show = genericShow

data DepthMode = DMNearWhite | DMNearBlack

derive instance Eq DepthMode
derive instance Generic DepthMode _
instance Show DepthMode where show = genericShow

data MaskChannel = MCLuminance | MCAlpha | MCRed | MCGreen | MCBlue

derive instance Eq MaskChannel
derive instance Generic MaskChannel _
instance Show MaskChannel where show = genericShow

data SubEmitterTrigger = SETDeath

derive instance Eq SubEmitterTrigger
derive instance Generic SubEmitterTrigger _
instance Show SubEmitterTrigger where show = genericShow

data AudioFeatureName
  = AFNAmplitude | AFNBass | AFNMid | AFNHigh | AFNBeat
  | AFNSpectralCentroid | AFNRMS | AFNOnsets

derive instance Eq AudioFeatureName
derive instance Generic AudioFeatureName _
instance Show AudioFeatureName where show = genericShow

data AudioTargetType = ATTEmitter | ATTSystem | ATTForceField

derive instance Eq AudioTargetType
derive instance Generic AudioTargetType _
instance Show AudioTargetType where show = genericShow

data AudioCurveType = ACTLinear | ACTExponential | ACTLogarithmic | ACTStep

derive instance Eq AudioCurveType
derive instance Generic AudioCurveType _
instance Show AudioCurveType where show = genericShow

data AudioTriggerMode = ATMContinuous | ATMOnThreshold | ATMOnBeat

derive instance Eq AudioTriggerMode
derive instance Generic AudioTriggerMode _
instance Show AudioTriggerMode where show = genericShow

data ModulationProperty
  = MPSize | MPSpeed | MPOpacity | MPColorR | MPColorG | MPColorB

derive instance Eq ModulationProperty
derive instance Generic ModulationProperty _
instance Show ModulationProperty where show = genericShow

data AudioMappingParameter
  = AMPEmissionRate | AMPSpeed | AMPSize | AMPGravity | AMPWindStrength

derive instance Eq AudioMappingParameter
derive instance Generic AudioMappingParameter _
instance Show AudioMappingParameter where show = genericShow

data MeshMode = MMMBillboard | MMMMesh

derive instance Eq MeshMode
derive instance Generic MeshMode _
instance Show MeshMode where show = genericShow

data MeshGeometry
  = MGCube | MGSphere | MGCylinder | MGCone | MGTorus | MGCustom

derive instance Eq MeshGeometry
derive instance Generic MeshGeometry _
instance Show MeshGeometry where show = genericShow

data FloorBehavior = FBNone | FBBounce | FBStick | FBKill

derive instance Eq FloorBehavior
derive instance Generic FloorBehavior _
instance Show FloorBehavior where show = genericShow

--------------------------------------------------------------------------------
-- Core Types
--------------------------------------------------------------------------------

type ParticleVec3 =
  { x :: FiniteFloat
  , y :: FiniteFloat
  , z :: FiniteFloat
  }

type ParticleEmitterConfig =
  { id               :: NonEmptyString
  , name             :: NonEmptyString
  , enabled          :: Boolean
  , shape            :: EmitterShape
  , position         :: ParticleVec3
  , emissionRate     :: PositiveFloat
  , maxParticles     :: Int
  , lifespanMin      :: PositiveFloat
  , lifespanMax      :: PositiveFloat
  , speedMin         :: NonNegativeFloat
  , speedMax         :: NonNegativeFloat
  , direction        :: ParticleVec3
  , spread           :: FiniteFloat  -- Degrees
  , sizeMin          :: PositiveFloat
  , sizeMax          :: PositiveFloat
  , colorStart       :: String  -- Hex color
  , colorEnd         :: String  -- Hex color
  , opacityStart     :: UnitFloat
  , opacityEnd       :: UnitFloat
  , gravity          :: ParticleVec3
  , boundaryBehavior :: BoundaryBehavior
  }

type ParticleRenderOptions =
  { shape          :: ParticleShape
  , blendMode      :: ParticleBlendMode
  , sortByDepth    :: Boolean
  , depthWrite     :: Boolean
  , textureType    :: ParticleTextureType
  , builtinShape   :: Maybe BuiltinShape
  , textureAssetId :: Maybe NonEmptyString
  }

type ParticleModulationConfig =
  { id       :: NonEmptyString
  , enabled  :: Boolean
  , property :: ModulationProperty
  , curve    :: Array { time :: FiniteFloat, value :: FiniteFloat }
  }

type ParticleLayerData =
  { emitters       :: Array ParticleEmitterConfig
  , renderOptions  :: ParticleRenderOptions
  , modulations    :: Array ParticleModulationConfig
  , exportEnabled  :: Boolean
  , exportFormat   :: Maybe NonEmptyString
  }
