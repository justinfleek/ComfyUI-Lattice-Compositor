-- | Lattice.Schemas.Layers.LayerDataSchema.Particle - Particle layer enums
-- |
-- | Enums for Particle layers including emitters, forces, audio, rendering.

module Lattice.Schemas.Layers.LayerDataSchema.Particle
  ( -- Emitter
    EmitterShape(..), emitterShapeFromString
  , SpritePlayMode(..), spritePlayModeFromString
  , SplineEmitMode(..), splineEmitModeFromString
  , DepthMode(..), depthModeFromString
  , MaskChannel(..), maskChannelFromString
    -- Forces
  , ForceFalloff(..), forceFalloffFromString
  , BoundaryBehavior(..), boundaryBehaviorFromString
  , FloorBehavior(..), floorBehaviorFromString
    -- Modulation
  , ModulationProperty(..), modulationPropertyFromString
    -- Audio
  , AudioFeature(..), audioFeatureFromString
  , AudioBindingTarget(..), audioBindingTargetFromString
  , AudioBindingCurve(..), audioBindingCurveFromString
    -- Rendering
  , ParticleBlendMode(..), particleBlendModeFromString
  , ParticleShape(..), particleShapeFromString
  , MeshMode(..), meshModeFromString
  , MeshGeometry(..), meshGeometryFromString
    -- Physics
  , SpringStructureType(..), springStructureTypeFromString
  , SPHFluidPreset(..), sphFluidPresetFromString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Emitter
-- ────────────────────────────────────────────────────────────────────────────

data EmitterShape
  = EsPoint | EsLine | EsCircle | EsBox | EsSphere | EsRing
  | EsSpline | EsDepthMap | EsMask | EsCone | EsImage | EsDepthEdge

derive instance Eq EmitterShape
derive instance Generic EmitterShape _
instance Show EmitterShape where show = genericShow

emitterShapeFromString :: String -> Maybe EmitterShape
emitterShapeFromString = case _ of
  "point" -> Just EsPoint
  "line" -> Just EsLine
  "circle" -> Just EsCircle
  "box" -> Just EsBox
  "sphere" -> Just EsSphere
  "ring" -> Just EsRing
  "spline" -> Just EsSpline
  "depth-map" -> Just EsDepthMap
  "mask" -> Just EsMask
  "cone" -> Just EsCone
  "image" -> Just EsImage
  "depthEdge" -> Just EsDepthEdge
  _ -> Nothing

data SpritePlayMode = SpLoop | SpOnce | SpPingpong | SpRandom

derive instance Eq SpritePlayMode
derive instance Generic SpritePlayMode _
instance Show SpritePlayMode where show = genericShow

spritePlayModeFromString :: String -> Maybe SpritePlayMode
spritePlayModeFromString = case _ of
  "loop" -> Just SpLoop
  "once" -> Just SpOnce
  "pingpong" -> Just SpPingpong
  "random" -> Just SpRandom
  _ -> Nothing

data SplineEmitMode = SeUniform | SeRandom | SeStart | SeEnd | SeSequential

derive instance Eq SplineEmitMode
derive instance Generic SplineEmitMode _
instance Show SplineEmitMode where show = genericShow

splineEmitModeFromString :: String -> Maybe SplineEmitMode
splineEmitModeFromString = case _ of
  "uniform" -> Just SeUniform
  "random" -> Just SeRandom
  "start" -> Just SeStart
  "end" -> Just SeEnd
  "sequential" -> Just SeSequential
  _ -> Nothing

data DepthMode = DmNearWhite | DmNearBlack

derive instance Eq DepthMode
derive instance Generic DepthMode _
instance Show DepthMode where show = genericShow

depthModeFromString :: String -> Maybe DepthMode
depthModeFromString = case _ of
  "near-white" -> Just DmNearWhite
  "near-black" -> Just DmNearBlack
  _ -> Nothing

data MaskChannel = McLuminance | McAlpha | McRed | McGreen | McBlue

derive instance Eq MaskChannel
derive instance Generic MaskChannel _
instance Show MaskChannel where show = genericShow

maskChannelFromString :: String -> Maybe MaskChannel
maskChannelFromString = case _ of
  "luminance" -> Just McLuminance
  "alpha" -> Just McAlpha
  "red" -> Just McRed
  "green" -> Just McGreen
  "blue" -> Just McBlue
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Forces
-- ────────────────────────────────────────────────────────────────────────────

data ForceFalloff = FfLinear | FfQuadratic | FfConstant

derive instance Eq ForceFalloff
derive instance Generic ForceFalloff _
instance Show ForceFalloff where show = genericShow

forceFalloffFromString :: String -> Maybe ForceFalloff
forceFalloffFromString = case _ of
  "linear" -> Just FfLinear
  "quadratic" -> Just FfQuadratic
  "constant" -> Just FfConstant
  _ -> Nothing

data BoundaryBehavior = BbNone | BbKill | BbBounce | BbWrap | BbStick

derive instance Eq BoundaryBehavior
derive instance Generic BoundaryBehavior _
instance Show BoundaryBehavior where show = genericShow

boundaryBehaviorFromString :: String -> Maybe BoundaryBehavior
boundaryBehaviorFromString = case _ of
  "none" -> Just BbNone
  "kill" -> Just BbKill
  "bounce" -> Just BbBounce
  "wrap" -> Just BbWrap
  "stick" -> Just BbStick
  _ -> Nothing

data FloorBehavior = FloorNone | FloorBounce | FloorStick | FloorKill

derive instance Eq FloorBehavior
derive instance Generic FloorBehavior _
instance Show FloorBehavior where show = genericShow

floorBehaviorFromString :: String -> Maybe FloorBehavior
floorBehaviorFromString = case _ of
  "none" -> Just FloorNone
  "bounce" -> Just FloorBounce
  "stick" -> Just FloorStick
  "kill" -> Just FloorKill
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Modulation
-- ────────────────────────────────────────────────────────────────────────────

data ModulationProperty = ModSize | ModSpeed | ModOpacity | ModColorR | ModColorG | ModColorB

derive instance Eq ModulationProperty
derive instance Generic ModulationProperty _
instance Show ModulationProperty where show = genericShow

modulationPropertyFromString :: String -> Maybe ModulationProperty
modulationPropertyFromString = case _ of
  "size" -> Just ModSize
  "speed" -> Just ModSpeed
  "opacity" -> Just ModOpacity
  "colorR" -> Just ModColorR
  "colorG" -> Just ModColorG
  "colorB" -> Just ModColorB
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Audio
-- ────────────────────────────────────────────────────────────────────────────

data AudioFeature = AfAmplitude | AfBass | AfMid | AfHigh | AfBeat | AfSpectralCentroid

derive instance Eq AudioFeature
derive instance Generic AudioFeature _
instance Show AudioFeature where show = genericShow

audioFeatureFromString :: String -> Maybe AudioFeature
audioFeatureFromString = case _ of
  "amplitude" -> Just AfAmplitude
  "bass" -> Just AfBass
  "mid" -> Just AfMid
  "high" -> Just AfHigh
  "beat" -> Just AfBeat
  "spectralCentroid" -> Just AfSpectralCentroid
  _ -> Nothing

data AudioBindingTarget = AtEmitter | AtSystem | AtForceField

derive instance Eq AudioBindingTarget
derive instance Generic AudioBindingTarget _
instance Show AudioBindingTarget where show = genericShow

audioBindingTargetFromString :: String -> Maybe AudioBindingTarget
audioBindingTargetFromString = case _ of
  "emitter" -> Just AtEmitter
  "system" -> Just AtSystem
  "forceField" -> Just AtForceField
  _ -> Nothing

data AudioBindingCurve = AbLinear | AbExponential | AbLogarithmic | AbStep

derive instance Eq AudioBindingCurve
derive instance Generic AudioBindingCurve _
instance Show AudioBindingCurve where show = genericShow

audioBindingCurveFromString :: String -> Maybe AudioBindingCurve
audioBindingCurveFromString = case _ of
  "linear" -> Just AbLinear
  "exponential" -> Just AbExponential
  "logarithmic" -> Just AbLogarithmic
  "step" -> Just AbStep
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Rendering
-- ────────────────────────────────────────────────────────────────────────────

data ParticleBlendMode = PbNormal | PbAdditive | PbMultiply | PbScreen

derive instance Eq ParticleBlendMode
derive instance Generic ParticleBlendMode _
instance Show ParticleBlendMode where show = genericShow

particleBlendModeFromString :: String -> Maybe ParticleBlendMode
particleBlendModeFromString = case _ of
  "normal" -> Just PbNormal
  "additive" -> Just PbAdditive
  "multiply" -> Just PbMultiply
  "screen" -> Just PbScreen
  _ -> Nothing

data ParticleShape = PsCircle | PsSquare | PsTriangle | PsStar

derive instance Eq ParticleShape
derive instance Generic ParticleShape _
instance Show ParticleShape where show = genericShow

particleShapeFromString :: String -> Maybe ParticleShape
particleShapeFromString = case _ of
  "circle" -> Just PsCircle
  "square" -> Just PsSquare
  "triangle" -> Just PsTriangle
  "star" -> Just PsStar
  _ -> Nothing

data MeshMode = MmBillboard | MmMesh

derive instance Eq MeshMode
derive instance Generic MeshMode _
instance Show MeshMode where show = genericShow

meshModeFromString :: String -> Maybe MeshMode
meshModeFromString = case _ of
  "billboard" -> Just MmBillboard
  "mesh" -> Just MmMesh
  _ -> Nothing

data MeshGeometry = MgCube | MgSphere | MgCylinder | MgCone | MgTorus | MgCustom

derive instance Eq MeshGeometry
derive instance Generic MeshGeometry _
instance Show MeshGeometry where show = genericShow

meshGeometryFromString :: String -> Maybe MeshGeometry
meshGeometryFromString = case _ of
  "cube" -> Just MgCube
  "sphere" -> Just MgSphere
  "cylinder" -> Just MgCylinder
  "cone" -> Just MgCone
  "torus" -> Just MgTorus
  "custom" -> Just MgCustom
  _ -> Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Physics
-- ────────────────────────────────────────────────────────────────────────────

data SpringStructureType = SsCloth | SsRope | SsSoftbody | SsCustom

derive instance Eq SpringStructureType
derive instance Generic SpringStructureType _
instance Show SpringStructureType where show = genericShow

springStructureTypeFromString :: String -> Maybe SpringStructureType
springStructureTypeFromString = case _ of
  "cloth" -> Just SsCloth
  "rope" -> Just SsRope
  "softbody" -> Just SsSoftbody
  "custom" -> Just SsCustom
  _ -> Nothing

data SPHFluidPreset = SphWater | SphHoney | SphLava | SphGas | SphCustom

derive instance Eq SPHFluidPreset
derive instance Generic SPHFluidPreset _
instance Show SPHFluidPreset where show = genericShow

sphFluidPresetFromString :: String -> Maybe SPHFluidPreset
sphFluidPresetFromString = case _ of
  "water" -> Just SphWater
  "honey" -> Just SphHoney
  "lava" -> Just SphLava
  "gas" -> Just SphGas
  "custom" -> Just SphCustom
  _ -> Nothing
