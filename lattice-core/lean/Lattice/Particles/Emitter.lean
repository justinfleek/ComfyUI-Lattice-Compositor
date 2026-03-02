/-
  Lattice.Particles.Emitter - Particle emitter configurations

  Part of Particles module. Max 500 lines.

  Source: ui/src/types/particles.ts (emitter configs)
-/

import Lattice.Primitives
import Lattice.Particles.Enums

namespace Lattice.Particles.Emitter

open Lattice.Primitives
open Lattice.Particles.Enums

/-! ## Depth Map Emission -/

/-- Depth map emission configuration -/
structure DepthMapEmission where
  sourceLayerId : NonEmptyString
  depthMin : Float                   -- 0-1
  depthMax : Float                   -- 0-1
  density : Float                    -- Emission density per pixel
  velocityByDepth : Bool             -- Scale velocity by depth
  sizeByDepth : Bool                 -- Scale size by depth
  depthMode : DepthMode
  depthMin_ge_0 : depthMin ≥ 0
  depthMin_le_1 : depthMin ≤ 1
  depthMin_finite : depthMin.isFinite
  depthMax_ge_0 : depthMax ≥ 0
  depthMax_le_1 : depthMax ≤ 1
  depthMax_finite : depthMax.isFinite
  depthMin_le_depthMax : depthMin ≤ depthMax
  density_positive : density > 0
  density_finite : density.isFinite
  deriving Repr

/-! ## Mask Emission -/

/-- Mask emission configuration -/
structure MaskEmission where
  sourceLayerId : NonEmptyString
  threshold : Float                  -- 0-1
  density : Float
  channel : MaskChannel
  invert : Bool
  sampleRate : Nat                   -- 1 = every pixel
  threshold_ge_0 : threshold ≥ 0
  threshold_le_1 : threshold ≤ 1
  threshold_finite : threshold.isFinite
  density_positive : density > 0
  density_finite : density.isFinite
  sampleRate_positive : sampleRate > 0
  deriving Repr

/-! ## Spline Path Emission -/

/-- Spline path emission configuration -/
structure SplinePathEmission where
  layerId : NonEmptyString           -- ID of SplineLayer
  emitMode : SplineEmitMode
  parameter : Float                  -- Offset/interval/speed depending on mode
  alignToPath : Bool                 -- Align direction with path tangent
  offset : Float                     -- Perpendicular offset from path
  bidirectional : Bool               -- Emit from both directions
  parameter_finite : parameter.isFinite
  offset_finite : offset.isFinite
  deriving Repr

/-! ## Sprite Config -/

/-- Sprite configuration for particles -/
structure SpriteConfig where
  enabled : Bool
  imageUrl : Option String
  isSheet : Bool
  columns : Nat
  rows : Nat
  totalFrames : Nat
  frameRate : Float
  playMode : SpritePlayMode
  billboard : Bool
  rotationEnabled : Bool
  rotationSpeed : Float
  rotationSpeedVariance : Float
  alignToVelocity : Bool
  columns_positive : columns > 0
  rows_positive : rows > 0
  totalFrames_positive : totalFrames > 0
  frameRate_positive : frameRate > 0
  frameRate_finite : frameRate.isFinite
  rotationSpeed_finite : rotationSpeed.isFinite
  rotationSpeedVariance_ge_0 : rotationSpeedVariance ≥ 0
  rotationSpeedVariance_finite : rotationSpeedVariance.isFinite
  deriving Repr

/-! ## Emitter Config -/

/-- Particle emitter configuration -/
structure ParticleEmitterConfig where
  id : NonEmptyString
  name : NonEmptyString
  x : Float
  y : Float
  z : Option Float                   -- Depth position
  direction : Float                  -- Degrees
  spread : Float                     -- Cone angle
  speed : Float
  speedVariance : Float
  size : Float
  sizeVariance : Float
  color : RGB                        -- RGB color
  emissionRate : Float               -- Particles per frame
  initialBurst : Nat
  particleLifetime : Float           -- Frames
  lifetimeVariance : Float
  enabled : Bool
  burstOnBeat : Bool
  burstCount : Nat
  -- Geometric emitter shape
  shape : EmitterShape
  shapeRadius : Float
  shapeWidth : Float
  shapeHeight : Float
  shapeDepth : Float
  shapeInnerRadius : Float
  emitFromEdge : Bool
  emitFromVolume : Bool
  -- Spline path emission (when shape = spline)
  splinePath : Option SplinePathEmission
  -- Depth map emission (when shape = depthMap)
  depthMapEmission : Option DepthMapEmission
  -- Mask emission (when shape = mask)
  maskEmission : Option MaskEmission
  -- Sprite configuration
  sprite : SpriteConfig
  -- Cone shape properties (when shape = cone)
  coneAngle : Option Float           -- 0-180 degrees
  coneRadius : Option Float
  coneLength : Option Float
  -- Image shape properties (when shape = image)
  imageSourceLayerId : Option NonEmptyString
  emissionThreshold : Option Float   -- 0-1
  emitFromMaskEdge : Option Bool
  -- Depth edge properties (when shape = depthEdge)
  depthSourceLayerId : Option NonEmptyString
  depthEdgeThreshold : Option Float
  depthScale : Option Float
  -- Alternative property names (preset compatibility)
  lifespan : Option Float            -- Alias for particleLifetime
  startSize : Option Float
  endSize : Option Float
  startColor : Option HexColor
  endColor : Option HexColor
  startOpacity : Option Float
  endOpacity : Option Float
  velocitySpread : Option Float
  -- Proofs
  x_finite : x.isFinite
  y_finite : y.isFinite
  direction_finite : direction.isFinite
  spread_ge_0 : spread ≥ 0
  spread_finite : spread.isFinite
  speed_ge_0 : speed ≥ 0
  speed_finite : speed.isFinite
  speedVariance_ge_0 : speedVariance ≥ 0
  speedVariance_finite : speedVariance.isFinite
  size_positive : size > 0
  size_finite : size.isFinite
  sizeVariance_ge_0 : sizeVariance ≥ 0
  sizeVariance_finite : sizeVariance.isFinite
  emissionRate_ge_0 : emissionRate ≥ 0
  emissionRate_finite : emissionRate.isFinite
  particleLifetime_positive : particleLifetime > 0
  particleLifetime_finite : particleLifetime.isFinite
  lifetimeVariance_ge_0 : lifetimeVariance ≥ 0
  lifetimeVariance_le_1 : lifetimeVariance ≤ 1
  lifetimeVariance_finite : lifetimeVariance.isFinite
  shapeRadius_ge_0 : shapeRadius ≥ 0
  shapeRadius_finite : shapeRadius.isFinite
  shapeWidth_ge_0 : shapeWidth ≥ 0
  shapeWidth_finite : shapeWidth.isFinite
  shapeHeight_ge_0 : shapeHeight ≥ 0
  shapeHeight_finite : shapeHeight.isFinite
  shapeDepth_ge_0 : shapeDepth ≥ 0
  shapeDepth_finite : shapeDepth.isFinite
  shapeInnerRadius_ge_0 : shapeInnerRadius ≥ 0
  shapeInnerRadius_finite : shapeInnerRadius.isFinite
  deriving Repr

/-! ## Sub Emitter Config -/

/-- Sub-emitter configuration -/
structure SubEmitterConfig where
  id : NonEmptyString
  parentEmitterId : NonEmptyString   -- '*' for all
  trigger : SubEmitterTrigger
  spawnCount : Nat                   -- 1-10
  inheritVelocity : Float            -- 0-1
  size : Float
  sizeVariance : Float
  lifetime : Float                   -- Frames
  speed : Float
  spread : Float                     -- Degrees
  color : RGB
  enabled : Bool
  spawnCount_positive : spawnCount > 0
  spawnCount_le_10 : spawnCount ≤ 10
  inheritVelocity_ge_0 : inheritVelocity ≥ 0
  inheritVelocity_le_1 : inheritVelocity ≤ 1
  inheritVelocity_finite : inheritVelocity.isFinite
  size_positive : size > 0
  size_finite : size.isFinite
  sizeVariance_ge_0 : sizeVariance ≥ 0
  sizeVariance_finite : sizeVariance.isFinite
  lifetime_positive : lifetime > 0
  lifetime_finite : lifetime.isFinite
  speed_ge_0 : speed ≥ 0
  speed_finite : speed.isFinite
  spread_ge_0 : spread ≥ 0
  spread_le_360 : spread ≤ 360
  spread_finite : spread.isFinite
  deriving Repr

/-! ## System Config -/

/-- Particle system layer configuration -/
structure ParticleSystemLayerConfig where
  maxParticles : Nat
  gravity : Float
  windStrength : Float
  windDirection : Float              -- Degrees
  warmupPeriod : Nat                 -- Frames
  respectMaskBoundary : Bool
  boundaryBehavior : BoundaryBehavior
  friction : Float                   -- 0-1
  useGPU : Bool                      -- Enable WebGPU compute
  maxParticles_positive : maxParticles > 0
  gravity_finite : gravity.isFinite
  windStrength_ge_0 : windStrength ≥ 0
  windStrength_finite : windStrength.isFinite
  windDirection_finite : windDirection.isFinite
  friction_ge_0 : friction ≥ 0
  friction_le_1 : friction ≤ 1
  friction_finite : friction.isFinite
  deriving Repr

/-! ## Visualization Config -/

/-- CC Particle World style visualization config -/
structure ParticleVisualizationConfig where
  showHorizon : Bool                 -- Show horizon line at floor
  showGrid : Bool                    -- Show 3D perspective grid
  showAxis : Bool                    -- Show XYZ axis at origin
  gridSize : Float                   -- Grid cell size in pixels
  gridDepth : Float                  -- Grid depth into Z axis
  gridSize_positive : gridSize > 0
  gridSize_finite : gridSize.isFinite
  gridDepth_positive : gridDepth > 0
  gridDepth_finite : gridDepth.isFinite
  deriving Repr

end Lattice.Particles.Emitter
