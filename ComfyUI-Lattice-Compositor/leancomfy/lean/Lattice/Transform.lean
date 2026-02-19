/-
  Lattice.Transform - Layer transforms and motion blur

  Max 500 lines.

  Source: ui/src/types/transform.ts (690 lines - mostly helper functions)
-/

import Lattice.Primitives

namespace Lattice.Transform

open Lattice.Primitives

/-! ## Vector Types -/

/-- 2D vector -/
structure Vec2 where
  x : Float
  y : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-- 3D vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  z_finite : z.isFinite
  deriving Repr

/-! ## Separate Dimensions -/

/-- Separate dimensions flags -/
structure SeparateDimensions where
  position : Bool
  scale : Bool
  deriving Repr

/-! ## Layer Transform -/

/-- Layer transform - all AnimatableProperty references as IDs -/
structure LayerTransform where
  -- Position (combined)
  positionPropertyId : NonEmptyString
  -- Separate position dimensions (when separateDimensions.position is true)
  positionXPropertyId : Option NonEmptyString
  positionYPropertyId : Option NonEmptyString
  positionZPropertyId : Option NonEmptyString
  -- Origin point for rotation/scale
  originPropertyId : NonEmptyString
  -- Scale (combined)
  scalePropertyId : NonEmptyString
  -- Separate scale dimensions (when separateDimensions.scale is true)
  scaleXPropertyId : Option NonEmptyString
  scaleYPropertyId : Option NonEmptyString
  scaleZPropertyId : Option NonEmptyString
  -- 2D Rotation
  rotationPropertyId : NonEmptyString
  -- 3D Rotations (active if threeD is true)
  orientationPropertyId : Option NonEmptyString
  rotationXPropertyId : Option NonEmptyString
  rotationYPropertyId : Option NonEmptyString
  rotationZPropertyId : Option NonEmptyString
  -- Separate dimensions flags
  separateDimensions : Option SeparateDimensions
  deriving Repr

/-! ## Motion Blur -/

/-- Motion blur type -/
inductive MotionBlurType where
  | standard     -- Standard shutter-based
  | pixel        -- Pixel motion blur
  | directional  -- Directional blur
  | radial       -- Radial blur (spin/zoom)
  | vector       -- Vector-based (uses velocity)
  | adaptive     -- Auto-selects based on motion
  deriving Repr, BEq, DecidableEq

/-- Radial blur mode -/
inductive RadialMode where
  | spin
  | zoom
  deriving Repr, BEq, DecidableEq

/-- Layer motion blur settings -/
structure LayerMotionBlurSettings where
  blurType : MotionBlurType
  shutterAngle : Float               -- 0-720 degrees (180 = standard film)
  shutterPhase : Float               -- -180 to 180
  samplesPerFrame : Nat              -- 2-64
  -- For directional blur
  direction : Option Float           -- Angle in degrees
  blurLength : Option Float          -- Pixels
  -- For radial blur
  radialMode : Option RadialMode
  radialCenterX : Option Float       -- 0-1 normalized
  radialCenterY : Option Float
  radialAmount : Option Float        -- 0-100
  -- Proofs
  shutterAngle_ge_0 : shutterAngle ≥ 0
  shutterAngle_le_720 : shutterAngle ≤ 720
  shutterAngle_finite : shutterAngle.isFinite
  shutterPhase_ge_neg180 : shutterPhase ≥ -180
  shutterPhase_le_180 : shutterPhase ≤ 180
  shutterPhase_finite : shutterPhase.isFinite
  samplesPerFrame_ge_2 : samplesPerFrame ≥ 2
  samplesPerFrame_le_64 : samplesPerFrame ≤ 64
  deriving Repr

/-! ## 3D Material Options -/

/-- Shadow casting mode -/
inductive CastsShadows where
  | off
  | on
  | only
  deriving Repr, BEq, DecidableEq

/-- Layer material options for 3D -/
structure LayerMaterialOptions where
  castsShadows : CastsShadows
  lightTransmission : Float          -- 0-100%
  acceptsShadows : Bool
  acceptsLights : Bool
  ambient : Float                    -- 0-100%
  diffuse : Float                    -- 0-100%
  specularIntensity : Float          -- 0-100%
  specularShininess : Float          -- 0-100%
  metal : Float                      -- 0-100%
  -- Proofs
  lightTransmission_ge_0 : lightTransmission ≥ 0
  lightTransmission_le_100 : lightTransmission ≤ 100
  lightTransmission_finite : lightTransmission.isFinite
  ambient_ge_0 : ambient ≥ 0
  ambient_le_100 : ambient ≤ 100
  ambient_finite : ambient.isFinite
  diffuse_ge_0 : diffuse ≥ 0
  diffuse_le_100 : diffuse ≤ 100
  diffuse_finite : diffuse.isFinite
  specularIntensity_ge_0 : specularIntensity ≥ 0
  specularIntensity_le_100 : specularIntensity ≤ 100
  specularIntensity_finite : specularIntensity.isFinite
  specularShininess_ge_0 : specularShininess ≥ 0
  specularShininess_le_100 : specularShininess ≤ 100
  specularShininess_finite : specularShininess.isFinite
  metal_ge_0 : metal ≥ 0
  metal_le_100 : metal ≤ 100
  metal_finite : metal.isFinite
  deriving Repr

/-! ## Auto-Orient -/

/-- Auto-orient mode -/
inductive AutoOrientMode where
  | off
  | toCamera
  | alongPath
  | toPointOfInterest
  deriving Repr, BEq, DecidableEq

/-! ## Follow Path -/

/-- Loop mode for path following -/
inductive LoopMode where
  | clamp
  | loop
  | pingpong
  deriving Repr, BEq, DecidableEq

/-- Follow path constraint -/
structure FollowPathConstraint where
  enabled : Bool
  pathLayerId : String               -- Empty = no target
  progressPropertyId : NonEmptyString -- AnimatableProperty ID (0-1)
  offsetPropertyId : NonEmptyString  -- Perpendicular offset in pixels
  tangentOffset : Float              -- 0-1 normalized
  autoOrient : Bool
  rotationOffsetPropertyId : NonEmptyString -- Degrees
  bankingPropertyId : NonEmptyString
  loopMode : LoopMode
  tangentOffset_ge_0 : tangentOffset ≥ 0
  tangentOffset_le_1 : tangentOffset ≤ 1
  tangentOffset_finite : tangentOffset.isFinite
  deriving Repr

/-! ## Default Values -/

/-- Default Vec2 (zero) -/
def Vec2.zero : Vec2 :=
  ⟨0, 0, by decide, by decide⟩

/-- Default Vec3 (zero) -/
def Vec3.zero : Vec3 :=
  ⟨0, 0, 0, by decide, by decide, by decide⟩

/-- Default separate dimensions (both false) -/
def defaultSeparateDimensions : SeparateDimensions :=
  { position := false, scale := false }

end Lattice.Transform
