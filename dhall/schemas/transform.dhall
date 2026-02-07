-- |
-- Module      : Lattice.Schema.Transform
-- Description : Transform type definitions and validation constants
--
-- Migrated from ui/src/schemas/layers/transform-schema.ts
-- Defines transform types: layer transforms, motion blur, materials, constraints

let Primitives = ./primitives.dhall

let Animation = ./animation.dhall

-- ============================================================================
-- Separate Dimensions
-- ============================================================================

let SeparateDimensions = { position : Bool, scale : Bool }

-- ============================================================================
-- Layer Transform
-- ============================================================================

let LayerTransform =
      { position : Animation.AnimatableProperty Primitives.Position2DOr3D
      , positionX : Optional (Animation.AnimatableProperty Primitives.FiniteNumber)
      , positionY : Optional (Animation.AnimatableProperty Primitives.FiniteNumber)
      , positionZ : Optional (Animation.AnimatableProperty Primitives.FiniteNumber)
      , origin : Animation.AnimatableProperty Primitives.Position2DOr3D
      , anchorPoint : Optional (Animation.AnimatableProperty Primitives.Position2DOr3D)
      , scale : Animation.AnimatableProperty Primitives.Position2DOr3D
      , scaleX : Optional (Animation.AnimatableProperty Primitives.FiniteNumber)
      , scaleY : Optional (Animation.AnimatableProperty Primitives.FiniteNumber)
      , scaleZ : Optional (Animation.AnimatableProperty Primitives.FiniteNumber)
      , rotation : Animation.AnimatableProperty Primitives.FiniteNumber
      , orientation : Optional (Animation.AnimatableProperty Primitives.Vec3)
      , rotationX : Optional (Animation.AnimatableProperty Primitives.FiniteNumber)
      , rotationY : Optional (Animation.AnimatableProperty Primitives.FiniteNumber)
      , rotationZ : Optional (Animation.AnimatableProperty Primitives.FiniteNumber)
      , separateDimensions : Optional SeparateDimensions
      }

-- ============================================================================
-- Motion Blur
-- ============================================================================

let MotionBlurType = < Standard | Pixel | Directional | Radial | Vector | Adaptive >

let RadialMode = < Spin | Zoom >

let LayerMotionBlurSettings =
      { type : MotionBlurType
      , shutterAngle : Primitives.FiniteNumber  -- 0-720
      , shutterPhase : Primitives.FiniteNumber  -- -180 to 180
      , samplesPerFrame : Natural  -- 2-64 (int)
      , direction : Optional Primitives.FiniteNumber
      , blurLength : Optional Primitives.FiniteNumber  -- 0-1000
      , radialMode : Optional RadialMode
      , radialCenterX : Optional Primitives.Normalized01
      , radialCenterY : Optional Primitives.Normalized01
      , radialAmount : Optional Primitives.FiniteNumber  -- 0-100
      }

-- ============================================================================
-- Material Options
-- ============================================================================

let CastsShadows = < Off | On | Only >

let LayerMaterialOptions =
      { castsShadows : CastsShadows
      , lightTransmission : Primitives.FiniteNumber  -- 0-100
      , acceptsShadows : Bool
      , acceptsLights : Bool
      , ambient : Primitives.FiniteNumber  -- 0-100
      , diffuse : Primitives.FiniteNumber  -- 0-100
      , specularIntensity : Primitives.FiniteNumber  -- 0-100
      , specularShininess : Primitives.FiniteNumber  -- 0-100
      , metal : Primitives.FiniteNumber  -- 0-100
      }

-- ============================================================================
-- Auto-Orient
-- ============================================================================

let AutoOrientMode = < Off | ToCamera | AlongPath | ToPointOfInterest >

-- ============================================================================
-- Follow Path Constraint
-- ============================================================================

let FollowPathConstraint =
      { enabled : Bool
      , pathLayerId : Primitives.EntityId
      , progress : Animation.AnimatableProperty Primitives.FiniteNumber
      , offset : Optional (Animation.AnimatableProperty Primitives.Position2DOr3D)
      , autoOrient : Optional Bool
      , orientOffset : Optional (Animation.AnimatableProperty Primitives.FiniteNumber)
      , loop : Optional Bool
      , pingPong : Optional Bool
      }

-- ============================================================================
-- Audio Path Animation
-- ============================================================================

let AudioFeature = < Amplitude | Bass | Mid | Treble | Spectral >

let AudioPathAnimation =
      { enabled : Bool
      , pathLayerId : Primitives.EntityId
      , audioLayerId : Primitives.EntityId
      , feature : AudioFeature
      , sensitivity : Primitives.FiniteNumber  -- 0-2
      , smoothing : Primitives.Normalized01
      , offset : Primitives.FiniteNumber
      , loop : Bool
      }

-- ============================================================================
-- Export
-- ============================================================================

in  { SeparateDimensions
    , LayerTransform
    , MotionBlurType
    , RadialMode
    , LayerMotionBlurSettings
    , CastsShadows
    , LayerMaterialOptions
    , AutoOrientMode
    , FollowPathConstraint
    , AudioFeature
    , AudioPathAnimation
    }
