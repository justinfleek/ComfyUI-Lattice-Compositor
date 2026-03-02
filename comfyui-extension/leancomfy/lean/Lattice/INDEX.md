# Lattice Lean4 Type System Index

This document indexes all Lean4 modules in the Lattice type system.
Each module has a max 500 line limit and contains formal proofs for all invariants.

## Module Structure

```
Lattice/
├── Primitives.lean          # Core primitive types (NonEmptyString, RGB, RGBA, etc.)
├── Entities.lean            # Core entities (Keyframe, AnimatableProperty, Layer, etc.)
│
├── Animation.lean           # Extended animation types (FullInterpolationType, etc.)
├── BlendModes.lean          # Industry standard blend modes (121 lines TS)
├── Transform.lean           # Layer transforms, motion blur (690 lines TS)
├── Assets.lean              # Asset types and references (157 lines TS)
│
├── Effects/                 # Effects system (3339 lines TS → split)
│   ├── Enums.lean          # Effect parameter types, 30+ effect enums
│   ├── Parameters.lean     # Effect parameter value types with proofs
│   ├── Core.lean           # Effect, EffectInstance, EffectDefinition
│   └── Presets.lean        # PresetCategory, AnimationPreset
├── Effects.lean             # Main re-export module
│
├── Shapes/                  # Shape system
│   ├── Groups.lean         # ShapeGroup, ShapeLayer grouping
│   └── ...
├── Shapes.lean              # Main re-export module
│
├── MeshWarp.lean           # Mesh warp types (pins, deformations)
│
├── Spline.lean             # Spline and path types
│
├── LayerStyles/            # Layer styles (722 lines TS → split)
│   ├── Enums.lean          # GlowTechnique, BevelStyle, StrokePosition, etc.
│   └── Core.lean           # All layer style structures with proofs
├── LayerStyles.lean         # Main re-export module
│
├── Masks.lean              # Mask types (270 lines TS)
│
├── Physics/                # Physics system (991 lines TS → split)
│   ├── Enums.lean          # BodyType, JointType, ForceType, ShapeType, etc.
│   ├── Core.lean           # PhysicsVec2, PhysicsMaterial, RigidBody, etc.
│   ├── Joints.lean         # All joint configuration types
│   ├── Forces.lean         # All force field types
│   ├── SoftBody.lean       # Verlet particles, cloth, ragdoll
│   └── Space.lean          # PhysicsSpaceConfig, simulation state, export
├── Physics.lean             # Main re-export module
│
├── Particles/              # Particle system (644 lines TS → split)
│   ├── Enums.lean          # EmitterShape, blend modes, audio features, etc.
│   ├── Physics.lean        # Collision, flocking, spring, SPH configs
│   ├── Emitter.lean        # Emitter configurations
│   ├── Rendering.lean      # Render options, connections
│   ├── Audio.lean          # Audio bindings and mappings
│   └── Legacy.lean         # Legacy particle types (backwards compat)
├── Particles.lean           # Main re-export module
│
├── Text.lean               # Text layer types and animators (264 lines TS)
│
├── Camera.lean             # 2.5D Camera system (282 lines TS)
│
└── TemplateBuilder.lean    # Template Builder system (486 lines TS)
```

## TypeScript Source Mapping

| Lean4 Module | TypeScript Source | Lines |
|--------------|-------------------|-------|
| Primitives.lean | (new) | ~200 |
| Entities.lean | project.ts (subset) | ~300 |
| Animation.lean | animation.ts | 213 |
| BlendModes.lean | blendModes.ts | 121 |
| Transform.lean | transform.ts | 690 |
| Assets.lean | assets.ts | 157 |
| Effects/* | effects.ts | 3339 |
| Shapes/* | shapes.ts | - |
| MeshWarp.lean | meshWarp.ts | - |
| Spline.lean | spline.ts | - |
| LayerStyles/* | layerStyles.ts | 722 |
| Masks.lean | masks.ts | 270 |
| Physics/* | physics.ts | 991 |
| Particles/* | particles.ts | 644 |
| Text.lean | text.ts | 264 |
| Camera.lean | camera.ts | 282 |
| TemplateBuilder.lean | templateBuilder.ts | 486 |

## Key Principles

### 1. No Type Escapes
- No `sorry` - all proofs must be complete
- No `unsafe` - all code must be safe
- No `partial` without termination proof

### 2. All Invariants Proven
Every numeric field has proofs for:
- `x_finite : x.isFinite` - No NaN or Infinity
- `x_positive : x > 0` - Positive values where required
- `x_ge_0 : x ≥ 0` - Non-negative values
- `x_le_N : x ≤ N` - Upper bounds where required

### 3. NonEmptyString for IDs
All identifiers use `NonEmptyString` to guarantee non-empty strings at the type level.

### 4. AnimatableProperty References
Properties that reference AnimatableProperty use `NonEmptyString` IDs (e.g., `positionPropertyId`)
rather than inline AnimatableProperty objects to avoid circular dependencies.

### 5. Sum Types for Unions
TypeScript union types become Lean4 inductive types:
```lean
inductive BlendMode where
  | normal | multiply | screen | overlay
  deriving Repr, BEq, DecidableEq
```

### 6. Structure Extension
TypeScript `extends` becomes Lean4 `extends`:
```lean
structure GravityForce extends ForceFieldBase where
  gravityPropertyId : NonEmptyString
  deriving Repr
```

## Remaining Work

### Not Yet Migrated
- [ ] cameraTracking.ts - Camera tracking data import
- [ ] export.ts - Export settings and formats
- [ ] layerData.ts - Layer-specific data types
- [ ] dataAsset.ts - Data asset (JSON value types)
- [ ] presets.ts - Effect presets
- [ ] project.ts - Full project types (large file, needs splitting)

### Code Generation (Future)
- [ ] Haskell backend generation from Lean4
- [ ] PureScript frontend generation from Lean4
- [ ] TypeScript runtime validation generation

## Usage

Import the main module:
```lean
import Lattice.Physics
import Lattice.Particles
import Lattice.Camera
```

Or import specific submodules:
```lean
import Lattice.Physics.Joints
import Lattice.Particles.Emitter
```
