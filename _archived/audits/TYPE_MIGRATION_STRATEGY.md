# Type Migration Strategy

**Date:** 2026-01-XX  
**Phase:** 4.1 - TypeScript Types → Haskell Types

---

## Overview

Migrating 291k+ lines of TypeScript/Vue code to Haskell is a massive undertaking. This document outlines the systematic strategy for type migration.

---

## Migration Order

### Phase 4.1.1: Core Types ✅ (Examples Created)
- ✅ `Vec3`, `Vec2` → `Lattice.Types.Transform`
- ✅ `Point`, `BoundingBox` → `Lattice.Types.Core`
- ✅ `BlendMode`, `ColorSpace` → `Lattice.Types.Core`

### Phase 4.1.2: Transform Types ✅ (Examples Created)
- ✅ `LayerTransform` → `Lattice.Types.Transform`
- ✅ `MotionBlurType` → `Lattice.Types.Transform`

### Phase 4.1.3: Animation Types (Next)
- ⏳ `AnimatableProperty<T>` → `Lattice.Types.Animation`
- ⏳ `Keyframe`, `EasingType` → `Lattice.Types.Animation`
- ⏳ `InterpolationType` → `Lattice.Types.Animation`

### Phase 4.1.4: Layer Types (Large)
- ⏳ `Layer` → `Lattice.Types.Layer`
- ⏳ `LayerType` → `Lattice.Types.Layer`
- ⏳ `LayerDataMap` → `Lattice.Types.Layer` (sum type)

### Phase 4.1.5: Project Types (Large)
- ⏳ `LatticeProject` → `Lattice.Types.Project`
- ⏳ `Composition` → `Lattice.Types.Composition`
- ⏳ `AssetReference` → `Lattice.Types.Asset`

### Phase 4.1.6: Specialized Layer Data Types
- ⏳ `SplineData` → `Lattice.Types.Spline`
- ⏳ `TextData` → `Lattice.Types.Text`
- ⏳ `ParticleLayerData` → `Lattice.Types.Particle`
- ⏳ `CameraLayerData` → `Lattice.Types.Camera`
- ⏳ ... (20+ more layer data types)

---

## Migration Patterns

### TypeScript Interface → Haskell Record

**Before (TypeScript):**
```typescript
export interface Vec3 {
  x: number;
  y: number;
  z: number;
}
```

**After (Haskell):**
```haskell
data Vec3 = Vec3
  { vec3X :: Double
  , vec3Y :: Double
  , vec3Z :: Double
  }
  deriving (Eq, Show, Generic, ToJSON, FromJSON)
```

### TypeScript Union → Haskell Sum Type

**Before (TypeScript):**
```typescript
export type BlendMode =
  | "normal"
  | "multiply"
  | "screen";
```

**After (Haskell):**
```haskell
data BlendMode
  = BlendNormal
  | BlendMultiply
  | BlendScreen
  deriving (Eq, Show, Generic, ToJSON, FromJSON)
```

### TypeScript Optional → Haskell Maybe

**Before (TypeScript):**
```typescript
export interface Layer {
  parentId: string | null;
  matteLayerId?: string;
}
```

**After (Haskell):**
```haskell
data Layer = Layer
  { layerParentId :: Maybe Text
  , layerMatteLayerId :: Maybe Text
  }
```

### TypeScript Generic → Haskell Type Parameter

**Before (TypeScript):**
```typescript
export interface AnimatableProperty<T> {
  value: T;
  keyframes: Keyframe<T>[];
}
```

**After (Haskell):**
```haskell
data AnimatableProperty a = AnimatableProperty
  { animatableValue :: a
  , animatableKeyframes :: [Keyframe a]
  }
```

---

## File Size Constraint

**Rule:** Every file must be <500 lines

**Strategy:**
- Split large type files into modules by domain
- `project.ts` (2200 lines) → Split into:
  - `Lattice.Types.Project` (<200 lines)
  - `Lattice.Types.Layer` (<300 lines)
  - `Lattice.Types.Composition` (<200 lines)
  - `Lattice.Types.Asset` (<200 lines)
  - `Lattice.Types.LayerData.*` (one module per layer type)

---

## Verification

**After each migration:**
1. Types compile (`ghc -c`)
2. JSON serialization works (`aeson`)
3. Roundtrip tests pass (TypeScript → Haskell → TypeScript)
4. File size <500 lines

---

## Progress Tracking

- **Completed:** 2 modules, ~150 lines
- **Remaining:** ~50+ modules, ~15,000+ lines of types
- **Estimated Time:** 2-3 months (incremental)

---

## Notes

- **Preserve JSON compatibility** - Use `aeson` with field name mapping
- **No null/undefined** - Use `Maybe` explicitly
- **Explicit types** - No type inference at module boundaries
- **Documentation** - Each type has Haddock comments
