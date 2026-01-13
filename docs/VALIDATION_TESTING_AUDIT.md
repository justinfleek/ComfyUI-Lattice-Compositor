# Schema Validation Testing Status

> **Date:** 2026-01-12
> **Purpose:** What exists, what's missing, what needs testing

---

## Current State

### Schemas Created: **321+ definitions** across 6 files
- `layer-data-schema.ts` - 139 schemas (all 26 layer types: Image, Video, Depth, Normal, Audio, Generated, Solid, Control, Null, Group, Effect, NestedComp, Camera, Light, Pose, Model, PointCloud, Matte, ProceduralMatte, Depthflow, GeneratedMap, Spline, Path, Text, Shape, Particle)
- `shapes-schema.ts` - 89 schemas (shape system: generators, modifiers, operators, groups)
- `animation-schema.ts` - 38 schemas (keyframes, animatable properties)
- `transform-schema.ts` - 16 schemas (transforms, motion blur)
- `primitives-schema.ts` - 24 schemas (Vec2, Vec3, colors, etc.)
- `layer-schema.ts` - 15 schemas (main Layer schema)

### Test Coverage: **0%** - NO tests exist for ANY schemas

---

## What Testing EXISTS (Not Schema Tests)

### 1. Custom Validation Utilities (`utils/validation.ts`)
**Test File:** `ui/src/__tests__/property/validation.property.test.ts`
- Tests runtime validation helpers (NOT Zod schemas)
- Uses fast-check property-based testing

### 2. Regression Tests
- Camera export NaN validation
- Project dimension validation
- Viewport controls validation

---

## What's MISSING

### ❌ Schema Test Utilities
- No utilities for testing Zod schemas
- No pattern for `schema.safeParse()` testing

### ❌ Schema Test Files
- `ui/src/__tests__/schemas/` directory is EMPTY
- No tests for any of the 321+ schemas

### ❌ Integration Tests
- No tests verifying schemas are used at validation boundaries
- No tests for import/export validation

---

## What Needs to Be Done

1. **Create test utilities** for schema testing
2. **Test all 321+ schemas** systematically
3. **Integrate validation** at boundaries (store actions, file I/O, components)

---

*Last Updated: 2026-01-12*
