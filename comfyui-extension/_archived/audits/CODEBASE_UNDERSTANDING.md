# Codebase Understanding Document

> **Generated:** 2026-01-12
> **Purpose:** Capture architecture understanding for schema/refactor project
> **Status:** Active understanding phase

---

## Executive Summary

**Codebase:** 750k+ LOC, 550+ files, motion graphics compositor that exports to AI video models

**Current State:**
- ~40% types have Zod schemas (created previous session)
- 5036 tests passing
- 60% types missing schemas
- ShapeLayerData schema is structurally incorrect
- 7,793 lazy code patterns (581 `any`, 2,475 `!`, 172 `|| 0`, etc.)

**Critical Context:**
- Different export targets require DIFFERENT property names
- Schemas must define: canonical internal form + export mappings + import mappings
- This is NOT just validation - schemas define the API contract

---

## Export Format Architecture

### Export Targets & Their Requirements

| Target | Format | Key Properties | Notes |
|--------|--------|----------------|-------|
| **Wan-Move** | Trajectory arrays | `tracks: number[][][]`, `visibility: boolean[][]` | NumPy arrays (N, T, 2) |
| **ATI** | JSON string | `[[{x, y}, ...], ...]` | Fixed 121 frames, normalized [-1, 1] |
| **TTM** | Multi-layer masks | `layers[]` with masks + trajectories | Supports multiple animated layers |
| **MotionCtrl** | 4x4 RT matrices | `poses[]` with rotation + translation | Camera animation |
| **CameraCtrl** | AnimateDiff format | Camera-specific structure | Different from MotionCtrl |
| **Uni3C** | ⚠️ DEPRECATED | Non-functional with current models | Use MotionCtrl/CameraCtrl instead |

### Transformation Pattern

```
Internal Canonical Form (TypeScript interfaces)
    ↓
Export Transform Functions (services/export/*.ts)
    ↓
Model-Specific Format (JSON/arrays/matrices)
```

**Key Insight:** The same internal data structure (e.g., `Camera3D`) gets transformed differently for each target:
- MotionCtrl: `exportToMotionCtrl()` → 4x4 matrices
- CameraCtrl: `exportToCameraCtrl()` → AnimateDiff format
- Wan-Move: `exportWanMoveTrackCoordsJSON()` → trajectory arrays

---

## Schema Architecture

### Current Schema Structure

```
ui/src/schemas/
├── layers/
│   ├── layer-data-schema.ts    ⚠️ ShapeLayerData WRONG
│   ├── layer-schema.ts
│   ├── animation-schema.ts
│   ├── primitives-schema.ts
│   └── transform-schema.ts
├── exports/
│   ├── wanmove-schema.ts
│   ├── ati-schema.ts
│   ├── camera-schema.ts
│   └── depth-schema.ts
├── imports/
│   ├── camera-schema.ts
│   └── cameraTracking-schema.ts
├── project-schema.ts
└── comfyui-schema.ts
```

### Schema Design Principles

1. **Canonical Internal Form** - Schemas match TypeScript interfaces exactly
2. **Export Mappings** - Separate schemas for each export target format
3. **Import Mappings** - Schemas for external formats being imported
4. **Validation Boundaries** - Use `.finite()` to reject NaN/Infinity
5. **Type Safety** - No `any`, proper discriminated unions

---

## Critical Issues

### 1. ShapeLayerData Schema Mismatch

**Current Schema (WRONG):**
```typescript
{
  shapeType?: enum,
  fill?: string,
  stroke?: string,
  vertices?: array,
  closed?: boolean
}
```

**Actual Interface (types/shapes.ts:427-436):**
```typescript
{
  contents: ShapeContent[];      // Union of ~22 discriminated types
  blendMode: string;
  quality: "draft" | "normal" | "high";
  gpuAccelerated: boolean;
}
```

**ShapeContent Types:**
- Generators: `rectangle`, `ellipse`, `polygon`, `star`, `path`
- Modifiers: `fill`, `stroke`, `gradientFill`, `gradientStroke`
- Operators: `trimPaths`, `mergePaths`, `offsetPaths`, `puckerBloat`, `wigglePaths`, `zigZag`, `twist`, `roundedCorners`, `repeater`, `transform`
- Group: `group`
- Illustrator: `simplifyPath`, `smoothPath`, `extrude`, `trace`

**Fix Required:** Complete rewrite of `ShapeLayerDataSchema` to match actual structure.

### 2. Missing Schemas (60% of types)

| Type File | Lines | Schema Status | Priority |
|-----------|-------|---------------|----------|
| `types/shapes.ts` | 844 | ⚠️ WRONG schema | P0 |
| `types/effects.ts` | 3,319 | ❌ Missing | P0 |
| `types/physics.ts` | 990 | ❌ Missing | P1 |
| `types/layerStyles.ts` | 721 | ❌ Missing | P1 |
| `types/presets.ts` | 824 | ❌ Missing | P2 |
| `types/meshWarp.ts` | ? | ❌ Missing | P2 |
| `types/masks.ts` | ? | ❌ Missing | P2 |
| `types/assets.ts` | ? | ❌ Missing | P2 |

### 3. Lazy Code Patterns

**Root Cause:** 581 type escapes (`as any`, `: any`) force defensive coding

**Patterns:**
- `as any` (344 in production) → Type system bypass
- `: any` parameters (170) → Untyped code
- `!` assertions (~2,475) → Non-null assumptions
- `|| 0` (172) → Lazy defaults masking NaN
- `??` (1,984) → Defensive null guards
- `?.` (1,580) → Optional chaining

**Cleanup Priority:**
1. P0: Fix `as any` in production (344 instances)
2. P1: Fix `: any` parameters (170 instances)
3. P2: Fix `|| 0` in math code (172 instances)
4. P3: Clean up `!` assertions (after types fixed)
5. P4: Clean up nullish coalesce (after types fixed)

---

## Export Service Architecture

### Key Files

**Export Services:**
- `services/export/wanMoveExport.ts` - Wan-Move trajectory format
- `services/export/atiExport.ts` - ATI format (121 frames, normalized)
- `services/export/cameraExportFormats.ts` - MotionCtrl, CameraCtrl, Uni3C
- `services/modelExport.ts` - Unified export orchestrator
- `services/export/exportPipeline.ts` - Main export pipeline

**Import Services:**
- `services/cameraTrackingImport.ts` - COLMAP, Blender, Lattice JSON
- `services/cameraExport.ts` - Camera format conversions

### Export Transformation Flow

```
Layer Data (internal)
    ↓
getPositionAtFrame() / getTransformAtFrame()
    ↓
PointTrajectory[] / Camera3D[]
    ↓
exportForModel() → switch(target)
    ↓
Target-specific export function
    ↓
Model-specific format (JSON/arrays/matrices)
```

**Example: Wan-Move Export**
```typescript
// 1. Extract trajectories from layers
const trajectories = layers
  .filter(l => l.transform.position.animated)
  .map(l => extractLayerTrajectory(l, startFrame, endFrame, getPositionAtFrame));

// 2. Convert to WanMove format
const wanMoveTrajectory = convertPointTrajectoriesToWanMove(
  trajectories, compWidth, compHeight, fps
);

// 3. Export as JSON
const json = exportWanMoveTrackCoordsJSON(wanMoveTrajectory);
```

---

## Type System Architecture

### Layer Data Types

**26 Layer Types:**
1. `image` - ImageLayerData
2. `video` - VideoData
3. `text` - TextData
4. `spline` - SplineData
5. `path` - PathLayerData
6. `shape` - ShapeLayerData ⚠️ SCHEMA WRONG
7. `particles` - ParticleLayerData (new system)
8. `particle` - LegacyParticleLayerData
9. `camera` - CameraLayerData
10. `light` - LightLayerData
11. `audio` - AudioLayerData
12. `depth` - DepthLayerData
13. `normal` - NormalLayerData
14. `matte` - MatteLayerData
15. `proceduralMatte` - ProceduralMatteData
16. `depthflow` - DepthflowLayerData
17. `model` - ModelLayerData
18. `pointCloud` - PointCloudLayerData
19. `pose` - PoseLayerData
20. `generated` - GeneratedLayerData
21. `solid` - SolidLayerData
22. `group` - GroupLayerData
23. `effect` - EffectLayerData
24. `nestedComp` - NestedCompData
25. `control` - ControlLayerData
26. `null` - NullLayerData (deprecated)

### Shape Content Discriminated Union

**ShapeContent** is a union of ~22 types:
- **Generators:** RectangleShape, EllipseShape, PolygonShape, StarShape, PathShape
- **Modifiers:** FillShape, StrokeShape, GradientFillShape, GradientStrokeShape
- **Operators:** TrimPathsShape, MergePathsShape, OffsetPathsShape, PuckerBloatShape, WigglePathsShape, ZigZagShape, TwistShape, RoundedCornersShape, RepeaterShape, TransformShape
- **Group:** ShapeGroup
- **Illustrator:** SimplifyPathShape, SmoothPathShape, ExtrudeShape, TraceShape

Each has `type: "rectangle" | "ellipse" | ...` discriminator.

---

## Next Steps

### Immediate (P0)

1. **Fix ShapeLayerData Schema**
   - Read `types/shapes.ts` completely
   - Understand all 22 ShapeContent types
   - Create proper discriminated union schema
   - Update `layer-data-schema.ts`

2. **Understand Export Mappings**
   - Document property name differences per target
   - Create mapping tables
   - Update schemas with export transformation hints

### Short-term (P1)

3. **Create Missing Schemas**
   - `effects.ts` (3,319 lines) - Split by category
   - `physics.ts` (990 lines)
   - `layerStyles.ts` (721 lines)

4. **Fix Type Escapes**
   - Audit `as any` usage
   - Replace with proper types
   - Update schemas to match

### Long-term (P2+)

5. **Clean Up Lazy Patterns**
   - Fix `|| 0` in math code
   - Remove unnecessary `!` assertions
   - Clean up defensive null guards

6. **Complete Schema Coverage**
   - All types have schemas
   - All exports have schemas
   - All imports have schemas

---

## Key Files Reference

### Types
- `ui/src/types/shapes.ts` - Shape layer system (844 lines)
- `ui/src/types/effects.ts` - Effect types (3,319 lines)
- `ui/src/types/physics.ts` - Physics types (990 lines)
- `ui/src/types/layerData.ts` - Layer data union

### Schemas
- `ui/src/schemas/layers/layer-data-schema.ts` - ⚠️ ShapeLayerData WRONG
- `ui/src/schemas/exports/` - Export format schemas
- `ui/src/schemas/imports/` - Import format schemas

### Export Services
- `ui/src/services/export/wanMoveExport.ts` - Wan-Move format
- `ui/src/services/export/atiExport.ts` - ATI format
- `ui/src/services/export/cameraExportFormats.ts` - Camera formats
- `ui/src/services/modelExport.ts` - Unified export

### Import Services
- `ui/src/services/cameraTrackingImport.ts` - Camera tracking import

---

*Document Version: 1.0*
*Last Updated: 2026-01-12*
