# Z Coordinate Missing Analysis

## Critical Architectural Issue

**Problem:** `Point2D`, `BezierVertex`, and `BezierPath` are 2D-only, but `ControlPoint` has `depth?: number` (z coordinate). This creates a mismatch where many path operations lose z information.

## Type Definitions

### Current 2D Types (MISSING Z):
- `Point2D` (`types/shapes.ts`): `{ x: number; y: number }` - **NO z**
- `BezierVertex` (`types/shapes.ts`): Uses `Point2D` for `point`, `inHandle`, `outHandle` - **NO z**
- `BezierPath` (`types/shapes.ts`): Uses `BezierVertex[]` - **NO z**

### Current 3D Type (HAS Z):
- `ControlPoint` (`types/spline.ts`): `{ x: number; y: number; depth?: number }` - **HAS z**

## Files Missing Z Support

### Services (16 files):
1. **`pathMorphing.ts`** - Uses `BezierPath`, `BezierVertex`, `Point2D` - **CRITICAL: Path morphing loses z**
2. **`shapeOperations.ts`** - Uses `BezierPath`, `BezierVertex`, `Point2D` - All boolean operations, offset, rounding lose z
3. **`shape/pathModifiers.ts`** - Uses `BezierPath`, `BezierVertex`, `Point2D` - Pucker/bloat, wiggle, zigzag, roughen, wave, twist lose z
4. **`vectorLOD.ts`** - Uses `BezierPath`, `BezierVertex`, `Point2D` - LOD operations lose z
5. **`bezierBoolean.ts`** - Uses `BezierPath` - Boolean operations lose z
6. **`segmentToMask.ts`** - Uses `Point2D` - Mask conversion loses z
7. **`trackPointService.ts`** - Uses `Point2D` - Track points lose z
8. **`textToVector.ts`** - Uses `BezierPath`, `BezierVertex`, `Point2D` - Text conversion loses z
9. **`expressions/layerContentExpressions.ts`** - Uses `BezierPath`, `Point2D` - Expressions lose z
10. **`effects/meshDeformRenderer.ts`** - Uses `BezierPath`, `Point2D` - Mesh deformation loses z
11. **`interpolation.ts`** - Uses `BezierPath`, `Point2D` - Interpolation loses z
12. **`arcLength.ts`** - Uses `Point2D` (but has `Point3D` support) - Mixed support
13. **`meshWarpDeformation.ts`** - Uses `BezierPath`, `Point2D` - Mesh warp loses z
14. **`imageTrace.ts`** - Uses `BezierPath`, `Point2D` - Image tracing loses z
15. **`alphaToMesh.ts`** - Uses `BezierPath`, `Point2D` - Alpha conversion loses z
16. **`textOnPath.ts`** - Uses `ControlPoint` (HAS z) but converts to `BezierPath` - **Loses z during conversion**

### Stores (2 files):
17. **`layerStore/spline.ts`** - Uses `BezierPath`, `BezierVertex`, `Point2D` - Store operations lose z
18. **`layerStore/textConversion.ts`** - Uses `BezierPath`, `BezierVertex` - Text conversion loses z

### Engine Layers (2 files):
19. **`ShapeLayer.ts`** - Uses `BezierPath`, `Point2D` - Shape rendering loses z
20. **`SplineLayer.ts`** - Uses `ControlPoint` (HAS z) - **This one is correct**

### Components (1 file):
21. **`timeline/NodeConnection.vue`** - Uses `Point2D` - Node connections lose z

### Schemas (3 files):
22. **`schemas/layers/shapes-schema.ts`** - Validates `BezierPath` (2D only)
23. **`schemas/exports/wanmove-schema.ts`** - Uses `BezierPath` (2D only)
24. **`schemas/imports/cameraTracking-schema.ts`** - Uses `Point2D` (2D only)

## Impact Assessment

### High Impact (Operations that should preserve z):
- **Path morphing** - Morphing between 3D paths loses z
- **Boolean operations** - Union/intersect/difference lose z
- **Path modifiers** - All modifiers (wiggle, zigzag, etc.) lose z
- **Offset paths** - Offset operations lose z
- **Text on path** - Text following 3D paths loses z during conversion

### Medium Impact:
- **Shape operations** - Rounding, offset lose z
- **Vector LOD** - LOD simplification loses z
- **Interpolation** - Path interpolation loses z

### Low Impact (2D-only operations):
- **2D shape generation** - Rectangles, ellipses, polygons (these are inherently 2D)
- **Canvas rendering** - Path2D API is 2D-only

## Required Changes

### Phase 1: Type System Updates
1. Add `Point3D` type: `{ x: number; y: number; z: number }`
2. Update `BezierVertex` to support optional z:
   ```typescript
   interface BezierVertex {
     point: Point2D | Point3D;
     inHandle: Point2D | Point3D;
     outHandle: Point2D | Point2D;
   }
   ```
3. Or create `BezierVertex3D` and `BezierPath3D` types

### Phase 2: Service Updates
- Update all path operations to preserve z when present
- Add z interpolation in morphing operations
- Update distance calculations to include z
- Update arc length calculations for 3D curves

### Phase 3: Conversion Functions
- Add `ControlPoint` ↔ `BezierVertex` conversion that preserves z
- Update `textOnPath.ts` to preserve z during conversion

## Files That Already Handle Z Correctly

- `SplineLayer.ts` - Uses `ControlPoint` with `depth`
- `PathLayer.ts` - Uses `ControlPoint` with `depth`
- `textOnPath.ts` - Uses `ControlPoint` (but converts to `BezierPath` losing z)
- `arcLength.ts` - Has `Point3D` support but mixed usage

## Next Steps

1. **Immediate:** Finish `??` pattern refactoring (current task)
2. **Next:** Add z support to `Point2D` → `Point3D` or make `Point2D` support optional z
3. **Then:** Update `BezierVertex` and `BezierPath` to support z
4. **Finally:** Update all services to preserve z coordinates
