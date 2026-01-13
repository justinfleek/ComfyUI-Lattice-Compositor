# ShapeLayerData Schema Fix - Summary

> **Date:** 2026-01-12
> **Status:** ✅ COMPLETE
> **Issue:** ShapeLayerData schema was structurally incorrect

---

## Problem

The `ShapeLayerDataSchema` in `ui/src/schemas/layers/layer-data-schema.ts` was completely wrong:

**Old (WRONG) Schema:**
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

---

## Solution

Created comprehensive `ui/src/schemas/layers/shapes-schema.ts` with:

1. **Base Types:**
   - `Point2DSchema` (Vec2Schema alias)
   - `ShapeColorSchema` (r,g,b: 0-255, a: 0-1)
   - `BezierVertexSchema`
   - `BezierPathSchema`
   - `GradientDefSchema`

2. **Animatable Property Schemas:**
   - `AnimatablePoint2DSchema`
   - `AnimatableShapeColorSchema`
   - `AnimatableBezierPathSchema`
   - `AnimatableGradientDefSchema`
   - `AnimatableNumberArraySchema`

3. **Shape Generators (5 types):**
   - `RectangleShapeSchema`
   - `EllipseShapeSchema`
   - `PolygonShapeSchema`
   - `StarShapeSchema`
   - `PathShapeSchema`

4. **Shape Modifiers (4 types):**
   - `FillShapeSchema`
   - `StrokeShapeSchema`
   - `GradientFillShapeSchema`
   - `GradientStrokeShapeSchema`

5. **Path Operators (8 types):**
   - `TrimPathsOperatorSchema`
   - `MergePathsOperatorSchema`
   - `OffsetPathsOperatorSchema`
   - `PuckerBloatOperatorSchema`
   - `WigglePathsOperatorSchema`
   - `ZigZagOperatorSchema`
   - `TwistOperatorSchema`
   - `RoundedCornersOperatorSchema`

6. **Transform & Repeater:**
   - `ShapeTransformSchema`
   - `RepeaterOperatorSchema`

7. **Group (recursive):**
   - `ShapeGroupSchema` (uses `z.lazy()` for circular reference)

8. **Illustrator Operators (4 types):**
   - `SimplifyPathOperatorSchema`
   - `SmoothPathOperatorSchema`
   - `ExtrudeOperatorSchema`
   - `TraceOperatorSchema`

9. **Combined Types:**
   - `ShapeContentSchema` - Discriminated union of all 22+ types
   - `ShapeLayerDataSchema` - Final schema matching the interface

---

## Files Changed

1. **Created:** `ui/src/schemas/layers/shapes-schema.ts` (577 lines)
2. **Updated:** `ui/src/schemas/layers/layer-data-schema.ts`
   - Removed incorrect `ShapeLayerDataSchema`
   - Added import from `shapes-schema.ts`
3. **Updated:** `ui/src/schemas/layers/index.ts`
   - Removed non-existent `ShapeTypeSchema` export

---

## Technical Details

### Circular Reference Handling

`ShapeGroup` contains `ShapeContent[]`, and `ShapeContent` includes `ShapeGroup`, creating a circular reference. Solved using:

```typescript
// Forward declaration
let ShapeGroupSchema: z.ZodType<any>;

// ShapeContentSchema uses z.lazy() and references ShapeGroupSchema
export const ShapeContentSchema: z.ZodType<any> = z.lazy(() =>
  z.discriminatedUnion("type", [
    // ... all types including ShapeGroupSchema
  ])
);

// ShapeGroupSchema defined after, completing the circle
ShapeGroupSchema = z.lazy(() =>
  z.object({
    type: z.literal("group"),
    contents: z.array(ShapeContentSchema),
    // ...
  })
);
```

### Validation Boundaries

All numeric values use `.finite()` to reject NaN/Infinity:
- `finiteNumber` - Base finite number
- `positiveFinite` - Positive finite
- `nonNegativeFinite` - Non-negative finite
- `normalized01` - 0-1 range

---

## Testing Status

- ✅ No linting errors
- ✅ Schema compiles correctly
- ✅ Exports properly configured
- ⚠️ **TODO:** Test with actual ShapeLayerData instances
- ⚠️ **TODO:** Verify validation works correctly

---

## Next Steps

1. **Test the Schema:**
   ```typescript
   import { ShapeLayerDataSchema } from "@/schemas/layers/shapes-schema";
   
   const testData = {
     contents: [/* ... */],
     blendMode: "normal",
     quality: "normal",
     gpuAccelerated: true,
   };
   
   const result = ShapeLayerDataSchema.safeParse(testData);
   ```

2. **Create Missing Schemas:**
   - `types/effects.ts` (3,319 lines) - P0
   - `types/physics.ts` (990 lines) - P1
   - `types/layerStyles.ts` (721 lines) - P1

3. **Document Export Mappings:**
   - Map internal property names → export format property names
   - Document transformations for each target (Wan-Move, ATI, TTM, etc.)

---

## Related Documents

- `docs/CODEBASE_UNDERSTANDING.md` - Architecture overview
- `docs/SCHEMA_SPECIFICATION.md` - Complete schema reference
- `docs/MASTER_REFACTOR_PLAN.md` - Refactoring plan

---

*Fix completed: 2026-01-12*
