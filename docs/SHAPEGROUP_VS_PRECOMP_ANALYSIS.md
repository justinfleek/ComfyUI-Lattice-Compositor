# ShapeGroup vs After Effects Precomps - What Would We Lose?

> **Date:** 2026-01-12  
> **Question:** "What functionality does After Effects have in pre-comps that we would lose by getting rid of ShapeGroup?"

---

## Critical Clarification

**ShapeGroup is NOT a precomp.** It's more like **Illustrator grouping** (organizes shapes within one layer).

**NestedComp is the After Effects precomp equivalent** (separate composition).

---

## What ShapeGroup Currently Does (and Doesn't Do)

### ✅ What ShapeGroup DOES:

1. **Organizes shapes within ONE ShapeLayer:**
   ```typescript
   ShapeLayer "Face"
     └─ ShapeGroup "Left Eye"
         ├─ EllipseShape (eyeball)
         ├─ FillShape (iris)
         └─ StrokeShape (outline)
   ```

2. **Has transform and blendMode properties:**
   ```typescript
   interface ShapeGroup {
     transform: ShapeTransform;  // Position, rotation, scale, opacity
     blendMode: string;           // Normal, multiply, screen, etc.
   }
   ```

### ❌ What ShapeGroup DOESN'T Do (Currently Broken):

1. **Transform is NOT applied:**
   ```typescript
   // ShapeLayer.ts:404-408
   for (const group of groups) {
     const groupPaths = this.evaluateContents(group.contents);
     result.push(...groupPaths); // Transform NOT applied!
   }
   ```

2. **BlendMode is NOT applied:**
   - Group's blendMode is ignored
   - Only layer-level blendMode works

3. **Cannot nest groups:**
   - Made non-recursive to break circular dependency
   - Groups cannot contain other groups

---

## What We'd Lose by Removing ShapeGroup

### ❌ Lost Functionality:

1. **Shape Organization:**
   - Cannot organize shapes within one layer
   - Would need separate ShapeLayers for each logical group
   - More layers = more overhead

2. **UI Organization:**
   - Cannot collapse/expand shape groups in UI
   - Cannot name groups for clarity
   - Harder to manage complex shape layers

3. **Potential Future Features (if we fix it):**
   - Group-level transforms (if implemented)
   - Group-level blend modes (if implemented)
   - Group-level effects (if implemented)

### ✅ What We WOULDN'T Lose:

1. **Precomp functionality:**
   - That's handled by **NestedComp**, not ShapeGroup
   - NestedComp provides all precomp features

2. **Global layer grouping:**
   - That's handled by **GroupLayer**, not ShapeGroup
   - GroupLayer groups any layer types together

---

## After Effects Precomp Features (NestedComp Equivalent)

### ✅ What NestedComp HAS (matches AE precomps):

1. **Separate Composition:**
   - ✅ Independent composition (`compositionId`)
   - ✅ Own timeline and layers
   - ✅ Can be reused multiple times

2. **Time Remapping:**
   - ✅ `speedMap` / `timeRemap` (maps parent time to nested time)
   - ✅ `timewarpSpeed` (animatable speed)
   - ✅ `timewarpMethod` (whole-frames, frame-mix, pixel-motion)

3. **Frame Rate Override:**
   - ✅ `overrideFrameRate` + `frameRate`
   - ✅ Frame rate conversion between parent and nested comp

4. **Transform Flattening:**
   - ✅ `flattenTransform` (render nested layers in parent's 3D space)
   - ✅ `combineTransforms` method

5. **ComfyUI Integration:**
   - ✅ Maps to sub-graphs in ComfyUI workflow
   - ✅ Workflow inputs/outputs per nested comp

### ❌ What NestedComp is MISSING (compared to AE):

1. **Collapse Transform / Continuously Rasterize:**
   - ❌ No "collapse transform" toggle (AE has this)
   - ❌ No "continuously rasterize" option (AE has this for vector layers)

2. **Quality Override:**
   - ❌ No per-nested-comp quality setting
   - ❌ No "draft" vs "final" quality toggle

3. **Motion Blur:**
   - ❌ No nested-comp-specific motion blur settings
   - ❌ Motion blur is layer-level only

4. **Blend Mode Inheritance:**
   - ❌ No "preserve underlying transparency" option
   - ❌ No "alpha additive" mode

5. **Composition Settings Override:**
   - ❌ Cannot override composition settings per instance
   - ❌ No per-instance resolution override

6. **Collapse / Expand in Timeline:**
   - ❌ No UI for collapsing nested comp layers in timeline
   - ❌ No "show nested layers" toggle

7. **Expressions:**
   - ❌ No `comp()` expression reference
   - ❌ Cannot reference parent comp from nested comp expressions

8. **Render Order:**
   - ❌ No "render before parent" option
   - ❌ No "render after parent" option

---

## ShapeGroup vs After Effects Shape Groups

### After Effects Shape Groups:

**AE has shape groups within shape layers** (similar to ShapeGroup):

1. **Transform IS applied:**
   - Group transform affects all children
   - Position, rotation, scale, opacity

2. **Blend Mode IS applied:**
   - Group blend mode affects how group composites
   - Can have different blend mode than layer

3. **Can nest groups:**
   - Groups can contain other groups
   - Unlimited nesting depth

4. **Group-level effects:**
   - Effects can be applied to groups
   - Affects all shapes in group

5. **Group-level masks:**
   - Masks can be applied to groups
   - Affects all shapes in group

### What ShapeGroup is Missing (compared to AE):

1. **Transform NOT applied:**
   - ❌ Group transform is ignored
   - ❌ Children don't inherit group transform

2. **Blend Mode NOT applied:**
   - ❌ Group blendMode is ignored
   - ❌ Only layer-level blendMode works

3. **Cannot nest groups:**
   - ❌ Made non-recursive (breaks circular dependency)
   - ❌ Groups cannot contain other groups

4. **No group-level effects:**
   - ❌ Effects are layer-level only
   - ❌ Cannot apply effects to groups

5. **No group-level masks:**
   - ❌ Masks are layer-level only
   - ❌ Cannot apply masks to groups

---

## The Answer: What Would We Lose?

### If We Remove ShapeGroup:

**We'd lose:**
- ✅ Shape organization within one layer
- ✅ UI grouping/collapsing for shapes
- ✅ Named groups for clarity
- ✅ Potential for group-level transforms (if we fix it)
- ✅ Potential for group-level blend modes (if we fix it)

**We WOULDN'T lose:**
- ❌ Precomp functionality (that's NestedComp)
- ❌ Global layer grouping (that's GroupLayer)
- ❌ Time remapping (that's NestedComp)
- ❌ Frame rate override (that's NestedComp)

### The Real Question:

**Should we fix ShapeGroup or remove it?**

**Option 1: Fix ShapeGroup** (make it work like AE shape groups):
- Apply transform to children
- Apply blendMode to group
- Allow nested groups (if needed)
- Add group-level effects (future)

**Option 2: Remove ShapeGroup** (use separate ShapeLayers):
- Each logical group = separate ShapeLayer
- Use GroupLayer to organize multiple ShapeLayers
- Simpler, but more layers = more overhead

**Option 3: Keep ShapeGroup** (as-is, just organization):
- Keep for UI organization only
- Don't apply transform/blendMode
- Accept that it's just a UI convenience

---

## ✅ FIXED: ShapeGroup Now Works Like After Effects

**Status:** ShapeGroup transform, blendMode, and opacity are now applied correctly.

### What Was Fixed:

1. **✅ Group transform is now applied to children:**
   ```typescript
   // ShapeLayer.ts:410-427
   const transformedPath = this.applyShapeTransform(
     evalPath.path,
     groupTransform,
   );
   ```
   - Position, rotation, scale, and anchor point are applied
   - Children inherit group transform

2. **✅ Group blendMode is now applied:**
   ```typescript
   // ShapeLayer.ts:809-815
   if (groupBlendMode && groupBlendMode !== "normal") {
     const compositeOp = this.getBlendModeCompositeOperation(groupBlendMode);
     if (compositeOp) {
       this.ctx.globalCompositeOperation = compositeOp;
     }
   }
   ```
   - Group blendMode affects how group composites with layers below
   - Supports: multiply, screen, overlay, darken, lighten, etc.

3. **✅ Group opacity is now applied:**
   ```typescript
   // ShapeLayer.ts:411-450
   const groupOpacity = this.getAnimatedValue(groupTransform.opacity) / 100;
   // Multiply existing opacities by group opacity
   ```
   - Group opacity multiplies fill/stroke opacities
   - Affects entire group uniformly

### What's Still Missing (Compared to AE):

1. **❌ Cannot nest groups:**
   - Groups cannot contain other groups (non-recursive)
   - Would require circular dependency handling

2. **❌ No group-level effects:**
   - Effects are layer-level only
   - Cannot apply effects to groups

3. **❌ No group-level masks:**
   - Masks are layer-level only
   - Cannot apply masks to groups

**Why Keep Non-Recursive:**
- Current implementation is simpler
- Matches most use cases
- Can be extended later if needed

---

*Created: 2026-01-12*  
*Purpose: Analyze what we'd lose by removing ShapeGroup vs what AE precomps provide*
