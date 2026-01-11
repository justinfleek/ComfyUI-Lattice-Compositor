# Layer Data Type Audit

**Date:** 2026-01-11
**Status:** Complete
**Scope:** 17 layer types using `as unknown as AnyLayerData` in layerDefaults.ts
**Methodology:** CODE IS TRUTH - types must match runtime behavior

## Summary

| Layer Type | Defaults Line | Mismatch Severity | Action |
|------------|---------------|-------------------|--------|
| text | 61-88 | LOW | Update type - make 5 fields optional |
| spline | 100-111 | HIGH | Update type - wrong property names |
| particles | 123-177 | MEDIUM | Update type - add missing optional fields |
| depthflow | 179-199 | LOW | Update type - nullable IDs |
| light | 201-212 | HIGH | Update type - penumbra→coneFeather |
| camera | 214-218 | LOW | Update type - nullable ID |
| image | 220-224 | MATCH | No changes needed |
| video | 226-232 | LOW | Update type - make fields optional |
| nestedComp | 247-254 | LOW | Update type - nullable ID, optional fields |
| matte | 256-265 | CRITICAL | **LayerDataMap wrong** - should be MatteLayerData |
| depth | 333-352 | MATCH | No changes needed |
| normal | 354-368 | MATCH | No changes needed |
| audio | 370-383 | MATCH | No changes needed |
| generated | 385-394 | MATCH | No changes needed |
| group | 396-402 | MATCH | No changes needed |
| particle | 404-415 | CRITICAL | **Create LegacyParticleData**, update LayerDataMap |
| effectLayer | 417-423 | MATCH | No changes needed |

---

## TEXT Layer

### Type Definition (types/text.ts)
Required fields not in defaults:
- `anchorPointGrouping: "character" | "word" | "line" | "all"`
- `groupingAlignment: { x: number; y: number }`
- `fillAndStroke: "fill-over-stroke" | "stroke-over-fill"`
- `interCharacterBlending: "normal" | "multiply" | "screen" | "overlay"`
- `perCharacter3D: boolean`

### Runtime Default (layerDefaults.ts line 61-88)
Does not include the 5 fields above.

### Code Usage Analysis
```typescript
// TextLayer.ts:276 - uses fallback default
anchorPointGrouping: data?.anchorPointGrouping ?? "character"
```
All 5 fields are read with fallback defaults in consuming code.

### Action Required
- [ ] Update TextData type: Make 5 fields optional with `?`

---

## SPLINE Layer

### Type Definition (types/spline.ts)
```typescript
strokeLineCap?: "butt" | "round" | "square"
strokeLineJoin?: "miter" | "round" | "bevel"
strokeDashArray?: number[] | AnimatableProperty<number[]>
strokeDashOffset?: number | AnimatableProperty<number>
fill: string  // REQUIRED
```

### Runtime Default (layerDefaults.ts line 100-111)
```typescript
lineCap: "round",
lineJoin: "round",
dashArray: "",
dashOffset: 0,
// fill: NOT PRESENT
```

### Code Usage Analysis
```
lineCap usage: 23 (ShapeLayer.ts, editors, composables)
strokeLineCap usage: 2 (ShapeProperties.vue only - for SHAPE layer, not spline)

lineJoin usage: 34
strokeLineJoin usage: 2

dashArray usage in SPLINE context:
- EnhancedLayerTrack.vue:537 → path: "data.dashArray"
- EnhancedLayerTrack.vue:540 → splineData.dashArray ?? ""
strokeDashArray usage: ShapeProperties.vue only (SHAPE layer context)
```

### Mismatches (CODE IS TRUTH)
| Type Says | Code Uses | Usage Count | Action |
|-----------|-----------|-------------|--------|
| strokeLineCap | lineCap | 23 vs 2 | **Update type → lineCap** |
| strokeLineJoin | lineJoin | 34 vs 2 | **Update type → lineJoin** |
| strokeDashArray | dashArray | 3 vs 0 in spline | **Update type → dashArray** |
| strokeDashOffset | dashOffset | similar | **Update type → dashOffset** |
| fill (required) | not present | - | **Make optional OR add default** |

### Action Required
- [ ] Update SplineData type: `strokeLineCap` → `lineCap`
- [ ] Update SplineData type: `strokeLineJoin` → `lineJoin`
- [ ] Update SplineData type: `strokeDashArray` → `dashArray`
- [ ] Update SplineData type: `strokeDashOffset` → `dashOffset`
- [ ] Update SplineData type: `fill` → `fill?` (make optional)

---

## PARTICLES Layer

### Type Definition (types/particles.ts - ParticleLayerData)
Required field not in defaults:
- `modulations: ParticleModulationConfig[]`

Fields in defaults not in type:
- `audioMappings`
- `exportEnabled`
- `exportFormat`

### Action Required
- [ ] Update ParticleLayerData: `modulations` → `modulations?`
- [ ] Update ParticleLayerData: Add `audioMappings?: AudioParticleMapping[]`
- [ ] Update ParticleLayerData: Add `exportEnabled?: boolean`
- [ ] Update ParticleLayerData: Add `exportFormat?: string`

---

## DEPTHFLOW Layer

### Type Definition
```typescript
sourceLayerId: string;  // NOT nullable
depthLayerId: string;   // NOT nullable
```

### Runtime Default
```typescript
sourceLayerId: null,
depthLayerId: null,
```

### Action Required
- [ ] Update DepthflowLayerData: `sourceLayerId: string | null`
- [ ] Update DepthflowLayerData: `depthLayerId: string | null`

---

## LIGHT Layer

### Type Definition (types/project.ts)
```typescript
penumbra?: number;  // WRONG NAME
```

### Code Usage
```typescript
// LightLayer.ts:387 - code uses coneFeather, maps to THREE.js penumbra
light.penumbra = (this.lightData.coneFeather ?? 50) / 100;

// LightProperties.vue - UI uses coneFeather
lightData.coneFeather ?? 50
```

### Mismatches (CODE IS TRUTH)
| Type Says | Code Uses | Usage Count | Action |
|-----------|-----------|-------------|--------|
| penumbra | coneFeather | 11 | **Update type → coneFeather** |

### Action Required
- [ ] Update LightLayerData: `penumbra` → `coneFeather`

---

## CAMERA Layer

### Type Definition
```typescript
cameraId: string;  // NOT nullable
```

### Runtime Default
```typescript
cameraId: null,
```

### Action Required
- [ ] Update CameraLayerData: `cameraId: string | null`

---

## IMAGE Layer

**MATCH** - Type and defaults align. No changes needed.

---

## VIDEO Layer

### Type Definition - Required fields not in defaults:
- `pingPong: boolean`
- `speedMapEnabled: boolean`
- `frameBlending: "none" | "frame-mix" | "pixel-motion"`
- `audioEnabled: boolean`
- `audioLevel: number`

### Code Usage Analysis
```typescript
// VideoLayer.ts:128 - all use fallback defaults
pingPong: data?.pingPong ?? false,
frameBlending: data?.frameBlending ?? "none",
```

### Action Required
- [ ] Update VideoData: Make `pingPong`, `speedMapEnabled`, `frameBlending`, `audioEnabled`, `audioLevel` optional

---

## NESTEDCOMP Layer

### Type Definition
```typescript
compositionId: string;  // NOT nullable
flattenTransform: boolean;  // REQUIRED
overrideFrameRate: boolean;  // REQUIRED
```

### Runtime Default
```typescript
compositionId: null,
// flattenTransform: NOT PRESENT
// overrideFrameRate: NOT PRESENT
```

### Action Required
- [ ] Update NestedCompData: `compositionId: string | null`
- [ ] Update NestedCompData: `flattenTransform?: boolean`
- [ ] Update NestedCompData: `overrideFrameRate?: boolean`

---

## MATTE Layer - CRITICAL

### LayerDataMap Says
```typescript
matte: ProceduralMatteData;
```

### ProceduralMatteData Structure
```typescript
{
  patternType: ProceduralMatteType;
  parameters: ProceduralMatteParams;
  animation: { enabled, speed, phase, direction };
  inverted: boolean;
  levels: { inputBlack, inputWhite, ... };
}
```

### Runtime Default Creates
```typescript
{
  matteType: "luminance",
  invert: false,
  threshold: 0.5,
  feather: 0,
  expansion: 0,
  sourceLayerId: null,
  previewMode: "matte",
}
```

### MatteLayerData Structure (EXISTS in project.ts!)
```typescript
export interface MatteLayerData {
  matteType: "luminance" | "alpha" | "red" | "green" | "blue" | "hue" | "saturation";
  invert: boolean;
  threshold: number;
  feather: number;
  expansion: number;
  // ...
}
```

### Analysis
**LayerDataMap is WRONG.** The defaults match `MatteLayerData`, not `ProceduralMatteData`.

### Action Required
- [ ] **Update LayerDataMap:** `matte: ProceduralMatteData` → `matte: MatteLayerData`

---

## DEPTH Layer

**MATCH** - Type and defaults align. No changes needed.

---

## NORMAL Layer

**MATCH** - Type and defaults align. No changes needed.

---

## AUDIO Layer

**MATCH** - Type and defaults align. No changes needed.

---

## GENERATED Layer

**MATCH** - Type and defaults align. No changes needed.

---

## GROUP Layer

**MATCH** - Type and defaults align. No changes needed.

---

## PARTICLE Layer (Legacy) - CRITICAL

### LayerDataMap Says
```typescript
particle: ParticleData;
```

### ParticleData Structure
```typescript
{
  emitter: ParticleEmitter;   // Complex nested object
  texture: ParticleTexture;   // Complex nested object
  physics: ParticlePhysics;   // Complex nested object
  rendering: ParticleRendering; // Complex nested object
}
```

### Runtime Default Creates
```typescript
{
  emitterType: "point",
  particleCount: 100,
  lifetime: 2.0,
  speed: 50,
  spread: 45,
  gravity: -9.8,
  color: "#ffffff",
  size: 5,
}
```

### Analysis
**Complete structural mismatch.** The defaults create a flat object; the type expects nested objects.
This is a legacy layer type (comment says "backwards compatibility").

### Action Required
- [ ] **Create new type:** `LegacyParticleData` matching the flat structure
- [ ] **Update LayerDataMap:** `particle: ParticleData` → `particle: LegacyParticleData`

---

## EFFECTLAYER Layer

**MATCH** - Type and defaults align. No changes needed.

---

# Execution Plan

## Phase 1: LayerDataMap Corrections
These fix the type system at its root.

### types/project.ts - LayerDataMap
```typescript
// Change:
matte: ProceduralMatteData → matte: MatteLayerData
particle: ParticleData → particle: LegacyParticleData
```

### types/particles.ts OR types/project.ts
```typescript
// ADD new type:
export interface LegacyParticleData {
  emitterType: "point" | "line" | "circle" | "box" | "path";
  particleCount: number;
  lifetime: number;
  speed: number;
  spread: number;
  gravity: number;
  color: string;
  size: number;
}
```

## Phase 2: Type Definition Updates (CODE IS TRUTH)

### types/spline.ts
```typescript
// Rename properties:
strokeLineCap → lineCap
strokeLineJoin → lineJoin
strokeDashArray → dashArray
strokeDashOffset → dashOffset
// Make optional:
fill → fill?
```

### types/project.ts - LightLayerData
```typescript
// Rename:
penumbra → coneFeather
```

### types/project.ts - Nullable IDs
```typescript
// DepthflowLayerData:
sourceLayerId: string | null
depthLayerId: string | null

// CameraLayerData:
cameraId: string | null

// NestedCompData:
compositionId: string | null
```

### types/project.ts - Optional fields
```typescript
// VideoData - make optional:
pingPong?: boolean
speedMapEnabled?: boolean
frameBlending?: "none" | "frame-mix" | "pixel-motion"
audioEnabled?: boolean
audioLevel?: number

// NestedCompData - make optional:
flattenTransform?: boolean
overrideFrameRate?: boolean
```

### types/text.ts - Optional fields
```typescript
anchorPointGrouping?: "character" | "word" | "line" | "all"
groupingAlignment?: { x: number; y: number }
fillAndStroke?: "fill-over-stroke" | "stroke-over-fill"
interCharacterBlending?: "normal" | "multiply" | "screen" | "overlay"
perCharacter3D?: boolean
```

### types/particles.ts - ParticleLayerData
```typescript
// Make optional:
modulations?: ParticleModulationConfig[]
// Add:
audioMappings?: AudioParticleMapping[]
exportEnabled?: boolean
exportFormat?: string
```

## Phase 3: Verify and Clean

1. Run `npx tsc --noEmit` after each change
2. Remove `as unknown as AnyLayerData` casts that become unnecessary
3. Remove `as any` casts on layer.data access where type guards work

---

**Audit Complete: 2026-01-11**
**Methodology: CODE IS TRUTH**
