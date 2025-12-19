# WEYL COMPOSITOR — LAYER SYSTEM

**Document ID**: 03_LAYER_SYSTEM  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md), [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)

> Layers are **data** that produces output at a frame.
> They are not living objects that evolve over time.

---

## 1. CORE PRINCIPLE

> **Layers are EVALUATED, not UPDATED.**

A layer at frame N is a pure function of:
- Project data
- Frame number N
- Property values (resolved by MotionEngine)

There is **no concept of**:
- "Previous frame"
- "Next frame"
- "Delta time"
- "Accumulated state"

---

## 2. LAYER LIFECYCLE

### 2.1 Authoring Phase (UI)

During editing in the UI:
- Layers store **data only** (keyframes, configuration)
- No evaluation occurs
- No runtime state exists
- Changes modify project data

### 2.2 Evaluation Phase (Engine)

During evaluation by MotionEngine:
- Layers are **read-only data**
- MotionEngine evaluates layer properties
- Layer produces an **EvaluatedLayer**
- EvaluatedLayer is **frozen and immutable**

**The same layer data + same frame = same EvaluatedLayer. Always.**

---

## 3. LAYER CATEGORIES

### 3.1 Primitive Layers

Primitive layers **generate content directly**.

| Type | Content |
|------|---------|
| `solid` | Solid color rectangle |
| `image` | Static image from asset |
| `video` | Video frame from asset |
| `text` | Text rendered from font |
| `shape` | Vector graphics |
| `particle` | Particle system snapshot |

### 3.2 Structural Layers

Structural layers **organize** but don't produce visible content.

| Type | Purpose |
|------|---------|
| `null` | Transform parent (invisible) |
| `camera` | Camera definition |
| `light` | Light definition |

### 3.3 Effect Layers

Effect layers **modify** other layers.

| Type | Effect |
|------|--------|
| `adjustment` | Apply effects to layers below |
| `precomp` | Nested composition as layer |

---

## 4. LAYER EVALUATION

### 4.1 Evaluation Function

```typescript
function evaluateLayer(
  layer: Layer,
  frame: number,
  propertyValues: Map<string, unknown>,
  composition: Composition
): EvaluatedLayer | null {
  // Check visibility
  if (!isLayerVisibleAtFrame(layer, frame)) {
    return null
  }
  
  // Evaluate transform
  const transform = evaluateTransform(layer.transform, frame, propertyValues)
  
  // Evaluate layer-specific content
  const content = evaluateLayerContent(layer, frame, propertyValues)
  
  // Compose result
  return Object.freeze({
    id: layer.id,
    type: layer.type,
    frame,
    visible: true,
    transform,
    blendMode: layer.blendMode,
    opacity: transform.opacity,
    content
  })
}
```

### 4.2 Visibility Check

```typescript
function isLayerVisibleAtFrame(layer: Layer, frame: number): boolean {
  // Check frame range
  if (frame < layer.startFrame || frame > layer.endFrame) {
    return false
  }
  
  // Check visibility property (may be animated)
  const visible = interpolateProperty(layer.visible, frame)
  return visible
}
```

### 4.3 Content Evaluation by Type

```typescript
function evaluateLayerContent(
  layer: Layer,
  frame: number,
  propertyValues: Map<string, unknown>
): LayerContent {
  switch (layer.type) {
    case 'solid':
      return evaluateSolidContent(layer as SolidLayer, frame, propertyValues)
    case 'image':
      return evaluateImageContent(layer as ImageLayer, frame)
    case 'video':
      return evaluateVideoContent(layer as VideoLayer, frame, propertyValues)
    case 'text':
      return evaluateTextContent(layer as TextLayer, frame, propertyValues)
    case 'shape':
      return evaluateShapeContent(layer as ShapeLayer, frame, propertyValues)
    case 'particle':
      return evaluateParticleContent(layer as ParticleLayer, frame)
    case 'null':
      return { type: 'null' }
    case 'camera':
      return { type: 'camera' }
    case 'precomp':
      return evaluatePrecompContent(layer as PrecompLayer, frame)
    default:
      throw new Error(`Unknown layer type: ${layer.type}`)
  }
}
```

---

## 5. COMPOSITION PIPELINE

### 5.1 Composition Order

Layers are composited bottom-to-top:

```
Layer Stack (in project):
  0: Background  (bottom)
  1: Midground
  2: Foreground  (top)

Render Order:
  Background renders first
  Midground composites over Background
  Foreground composites over result
```

### 5.2 Composition Steps

For each layer (bottom to top):

```
1. Layer Output
   └── Render layer content at frame
   
2. Apply Masks
   └── Multiply by mask alpha
   
3. Apply Opacity
   └── Multiply by layer opacity
   
4. Apply Blend Mode
   └── Blend with layers below using specified mode
   
5. Apply Transform
   └── Position, rotate, scale relative to anchor
```

### 5.3 Blend Mode Implementation

```typescript
function blendLayers(
  bottom: ImageBuffer,
  top: ImageBuffer,
  mode: BlendMode
): ImageBuffer {
  switch (mode) {
    case 'normal':
      return normalBlend(bottom, top)
    case 'add':
      return additiveBlend(bottom, top)
    case 'multiply':
      return multiplyBlend(bottom, top)
    case 'screen':
      return screenBlend(bottom, top)
    // ... other modes
  }
}

// All blend functions must be pure
function normalBlend(bottom: Color, top: Color, topAlpha: number): Color {
  return {
    x: bottom.x * (1 - topAlpha) + top.x * topAlpha,
    y: bottom.y * (1 - topAlpha) + top.y * topAlpha,
    z: bottom.z * (1 - topAlpha) + top.z * topAlpha,
    w: bottom.w * (1 - topAlpha) + top.w * topAlpha
  }
}
```

---

## 6. TRANSFORM HIERARCHY

### 6.1 Parent-Child Relationships

Layers can have parent layers via `parentId`.

```typescript
function resolveWorldTransform(
  layer: Layer,
  frame: number,
  layers: Map<string, EvaluatedLayer>
): Mat4 {
  // Get local transform
  const local = evaluateTransform(layer.transform, frame)
  
  // If no parent, local is world
  if (!layer.parentId) {
    return local.matrix
  }
  
  // Get parent's world transform
  const parent = layers.get(layer.parentId)
  if (!parent) {
    console.warn(`Parent layer not found: ${layer.parentId}`)
    return local.matrix
  }
  
  // Combine: parent * local
  return multiplyMat4(parent.transform.matrix, local.matrix)
}
```

### 6.2 Transform Order

Transforms apply in this order:
1. Translate by negative anchor
2. Scale
3. Rotate (Z, then Y, then X)
4. Translate by position
5. Apply parent transform (if any)

---

## 7. MASKING

### 7.1 Mask Application

```typescript
function applyMasks(
  layerOutput: ImageBuffer,
  maskIds: readonly string[],
  evaluatedLayers: Map<string, EvaluatedLayer>
): ImageBuffer {
  if (!maskIds || maskIds.length === 0) {
    return layerOutput
  }
  
  let result = layerOutput
  
  for (const maskId of maskIds) {
    const maskLayer = evaluatedLayers.get(maskId)
    if (!maskLayer) continue
    
    const maskAlpha = extractAlpha(maskLayer.content)
    result = multiplyAlpha(result, maskAlpha)
  }
  
  return result
}
```

### 7.2 Mask Modes

| Mode | Behavior |
|------|----------|
| `alpha` | Use mask alpha channel |
| `luma` | Use mask luminance |
| `inverted` | Invert mask result |

---

## 8. LAYER-SPECIFIC EVALUATION

### 8.1 Solid Layer

```typescript
function evaluateSolidContent(
  layer: SolidLayer,
  frame: number,
  propertyValues: Map<string, unknown>
): SolidContent {
  const color = getOrInterpolate(layer.color, propertyValues, frame)
  
  return Object.freeze({
    type: 'solid',
    color,
    width: layer.width,
    height: layer.height
  })
}
```

### 8.2 Image Layer

```typescript
function evaluateImageContent(
  layer: ImageLayer,
  frame: number
): ImageContent {
  return Object.freeze({
    type: 'image',
    assetId: layer.assetId
    // Image data is resolved by RenderEngine
  })
}
```

### 8.3 Video Layer

```typescript
function evaluateVideoContent(
  layer: VideoLayer,
  frame: number,
  propertyValues: Map<string, unknown>
): VideoContent {
  // Calculate video frame
  let videoFrame = frame - layer.startFrame
  
  // Apply time remap if present
  if (layer.timeRemap) {
    const remappedTime = getOrInterpolate(layer.timeRemap, propertyValues, frame)
    videoFrame = Math.floor(remappedTime * videoAsset.frameRate)
  }
  
  // Handle looping
  if (layer.loop && videoFrame >= videoAsset.frameCount) {
    videoFrame = videoFrame % videoAsset.frameCount
  }
  
  return Object.freeze({
    type: 'video',
    assetId: layer.assetId,
    videoFrame: Math.max(0, Math.min(videoFrame, videoAsset.frameCount - 1))
  })
}
```

---

## 9. FORBIDDEN PATTERNS

```typescript
// ❌ FORBIDDEN: Layer state
class Layer {
  private currentFrame: number  // NO!
  update(dt: number) { ... }    // NO!
}

// ❌ FORBIDDEN: Mutation during evaluation
function evaluateLayer(layer) {
  layer.evaluatedTransform = ...  // NO!
  layer.lastFrame = frame         // NO!
}

// ❌ FORBIDDEN: Frame dependency
function evaluateLayer(layer, frame) {
  const prev = layer.getEvaluatedAt(frame - 1)  // NO!
  return prev + delta                            // NO!
}

// ✅ REQUIRED: Pure evaluation
function evaluateLayer(layer, frame, propertyValues) {
  const transform = evaluateTransform(layer.transform, frame, propertyValues)
  return Object.freeze({ ...layer, transform })
}
```

---

## 10. TESTING REQUIREMENTS

```typescript
describe('Layer Evaluation', () => {
  it('same frame produces identical result', () => {
    const a = evaluateLayer(layer, 100, props, comp)
    const b = evaluateLayer(layer, 100, props, comp)
    expect(a).toEqual(b)
  })

  it('respects visibility bounds', () => {
    const layer = { startFrame: 10, endFrame: 20, ... }
    expect(evaluateLayer(layer, 5, props, comp)).toBeNull()
    expect(evaluateLayer(layer, 15, props, comp)).not.toBeNull()
    expect(evaluateLayer(layer, 25, props, comp)).toBeNull()
  })

  it('returns frozen output', () => {
    const result = evaluateLayer(layer, 100, props, comp)
    expect(Object.isFrozen(result)).toBe(true)
  })

  it('composites in correct order', () => {
    const result = compositeLayers([bg, fg], 100)
    // Foreground should be on top
    expect(result.topLayer).toBe(fg.id)
  })
})
```

---

## 11. AUDIT CHECKLIST

Claude Code must verify:

- [ ] Layers are data structures, not classes with methods
- [ ] No `update()`, `tick()`, or `step()` methods on layers
- [ ] No runtime state stored on layers
- [ ] Layer evaluation is pure function
- [ ] Transform hierarchy computed correctly
- [ ] Blend modes are pure functions
- [ ] Masking applies correctly
- [ ] All outputs are frozen

**Any stateful layer code is a violation.**

---

**Previous**: [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)  
**Next**: [04_PARTICLE_SYSTEM.md](./04_PARTICLE_SYSTEM.md)
