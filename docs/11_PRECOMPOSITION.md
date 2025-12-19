# WEYL COMPOSITOR — PRECOMPOSITION SYSTEM

**Document ID**: 11_PRECOMPOSITION  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md), [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md), [03_LAYER_SYSTEM.md](./03_LAYER_SYSTEM.md)

> A Precomp is a **fully evaluable sub-project** treated as a single layer.
> It is evaluated through MotionEngine, not rendered live.

---

## 1. WHAT IS A PRECOMP

A Precomposition ("Precomp") is:

> A **complete composition** that is treated as a **single layer** inside a parent composition.

This mirrors:
- **After Effects** Precomps
- **Nuke** Groups
- **TouchDesigner** Containers
- **DaVinci Resolve** Compound Clips

### 1.1 Precomp Characteristics

| Property | Description |
|----------|-------------|
| Own timeline | Independent frame range |
| Own layers | Complete layer stack |
| Own camera | Optional, can inherit parent |
| Deterministic | Evaluated at parent frame via MotionEngine |
| Returns | Complete FrameState as layer output |

---

## 2. CORE RULE

> **A precomp is evaluated exactly like a project — not rendered live, not simulated.**

```
Parent frame F
       ↓
Child frame f = timeMapping(F)
       ↓
MotionEngine.evaluate(f, childComposition)
       ↓
Frozen FrameState
       ↓
Returned as PrecompLayer output
```

---

## 3. PRECOMP LAYER MODEL

```typescript
interface PrecompLayer extends Layer {
  readonly type: 'precomp'
  readonly compositionId: string          // Reference to child composition
  readonly timeMapping: PrecompTimeMapping
  readonly inheritCamera: boolean         // Use parent's camera?
  readonly outputMode: PrecompOutputMode
}

interface PrecompTimeMapping {
  readonly mode: 'direct' | 'remap' | 'freeze'
  readonly offset: number                 // Frame offset
  readonly timeRemap?: AnimatableProperty<number>  // For 'remap' mode (0-1)
  readonly loop: boolean
  readonly pingPong: boolean
}

type PrecompOutputMode = 'rgba' | 'all'  // 'all' includes depth, normal, motion, mask
```

---

## 4. TIME MAPPING

### 4.1 Mapping Modes

| Mode | Description | Use Case |
|------|-------------|----------|
| `direct` | Parent frame = child frame + offset | Simple offset |
| `remap` | Animatable property maps to child timeline | Speed changes, reverse |
| `freeze` | Always evaluate at offset frame | Static snapshot |

### 4.2 Implementation

```typescript
function mapPrecompFrame(
  parentFrame: number,
  mapping: PrecompTimeMapping,
  childDuration: number
): number {
  let childFrame: number

  switch (mapping.mode) {
    case 'direct':
      childFrame = parentFrame + mapping.offset
      break

    case 'remap':
      // timeRemap is 0-1 normalized, maps to full child duration
      const t = interpolateProperty(mapping.timeRemap!, parentFrame)
      childFrame = t * (childDuration - 1)
      break

    case 'freeze':
      childFrame = mapping.offset
      break

    default:
      childFrame = parentFrame
  }

  // Handle looping
  if (mapping.loop && childFrame >= childDuration) {
    if (mapping.pingPong) {
      // 0→max→0→max... (bounce)
      const cycle = Math.floor(childFrame / childDuration)
      const phase = childFrame % childDuration
      childFrame = cycle % 2 === 0 ? phase : childDuration - 1 - phase
    } else {
      // 0→max→0→max... (restart)
      childFrame = childFrame % childDuration
    }
  }

  // Handle negative frames (from negative offset)
  if (childFrame < 0) {
    if (mapping.loop) {
      childFrame = (childFrame % childDuration + childDuration) % childDuration
    } else {
      childFrame = 0
    }
  }

  // Clamp to valid range
  return Math.max(0, Math.min(Math.floor(childFrame), childDuration - 1))
}
```

### 4.3 Time Remap Examples

```typescript
// Normal playback
const normal: PrecompTimeMapping = {
  mode: 'direct',
  offset: 0,
  loop: false,
  pingPong: false
}

// Half speed (100-frame precomp plays over 200 frames)
const halfSpeed: PrecompTimeMapping = {
  mode: 'remap',
  offset: 0,
  timeRemap: {
    keyframes: [
      { frame: 0, value: 0, interpolation: 'linear' },
      { frame: 200, value: 1, interpolation: 'linear' }
    ],
    defaultValue: 0
  },
  loop: false,
  pingPong: false
}

// Reverse playback
const reverse: PrecompTimeMapping = {
  mode: 'remap',
  offset: 0,
  timeRemap: {
    keyframes: [
      { frame: 0, value: 1, interpolation: 'linear' },
      { frame: 100, value: 0, interpolation: 'linear' }
    ],
    defaultValue: 1
  },
  loop: false,
  pingPong: false
}

// Loop with ping-pong
const pingPongLoop: PrecompTimeMapping = {
  mode: 'direct',
  offset: 0,
  loop: true,
  pingPong: true
}

// Freeze at frame 50
const freeze: PrecompTimeMapping = {
  mode: 'freeze',
  offset: 50,
  loop: false,
  pingPong: false
}
```

---

## 5. PRECOMP EVALUATION

### 5.1 Evaluation Function

```typescript
const MAX_PRECOMP_DEPTH = 10

function evaluatePrecompLayer(
  layer: PrecompLayer,
  parentFrame: number,
  project: WeylProject,
  audioAnalysis?: AudioAnalysis,
  depth: number = 0
): EvaluatedLayer {
  // 1. Check nesting depth
  if (depth >= MAX_PRECOMP_DEPTH) {
    throw new Error(`Precomp nesting depth exceeded (max ${MAX_PRECOMP_DEPTH})`)
  }

  // 2. Find child composition
  const childComp = project.compositions.find(c => c.id === layer.compositionId)
  if (!childComp) {
    throw new Error(`Precomp composition not found: ${layer.compositionId}`)
  }

  // 3. Detect circular references
  if (hasCircularReference(layer.compositionId, childComp, project)) {
    throw new Error(`Circular precomp reference detected: ${layer.compositionId}`)
  }

  // 4. Map parent frame to child frame
  const childFrame = mapPrecompFrame(
    parentFrame,
    layer.timeMapping,
    childComp.frameCount
  )

  // 5. Determine camera
  const cameraId = layer.inheritCamera ? undefined : childComp.activeCameraId

  // 6. Evaluate child composition through MotionEngine (recursive)
  const childFrameState = evaluateComposition(
    childFrame,
    childComp,
    project,
    audioAnalysis,
    cameraId,
    depth + 1  // Increment depth for nesting check
  )

  // 7. Evaluate this layer's transform
  const transform = evaluateTransform(layer.transform, parentFrame)

  // 8. Return as single evaluated layer
  return Object.freeze({
    id: layer.id,
    type: 'precomp',
    frame: parentFrame,
    visible: true,
    transform,
    blendMode: layer.blendMode,
    opacity: interpolateProperty(layer.opacity, parentFrame),
    content: Object.freeze({
      type: 'precomp',
      frameState: childFrameState,
      outputMode: layer.outputMode
    })
  })
}
```

### 5.2 Circular Reference Detection

```typescript
function hasCircularReference(
  targetId: string,
  composition: Composition,
  project: WeylProject,
  visited: Set<string> = new Set()
): boolean {
  if (visited.has(composition.id)) {
    return true
  }
  
  visited.add(composition.id)
  
  for (const layer of composition.layers) {
    if (layer.type === 'precomp') {
      const precompLayer = layer as PrecompLayer
      
      if (precompLayer.compositionId === targetId) {
        return true
      }
      
      const childComp = project.compositions.find(
        c => c.id === precompLayer.compositionId
      )
      
      if (childComp && hasCircularReference(targetId, childComp, project, visited)) {
        return true
      }
    }
  }
  
  return false
}
```

---

## 6. PRECOMP OUTPUT MODES

### 6.1 Output Configuration

```typescript
interface PrecompOutputConfig {
  readonly rgba: boolean    // Color + alpha
  readonly depth: boolean   // Z-depth buffer
  readonly normal: boolean  // Surface normals
  readonly motion: boolean  // Motion vectors
  readonly mask: boolean    // Binary mask
  readonly idMap: boolean   // Instance IDs
}
```

### 6.2 Use Cases

| Mode | Outputs | Use Case |
|------|---------|----------|
| `rgba` | Color + alpha only | Simple compositing |
| `all` | All buffers | Regional prompting, particle emission |

Precomp outputs can be used for:
- Parent particle systems (emit from precomp masks)
- ComfyUI regional conditioning
- Layered diffusion control (foreground/background separation)
- Depth-aware compositing

---

## 7. PRECOMP ISOLATION RULES

Precomps are **fully isolated**:

| Aspect | Behavior |
|--------|----------|
| Mutable state | ❌ No shared state with parent |
| Parent transforms | ❌ Not inherited (unless explicit) |
| RNG seeds | ❌ Not shared (unless explicitly linked) |
| Timeline | ✅ Own timeline |
| Layers | ✅ Own layer stack |
| Camera | ✅ Own camera (or inherited) |

### 7.1 Why Isolation Matters

```typescript
// ❌ FORBIDDEN: Shared state
precomp.particles = parent.particles  // NO shared particle state
precomp.rngSeed = parent.rngSeed      // NO inherited randomness

// ✅ REQUIRED: Full isolation
const childState = evaluateComposition(childFrame, childComp, project)
// childState is completely independent of parent evaluation
```

---

## 8. PRECOMP WITHIN PARTICLES

Precomps can be used as particle sprites:

```typescript
interface ParticleSystemConfig {
  // ... other config
  readonly sprite: {
    readonly type: 'image' | 'shape' | 'precomp'
    readonly precompId?: string  // If type === 'precomp'
  }
}
```

When a precomp is used as a particle sprite:
1. Each particle evaluates the precomp at its own age
2. Precomp frame = particle age (frames since birth)
3. Full isolation maintained per particle

---

## 9. FORBIDDEN PATTERNS

```typescript
// ❌ FORBIDDEN: Live rendering of precomp
precomp.render()
precomp.update(dt)

// ❌ FORBIDDEN: Shared mutable state
parent.layers.push(precomp.evaluatedLayers)  // NO merging

// ❌ FORBIDDEN: Evaluation outside MotionEngine
const result = precomp.evaluate(frame)  // Must go through MotionEngine

// ❌ FORBIDDEN: Circular reference
compA.layers = [precompB]
compB.layers = [precompA]  // CYCLE!

// ❌ FORBIDDEN: Infinite nesting
// 11+ levels of precomp nesting

// ✅ REQUIRED: MotionEngine evaluation
const childState = motionEngine.evaluate(childFrame, childComp, project)
```

---

## 10. TESTING REQUIREMENTS

```typescript
describe('Precomp Evaluation', () => {
  it('evaluates child composition through MotionEngine', () => {
    const spy = vi.spyOn(motionEngine, 'evaluate')
    
    evaluatePrecompLayer(precompLayer, 50, project)
    
    expect(spy).toHaveBeenCalledWith(
      expect.any(Number),  // Child frame
      childComp,
      project,
      undefined,
      expect.any(String),  // Camera ID
      1  // Depth
    )
  })

  it('maps time correctly', () => {
    const mapping: PrecompTimeMapping = {
      mode: 'remap',
      offset: 0,
      timeRemap: {
        keyframes: [
          { frame: 0, value: 0 },
          { frame: 100, value: 0.5 }
        ],
        defaultValue: 0
      },
      loop: false,
      pingPong: false
    }
    
    // At parent frame 100, child should be at frame 50 (half of 100-frame duration)
    const childFrame = mapPrecompFrame(100, mapping, 100)
    expect(childFrame).toBe(49)  // 0.5 * (100-1)
  })

  it('detects circular references', () => {
    const project = createProjectWithCircularPrecomps()
    
    expect(() => evaluatePrecompLayer(precompLayer, 0, project))
      .toThrow('Circular precomp reference')
  })

  it('enforces nesting depth limit', () => {
    const project = createDeeplyNestedPrecomps(15)
    
    expect(() => evaluatePrecompLayer(precompLayer, 0, project))
      .toThrow('nesting depth exceeded')
  })

  it('handles loop with pingPong', () => {
    const mapping: PrecompTimeMapping = {
      mode: 'direct',
      offset: 0,
      loop: true,
      pingPong: true
    }
    
    // 100-frame precomp
    expect(mapPrecompFrame(0, mapping, 100)).toBe(0)
    expect(mapPrecompFrame(99, mapping, 100)).toBe(99)
    expect(mapPrecompFrame(100, mapping, 100)).toBe(99)  // Bounce back
    expect(mapPrecompFrame(150, mapping, 100)).toBe(49)  // Midway back
    expect(mapPrecompFrame(199, mapping, 100)).toBe(0)   // Back to start
    expect(mapPrecompFrame(200, mapping, 100)).toBe(0)   // Forward again
  })

  it('returns frozen output', () => {
    const result = evaluatePrecompLayer(precompLayer, 50, project)
    
    expect(Object.isFrozen(result)).toBe(true)
    expect(Object.isFrozen(result.content)).toBe(true)
    expect(Object.isFrozen(result.content.frameState)).toBe(true)
  })
})
```

---

## 11. AUDIT CHECKLIST

Claude Code must verify:

- [ ] Precomps are evaluated through MotionEngine, not custom logic
- [ ] Time mapping is implemented correctly (direct, remap, freeze)
- [ ] Loop and pingPong work as expected
- [ ] Circular reference detection exists and works
- [ ] Nesting depth limit is enforced (max 10)
- [ ] Precomp isolation is maintained (no shared state)
- [ ] Child FrameState is frozen before return
- [ ] Camera inheritance works correctly
- [ ] Output modes are respected

**Any precomp evaluation outside of MotionEngine is a violation.**

---

**Previous**: [10_AUDIO_REACTIVITY.md](./10_AUDIO_REACTIVITY.md)  
**Next**: [12_COMPOSITION_IMPORT.md](./12_COMPOSITION_IMPORT.md)
