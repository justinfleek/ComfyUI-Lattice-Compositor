# WEYL COMPOSITOR — PICKWHIP & DEPENDENCY GRAPH

**Document ID**: 09_PICKWHIP_DEPENDENCIES  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md), [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)

> All property dependencies form a **Directed Acyclic Graph (DAG)**.
> Evaluation order is determined by topological sort. Cycles are hard errors.

---

## 1. PURPOSE

Pickwhip enables explicit dataflow relationships between properties.

Conceptually equivalent to:
- **After Effects** pickwhip expressions
- **Nuke** expressions
- **TouchDesigner** parameter linking
- **Houdini** parameter references

**Pickwhip does NOT mean scripting or live evaluation.**
**It means declaring dependencies.**

---

## 2. CORE PRINCIPLES

### 2.1 DAG Requirement

All property dependencies form a **Directed Acyclic Graph (DAG)**.

```
┌─────────────┐     ┌─────────────┐
│  Audio      │────▶│  Layer A    │
│  Analysis   │     │  Scale      │
└─────────────┘     └──────┬──────┘
                           │
                           ▼
┌─────────────┐     ┌─────────────┐
│  Layer A    │────▶│  Layer B    │
│  Position   │     │  Opacity    │
└─────────────┘     └─────────────┘

✅ Valid: Directed Acyclic Graph
```

There must **NEVER** be:

```
┌─────────────┐     ┌─────────────┐
│  Layer A    │◀───▶│  Layer B    │
│  Position   │     │  Opacity    │
└─────────────┘     └─────────────┘

❌ Invalid: Cycle detected
```

### 2.2 What Pickwhip IS

| Aspect | Description |
|--------|-------------|
| Reference | A pointer from one property to another |
| Dependency | Declares that A depends on B |
| Static edge | Resolved at evaluation time |
| Data flow | Enables property linking |

### 2.3 What Pickwhip IS NOT

| Forbidden | Why |
|-----------|-----|
| JavaScript evaluation | Non-deterministic, security risk |
| Runtime callbacks | Creates hidden state |
| Per-frame mutation | Violates purity |
| Expression side effects | Violates determinism |

---

## 3. PROPERTY PATH MODEL

All properties must be addressable via stable paths.

```typescript
interface PropertyPath {
  readonly layerId: string
  readonly property: string  // Dot notation: 'transform.position.x'
}

// Examples
const positionX: PropertyPath = {
  layerId: 'layer-abc123',
  property: 'transform.position.x'
}

const opacity: PropertyPath = {
  layerId: 'layer-def456',
  property: 'opacity'
}

const cameraFov: PropertyPath = {
  layerId: 'camera-main',
  property: 'fov'
}

const textContent: PropertyPath = {
  layerId: 'text-title',
  property: 'content'
}
```

### 3.1 Path Rules

| Rule | Description |
|------|-------------|
| Resolvable | Must resolve to a value at evaluation time |
| Immutable | Paths are static identifiers |
| No dynamic strings | No string interpolation or runtime construction |
| Type-aware | Path must match property type |

---

## 4. PROPERTY DRIVER MODEL

Pickwhip relationships are stored as **drivers**.

```typescript
interface PropertyDriver {
  readonly source: PropertyPath | AudioSourcePath
  readonly transform?: MappingFunction
}

interface AudioSourcePath {
  readonly type: 'audio'
  readonly feature: 'amplitude' | 'rms' | 'spectrum' | 'beat' | 'onset'
  readonly band?: number  // For spectrum bands (0-N)
}
```

### 4.1 Driver Examples

```typescript
// Simple link: Layer B opacity = Layer A position.x
const simpleDriver: PropertyDriver = {
  source: { layerId: 'layer-a', property: 'transform.position.x' }
}

// With transform: Layer B scale = Audio amplitude * 2
const audioDriver: PropertyDriver = {
  source: { type: 'audio', feature: 'amplitude' },
  transform: (value, frame) => 1 + value * 2
}

// Mapped link: Layer B rotation = Layer A position.y * 0.5
const mappedDriver: PropertyDriver = {
  source: { layerId: 'layer-a', property: 'transform.position.y' },
  transform: (value, frame) => value * 0.5
}

// Spectrum band: Layer C opacity = Mid frequencies
const spectrumDriver: PropertyDriver = {
  source: { type: 'audio', feature: 'spectrum', band: 5 },
  transform: (value, frame) => Math.min(1, value * 3)
}
```

---

## 5. MAPPING FUNCTIONS

Mapping functions must be **pure**.

```typescript
type MappingFunction = (value: number, frame: number) => number
```

### 5.1 Valid Mapping Functions

```typescript
// ✅ VALID: Pure functions (same inputs = same output)

const scale: MappingFunction = (v, f) => v * 2

const offset: MappingFunction = (v, f) => v + 100

const sine: MappingFunction = (v, f) => Math.sin(f * 0.1) * v

const clamp: MappingFunction = (v, f) => Math.max(0, Math.min(1, v))

const remap: MappingFunction = (v, f) => {
  const inMin = 0, inMax = 100
  const outMin = 0, outMax = 1
  return (v - inMin) / (inMax - inMin) * (outMax - outMin) + outMin
}

const easeInOut: MappingFunction = (v, f) => {
  const t = v
  return t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2
}

const frameModulated: MappingFunction = (v, f) => {
  // Frame-based oscillation (deterministic)
  return v * (1 + Math.sin(f * 0.05) * 0.5)
}
```

### 5.2 Invalid Mapping Functions

```typescript
// ❌ FORBIDDEN: Impure functions

// Random values
const random: MappingFunction = (v, f) => v * Math.random()

// Real time
const timeDependent: MappingFunction = (v, f) => v * Date.now()

// External state
let accumulator = 0
const stateful: MappingFunction = (v, f) => { 
  accumulator += v
  return accumulator 
}

// DOM access
const domBased: MappingFunction = (v, f) => {
  return v * document.querySelector('#slider').value
}

// Async
const asyncBased: MappingFunction = async (v, f) => {
  return await fetchValue(v)
}
```

---

## 6. DEPENDENCY GRAPH CONSTRUCTION

### 6.1 Building the Graph

```typescript
interface DependencyGraph {
  readonly nodes: Map<string, PropertyNode>
  readonly edges: Map<string, string[]>  // nodeId → dependsOn[]
}

interface PropertyNode {
  readonly id: string  // pathToKey(PropertyPath)
  readonly path: PropertyPath
  readonly driver?: PropertyDriver
}

function buildDependencyGraph(composition: Composition): DependencyGraph {
  const nodes = new Map<string, PropertyNode>()
  const edges = new Map<string, string[]>()
  
  // 1. Collect all properties
  for (const layer of composition.layers) {
    const properties = collectAnimatableProperties(layer)
    for (const prop of properties) {
      const key = pathToKey(prop.path)
      nodes.set(key, {
        id: key,
        path: prop.path,
        driver: prop.driver
      })
    }
  }
  
  // 2. Build edges from drivers
  for (const [key, node] of nodes) {
    const deps: string[] = []
    
    if (node.driver) {
      if ('layerId' in node.driver.source) {
        // Property dependency
        const depKey = pathToKey(node.driver.source)
        deps.push(depKey)
      }
      // Audio sources have no property dependencies
    }
    
    edges.set(key, deps)
  }
  
  return { nodes, edges }
}
```

### 6.2 Cycle Detection

```typescript
function detectCycles(graph: DependencyGraph): string[] | null {
  const visited = new Set<string>()
  const recursionStack = new Set<string>()
  const cyclePath: string[] = []
  
  function dfs(nodeId: string): boolean {
    visited.add(nodeId)
    recursionStack.add(nodeId)
    
    const deps = graph.edges.get(nodeId) || []
    for (const dep of deps) {
      if (!visited.has(dep)) {
        if (dfs(dep)) {
          cyclePath.unshift(nodeId)
          return true
        }
      } else if (recursionStack.has(dep)) {
        cyclePath.unshift(dep, nodeId)
        return true
      }
    }
    
    recursionStack.delete(nodeId)
    return false
  }
  
  for (const nodeId of graph.nodes.keys()) {
    if (!visited.has(nodeId)) {
      if (dfs(nodeId)) {
        return cyclePath
      }
    }
  }
  
  return null  // No cycles
}
```

### 6.3 Topological Sort

```typescript
function topologicalSort(graph: DependencyGraph): string[] {
  // Check for cycles first
  const cycle = detectCycles(graph)
  if (cycle) {
    throw new Error(`Circular dependency detected: ${cycle.join(' → ')}`)
  }
  
  const visited = new Set<string>()
  const result: string[] = []
  
  function visit(nodeId: string): void {
    if (visited.has(nodeId)) return
    visited.add(nodeId)
    
    const deps = graph.edges.get(nodeId) || []
    for (const dep of deps) {
      visit(dep)
    }
    
    result.push(nodeId)
  }
  
  for (const nodeId of graph.nodes.keys()) {
    visit(nodeId)
  }
  
  return result  // Dependencies before dependents
}
```

---

## 7. EVALUATION ORDER

### 7.1 Evaluation Flow

```
1. Build dependency graph
       ↓
2. Detect cycles (fail if found)
       ↓
3. Topological sort
       ↓
4. Evaluate in sorted order
       ↓
5. Store results in values map
       ↓
6. Apply to FrameState
```

### 7.2 Evaluation Implementation

```typescript
function evaluateProperties(
  composition: Composition,
  frame: number,
  audioAnalysis?: AudioAnalysis
): Map<string, unknown> {
  const graph = buildDependencyGraph(composition)
  const evalOrder = topologicalSort(graph)
  const values = new Map<string, unknown>()
  
  for (const nodeId of evalOrder) {
    const node = graph.nodes.get(nodeId)!
    
    if (node.driver) {
      // Evaluate driver
      const sourceValue = resolveSource(
        node.driver.source,
        values,
        frame,
        audioAnalysis
      )
      
      // Apply transform if present
      const finalValue = node.driver.transform
        ? node.driver.transform(sourceValue, frame)
        : sourceValue
      
      values.set(nodeId, finalValue)
    } else {
      // No driver - interpolate from keyframes
      const property = resolveProperty(composition, node.path)
      const value = interpolateProperty(property, frame)
      values.set(nodeId, value)
    }
  }
  
  return values
}

function resolveSource(
  source: PropertyPath | AudioSourcePath,
  values: Map<string, unknown>,
  frame: number,
  audioAnalysis?: AudioAnalysis
): number {
  if ('type' in source && source.type === 'audio') {
    // Audio source
    if (!audioAnalysis) {
      return 0  // Fallback when no audio
    }
    return getAudioFeature(audioAnalysis, source, frame)
  } else {
    // Property source
    const key = pathToKey(source as PropertyPath)
    const value = values.get(key)
    if (value === undefined) {
      throw new Error(`Property not yet evaluated: ${key}`)
    }
    return value as number
  }
}
```

---

## 8. AUDIO AS SOURCE

Audio features are read-only source nodes in the dependency graph.

### 8.1 Audio Source Properties

| Property | Description |
|----------|-------------|
| No dependencies | Audio is a root node |
| Pre-computed | Analysis happens at import |
| Frame-indexed | Direct lookup, no computation |
| Read-only | Cannot be driven by properties |

### 8.2 Available Audio Features

```typescript
interface AudioAnalysis {
  readonly sampleRate: number
  readonly frameRate: number
  readonly frameCount: number
  
  readonly features: {
    readonly amplitude: Float32Array   // Per-frame amplitude
    readonly rms: Float32Array         // Per-frame RMS
    readonly spectrum: Float32Array[]  // Per-frame spectrum bands
    readonly beats: number[]           // Beat frame indices
    readonly onsets: number[]          // Onset frame indices
  }
}

function getAudioFeature(
  analysis: AudioAnalysis,
  source: AudioSourcePath,
  frame: number
): number {
  const clampedFrame = Math.max(0, Math.min(frame, analysis.frameCount - 1))
  
  switch (source.feature) {
    case 'amplitude':
      return analysis.features.amplitude[clampedFrame]
    case 'rms':
      return analysis.features.rms[clampedFrame]
    case 'spectrum':
      const band = source.band ?? 0
      return analysis.features.spectrum[clampedFrame]?.[band] ?? 0
    case 'beat':
      return analysis.features.beats.includes(clampedFrame) ? 1 : 0
    case 'onset':
      return analysis.features.onsets.includes(clampedFrame) ? 1 : 0
    default:
      return 0
  }
}
```

---

## 9. MULTI-COMPONENT PROPERTIES

Vector properties (position, rotation, scale) must be decomposed for independent drivers.

```typescript
// Example: Position with different drivers per component
interface PositionWithDrivers {
  x: {
    keyframes: Keyframe<number>[]
    driver?: PropertyDriver  // Driven by audio
  }
  y: {
    keyframes: Keyframe<number>[]
    driver?: PropertyDriver  // Driven by another layer
  }
  z: {
    keyframes: Keyframe<number>[]
    // No driver - just keyframes
  }
}

// In project data
const layer = {
  transform: {
    position: {
      x: { 
        keyframes: [{ frame: 0, value: 0 }],
        driver: { source: { type: 'audio', feature: 'amplitude' } }
      },
      y: {
        keyframes: [{ frame: 0, value: 100 }],
        driver: { source: { layerId: 'other', property: 'transform.rotation.z' } }
      },
      z: {
        keyframes: [{ frame: 0, value: 0 }]  // No driver
      }
    }
  }
}
```

---

## 10. EXPRESSION PRESETS

Common mapping patterns can be provided as presets.

```typescript
const MAPPING_PRESETS = {
  // Scale value
  scale: (factor: number): MappingFunction => 
    (v, f) => v * factor,
  
  // Add offset
  offset: (amount: number): MappingFunction => 
    (v, f) => v + amount,
  
  // Remap range
  remap: (inMin: number, inMax: number, outMin: number, outMax: number): MappingFunction =>
    (v, f) => (v - inMin) / (inMax - inMin) * (outMax - outMin) + outMin,
  
  // Clamp to range
  clamp: (min: number, max: number): MappingFunction =>
    (v, f) => Math.max(min, Math.min(max, v)),
  
  // Smooth step
  smoothstep: (edge0: number, edge1: number): MappingFunction =>
    (v, f) => {
      const t = Math.max(0, Math.min(1, (v - edge0) / (edge1 - edge0)))
      return t * t * (3 - 2 * t)
    },
  
  // Frame-based oscillation
  oscillate: (frequency: number, amplitude: number): MappingFunction =>
    (v, f) => v + Math.sin(f * frequency) * amplitude,
  
  // Invert (useful for audio)
  invert: (): MappingFunction =>
    (v, f) => 1 - v,
  
  // Power curve
  power: (exponent: number): MappingFunction =>
    (v, f) => Math.pow(v, exponent)
}
```

---

## 11. FALLBACK BEHAVIOR

If a dependency cannot be resolved:

| Condition | Action |
|-----------|--------|
| Missing source property | Log warning, use keyframed value |
| Missing audio analysis | Return 0 for audio features |
| Invalid path | Log error, use default |
| Type mismatch | Log error, use default |

```typescript
function resolvePropertyWithFallback(
  composition: Composition,
  path: PropertyPath,
  values: Map<string, unknown>,
  frame: number
): unknown {
  const key = pathToKey(path)
  
  // Check if already evaluated
  if (values.has(key)) {
    return values.get(key)
  }
  
  try {
    const property = resolveProperty(composition, path)
    return interpolateProperty(property, frame)
  } catch (error) {
    console.warn(`Failed to resolve ${key}: ${error.message}. Using default.`)
    return getPropertyDefault(path)
  }
}

function getPropertyDefault(path: PropertyPath): unknown {
  // Defaults based on property type
  if (path.property.includes('position')) return 0
  if (path.property.includes('scale')) return 1
  if (path.property.includes('rotation')) return 0
  if (path.property.includes('opacity')) return 1
  if (path.property.includes('color')) return { r: 1, g: 1, b: 1, a: 1 }
  return 0
}
```

**Determinism must still hold even with fallbacks.**

---

## 12. FORBIDDEN PATTERNS

```typescript
// ❌ FORBIDDEN: Cycles
layerA.position.driver = { source: { layerId: 'layerB', property: 'opacity' } }
layerB.opacity.driver = { source: { layerId: 'layerA', property: 'position.x' } }

// ❌ FORBIDDEN: Self-reference
layer.scale.driver = { source: { layerId: layer.id, property: 'scale.x' } }

// ❌ FORBIDDEN: Runtime evaluation of expressions
const value = eval(expression)

// ❌ FORBIDDEN: Non-deterministic mapping
const random: MappingFunction = (v, f) => v * Math.random()

// ❌ FORBIDDEN: Dynamic property resolution
const path = `layer-${someVariable}.transform.position`

// ✅ REQUIRED: Static dependencies
const driver: PropertyDriver = {
  source: { layerId: 'layer-abc', property: 'transform.position.x' },
  transform: (v, f) => v * 2  // Pure function
}
```

---

## 13. TESTING REQUIREMENTS

```typescript
describe('Dependency Graph', () => {
  it('evaluates properties in dependency order', () => {
    // B.opacity depends on A.position.x
    const project = createProject({
      layers: [
        { id: 'A', transform: { position: { x: { keyframes: [{ frame: 0, value: 50 }] } } } },
        { id: 'B', opacity: { keyframes: [], driver: { 
          source: { layerId: 'A', property: 'transform.position.x' },
          transform: (v, f) => v / 100
        } } }
      ]
    })
    
    const result = motionEngine.evaluate(0, project)
    expect(result.layers[1].opacity).toBe(0.5)  // 50 / 100
  })

  it('detects cycles', () => {
    const cyclicProject = createProject({
      layers: [
        { id: 'A', opacity: { driver: { source: { layerId: 'B', property: 'opacity' } } } },
        { id: 'B', opacity: { driver: { source: { layerId: 'A', property: 'opacity' } } } }
      ]
    })
    
    expect(() => motionEngine.evaluate(0, cyclicProject))
      .toThrow('Circular dependency')
  })

  it('handles audio sources', () => {
    const audioAnalysis = createMockAudioAnalysis()
    audioAnalysis.features.amplitude[50] = 0.8
    
    const project = createProject({
      layers: [{
        id: 'A',
        transform: {
          scale: {
            x: { keyframes: [], driver: {
              source: { type: 'audio', feature: 'amplitude' },
              transform: (v, f) => 1 + v
            } }
          }
        }
      }]
    })
    
    const result = motionEngine.evaluate(50, project, audioAnalysis)
    expect(result.layers[0].transform.scale.x).toBeCloseTo(1.8)
  })

  it('mapping functions are deterministic', () => {
    const a = motionEngine.evaluate(100, project)
    const b = motionEngine.evaluate(100, project)
    expect(a).toEqual(b)
  })

  it('topological sort produces correct order', () => {
    // C depends on B, B depends on A
    const graph = buildDependencyGraph(composition)
    const order = topologicalSort(graph)
    
    const indexA = order.indexOf('A.position')
    const indexB = order.indexOf('B.opacity')
    const indexC = order.indexOf('C.scale')
    
    expect(indexA).toBeLessThan(indexB)
    expect(indexB).toBeLessThan(indexC)
  })
})
```

---

## 14. AUDIT CHECKLIST

Claude Code must verify:

- [ ] All property dependencies form a DAG (no cycles)
- [ ] Cycle detection runs before evaluation
- [ ] Topological sort determines evaluation order
- [ ] All mapping functions are pure
- [ ] Audio features are pre-computed, not runtime-sampled
- [ ] Multi-component properties can have independent drivers
- [ ] Fallback behavior maintains determinism
- [ ] No JavaScript `eval()` or dynamic code execution
- [ ] Property paths are static, not dynamically constructed
- [ ] Driver sources are validated at project load time

**Any cycle in the dependency graph is a critical error.**

---

**Previous**: [08_TIMELINE_GRAPH.md](./08_TIMELINE_GRAPH.md)  
**Next**: [10_AUDIO_REACTIVITY.md](./10_AUDIO_REACTIVITY.md)
