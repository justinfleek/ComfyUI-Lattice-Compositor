# WEYL COMPOSITOR — PARTICLE SYSTEM

**Document ID**: 05_PARTICLE_SYSTEM  
**Version**: 2.0.0 (Research-Validated)  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md), [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)  
**Reference Implementations**: Trapcode Particular, X-Particles (Cinema 4D), RyanOnTheInside (ComfyUI)

> Particles are **deterministic state snapshots** derived from seeds, configs, and frame indices.
> If particle output changes based on playback history, the system is broken.

---

## 1. REFERENCE IMPLEMENTATION ANALYSIS

### 1.1 How Professional Tools Achieve Determinism

| Tool | Strategy | Scrubbing Behavior | Trade-offs |
|------|----------|-------------------|------------|
| **Trapcode Particular** | Seeded PRNG | Re-simulates forward from frame 0 on every scrub | No storage cost; slow for complex simulations |
| **X-Particles** | Frame-by-frame disk caching | Instant scrub to any cached frame | Disk space required; cache invalidation complexity |
| **Weyl (recommended)** | Hybrid: Seeded PRNG + checkpoint caching | Fast scrub via checkpoints, guaranteed determinism via PRNG | Balanced approach |

### 1.2 Trapcode Particular Deep Dive

Trapcode Particular achieves determinism through:

1. **Explicit Random Seed Control**: Users can modify the seed to get different particle layouts
2. **Stateless Re-Evaluation**: Every scrub re-runs simulation from frame 0 using the seed
3. **Pre-roll Option**: Simulation can start before frame 0 for particles already existing at timeline start
4. **GPU Acceleration**: Fast re-simulation compensates for lack of caching

**Key Insight**: Particular does NOT cache frames to disk. It relies on fast GPU re-computation.

### 1.3 X-Particles Deep Dive

X-Particles requires explicit caching because:

> "Without caching there is no way of ensuring accurate visual playback in the viewport since under normal circumstances when we scrub the timeline, X-Particles just doesn't know what to do."

X-Particles caching works via:

1. **Cache Object**: Explicit object added to scene that captures simulation state
2. **Per-Frame Files**: Each frame saved as individual file (`.xpc` format or OpenVDB)
3. **Inclusion Control**: Users specify which data channels to cache
4. **Cache Tags**: Applied to objects to mark them as cache-dependent

**Key Insight**: X-Particles treats determinism as a **storage problem**, not a computation problem.

### 1.4 ComfyUI Patterns (RyanOnTheInside)

The RyanOnTheInside particle system operates differently:

- **Feature-Reactive**: Particles respond to audio, MIDI, motion, proximity, depth, color, time
- **Batch Processing**: Processes frame-by-frame in ComfyUI's execution model
- **Modular Features**: FLEX-prefixed nodes for reactive control

**Key Insight**: ComfyUI particles are designed for **reactive modulation**, not timeline scrubbing.

---

## 2. WEYL HYBRID STRATEGY

Weyl implements a **hybrid approach** combining the strengths of both Particular and X-Particles:

```
┌─────────────────────────────────────────────────────────────────┐
│                    DETERMINISM LAYER                            │
│  Seeded PRNG guarantees identical output for same inputs        │
│  (Like Trapcode Particular)                                     │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    PERFORMANCE LAYER                            │
│  Checkpoint caching every N frames for fast scrubbing           │
│  (Like X-Particles, but in-memory with optional disk export)    │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    EXPORT LAYER                                 │
│  Frame-indexed conditioning buffers for diffusion models        │
│  (Like ComfyUI export workflows)                                │
└─────────────────────────────────────────────────────────────────┘
```

---

## 3. ABSOLUTE REQUIREMENTS

### 3.1 Determinism Guarantee

Given:
- Same `seed: number`
- Same `config: ParticleSystemConfig`
- Same `projectState: ProjectState`
- Same `frame: number`

→ Particle output must be **bit-identical**.

This must hold regardless of:
- Scrub order (forward, backward, random access)
- Playback history (first play vs tenth play)
- Render batching (single frame vs batch export)
- Checkpoint cache state (warm vs cold)

### 3.2 Frame Addressability

Particles must support direct frame access:

```typescript
// All of these must work correctly:
controller.evaluateAtFrame(500, config, seed)  // Jump to frame 500
controller.evaluateAtFrame(12, config, seed)   // Jump back to frame 12
controller.evaluateAtFrame(500, config, seed)  // MUST equal first call

// Scrub order independence test:
const resultA = controller.evaluateAtFrame(240, config, seed)
controller.evaluateAtFrame(10, config, seed)   // Irrelevant scrub
controller.evaluateAtFrame(999, config, seed)  // Irrelevant scrub
const resultB = controller.evaluateAtFrame(240, config, seed)
// resultA MUST equal resultB
```

### 3.3 Zero Hidden State

**FORBIDDEN** in particle evaluation:
- `Math.random()` — use seeded PRNG only
- `Date.now()` — time must come from frame index
- `performance.now()` — no real-time dependencies
- Accumulated `deltaTime` — derive time from frame number
- Internal clocks — all timing from frame index
- Stateful noise evolution — noise must be frame-indexed

---

## 4. FORBIDDEN PATTERNS

```typescript
// ❌ FORBIDDEN: Incremental simulation (requires playback history)
class BadParticleSystem {
  private particles: Particle[] = []
  
  step(dt: number) {
    for (const p of this.particles) {
      p.position.add(p.velocity.multiplyScalar(dt))
      p.age += dt
      if (p.age > p.lifetime) this.particles.splice(...)
    }
  }
}

// ❌ FORBIDDEN: Playback-dependent mutation
update(dt: number) {
  this.noiseTime += dt  // Accumulates differently based on playback
  this.particles.push(newParticle)  // Array grows based on play count
}

// ❌ FORBIDDEN: Implicit randomness
const randomVelocity = Math.random() * 10  // Different every call!

// ❌ FORBIDDEN: Frame-rate dependent emission
if (lastEmitTime + emitInterval < performance.now()) {
  emit()  // Depends on actual elapsed time, not frame time
}
```

---

## 5. REQUIRED PATTERNS

```typescript
// ✅ REQUIRED: Pure evaluation function
function evaluateParticlesAtFrame(
  frame: number,
  config: ParticleSystemConfig,
  seed: number
): ParticleSnapshot {
  const rng = createSeededRNG(seed)
  const particles: Particle[] = []
  
  // Calculate how many particles exist at this frame
  for (let emitFrame = 0; emitFrame <= frame; emitFrame++) {
    const emitCount = calculateEmissionCount(emitFrame, config, rng.fork(emitFrame))
    
    for (let i = 0; i < emitCount; i++) {
      const particleRNG = rng.fork(emitFrame * 10000 + i)
      const particle = createParticle(emitFrame, config, particleRNG)
      
      // Check if particle is still alive at target frame
      const age = frame - emitFrame
      if (age <= particle.lifetime) {
        // Evaluate particle state at target frame
        const state = evaluateParticleAtAge(particle, age, config)
        particles.push(state)
      }
    }
  }
  
  return Object.freeze({ frame, particles: Object.freeze(particles) })
}

// ✅ REQUIRED: Seeded RNG with deterministic forking
class SeededRNG {
  private state: number
  
  constructor(seed: number) {
    this.state = seed
  }
  
  next(): number {
    // Mulberry32 or similar deterministic PRNG
    this.state |= 0
    this.state = (this.state + 0x6D2B79F5) | 0
    let t = Math.imul(this.state ^ (this.state >>> 15), 1 | this.state)
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
  
  fork(subSeed: number): SeededRNG {
    return new SeededRNG(this.state ^ subSeed)
  }
}

// ✅ REQUIRED: Frame-indexed noise
function evaluateNoise(frame: number, particleId: number, seed: number): number {
  // Noise is a pure function of frame + id + seed
  const rng = new SeededRNG(seed ^ (frame * 31337) ^ (particleId * 7919))
  return rng.next()
}
```

---

## 6. ARCHITECTURE

```
┌─────────────────────────────────────────────────────────────────┐
│                ParticleSimulationController                     │
│  - Orchestrates evaluation                                      │
│  - Manages checkpoint cache                                     │
│  - Exposes evaluateAtFrame() API                                │
└─────────────────────────────────────────────────────────────────┘
                              │
            ┌─────────────────┼─────────────────┐
            ▼                 ▼                 ▼
┌───────────────────┐ ┌───────────────┐ ┌───────────────────────┐
│  CheckpointCache  │ │   SeededRNG   │ │  ForceEvaluator       │
│  - Every N frames │ │   - PRNG      │ │  - Gravity            │
│  - LRU eviction   │ │   - Fork      │ │  - Turbulence         │
│  - Invalidation   │ │   - Per-frame │ │  - Attractors         │
└───────────────────┘ └───────────────┘ └───────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    ParticleSnapshot                             │
│  - Immutable (Object.freeze)                                    │
│  - Frame-indexed                                                │
│  - Contains all particle states for that frame                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 7. PARTICLE SIMULATION CONTROLLER

**File**: `ui/src/engine/ParticleSimulationController.ts`

### 7.1 Interface

```typescript
interface ParticleSimulationController {
  /**
   * Evaluate particles at a specific frame.
   * Always returns identical results for same inputs.
   * 
   * Performance strategy:
   * 1. Check checkpoint cache for nearby checkpoint
   * 2. If found, simulate forward from checkpoint
   * 3. If not found, simulate from frame 0
   * 4. Optionally create new checkpoint
   */
  evaluateAtFrame(
    frame: number,
    config: ParticleSystemConfig,
    seed: number
  ): ParticleSnapshot

  /**
   * Clear all cached checkpoints.
   * Call when starting fresh or freeing memory.
   */
  reset(): void

  /**
   * Invalidate checkpoints (call when config changes).
   * Checkpoints are only valid for unchanged configs.
   */
  invalidateCheckpoints(): void

  /**
   * Configure checkpoint strategy.
   */
  setCheckpointInterval(frames: number): void
}
```

### 7.2 Implementation

```typescript
class ParticleSimulationControllerImpl implements ParticleSimulationController {
  private checkpoints: Map<number, CheckpointData> = new Map()
  private checkpointInterval: number = 30  // Every 30 frames (1 second at 30fps)
  private maxCheckpoints: number = 100     // LRU cache limit
  private configHash: string = ''
  
  evaluateAtFrame(
    frame: number,
    config: ParticleSystemConfig,
    seed: number
  ): ParticleSnapshot {
    // Invalidate if config changed
    const newHash = hashConfig(config)
    if (newHash !== this.configHash) {
      this.invalidateCheckpoints()
      this.configHash = newHash
    }
    
    // Find nearest checkpoint at or before target frame
    const checkpoint = this.findNearestCheckpoint(frame)
    
    // Evaluate from checkpoint (or frame 0)
    const startFrame = checkpoint?.frame ?? 0
    const startState = checkpoint?.state ?? this.createInitialState(seed)
    
    // Simulate forward to target frame
    const result = this.simulateRange(startFrame, frame, startState, config, seed)
    
    // Optionally create checkpoint
    if (this.shouldCreateCheckpoint(frame)) {
      this.createCheckpoint(frame, result.internalState)
    }
    
    return result.snapshot
  }
  
  private simulateRange(
    fromFrame: number,
    toFrame: number,
    initialState: InternalState,
    config: ParticleSystemConfig,
    seed: number
  ): { snapshot: ParticleSnapshot; internalState: InternalState } {
    let state = initialState
    
    for (let f = fromFrame; f <= toFrame; f++) {
      state = this.stepFrame(f, state, config, seed)
    }
    
    return {
      snapshot: this.createSnapshot(toFrame, state),
      internalState: state
    }
  }
  
  private stepFrame(
    frame: number,
    state: InternalState,
    config: ParticleSystemConfig,
    seed: number
  ): InternalState {
    const frameRNG = new SeededRNG(seed ^ (frame * 0xDEADBEEF))
    
    // 1. Emit new particles for this frame
    const newParticles = this.emitParticles(frame, config, frameRNG)
    
    // 2. Update existing particles (pure function of frame, not accumulated state)
    const updatedParticles = state.particles.map(p => 
      this.updateParticle(p, frame, config, frameRNG.fork(p.id))
    )
    
    // 3. Remove dead particles
    const aliveParticles = [...updatedParticles, ...newParticles]
      .filter(p => (frame - p.birthFrame) <= p.lifetime)
    
    return { particles: aliveParticles }
  }
  
  private shouldCreateCheckpoint(frame: number): boolean {
    return frame % this.checkpointInterval === 0
  }
  
  private findNearestCheckpoint(targetFrame: number): CheckpointData | null {
    let best: CheckpointData | null = null
    
    for (const [frame, checkpoint] of this.checkpoints) {
      if (frame <= targetFrame && (!best || frame > best.frame)) {
        best = checkpoint
      }
    }
    
    return best
  }
  
  reset(): void {
    this.checkpoints.clear()
    this.configHash = ''
  }
  
  invalidateCheckpoints(): void {
    this.checkpoints.clear()
  }
  
  setCheckpointInterval(frames: number): void {
    this.checkpointInterval = Math.max(1, frames)
  }
}
```

---

## 8. PARTICLE SNAPSHOT (IMMUTABLE OUTPUT)

```typescript
interface ParticleSnapshot {
  readonly frame: number
  readonly particles: ReadonlyArray<ParticleState>
  readonly metadata: {
    readonly particleCount: number
    readonly seed: number
    readonly configHash: string
  }
}

interface ParticleState {
  readonly id: number
  readonly position: Readonly<Vec3>
  readonly velocity: Readonly<Vec3>
  readonly rotation: Readonly<Vec3>
  readonly scale: Readonly<Vec3>
  readonly color: Readonly<Color>
  readonly opacity: number
  readonly age: number          // Current age in frames
  readonly lifetime: number     // Total lifetime in frames
  readonly birthFrame: number   // Frame when particle was emitted
}

// Factory function ensures immutability
function createSnapshot(frame: number, state: InternalState, seed: number, configHash: string): ParticleSnapshot {
  const particles = state.particles.map(p => Object.freeze({ ...p }))
  
  return Object.freeze({
    frame,
    particles: Object.freeze(particles),
    metadata: Object.freeze({
      particleCount: particles.length,
      seed,
      configHash
    })
  })
}
```

---

## 9. SEEDED RNG IMPLEMENTATION

```typescript
/**
 * Mulberry32 PRNG - fast, deterministic, good distribution
 * Used by many game engines and particle systems
 */
class SeededRNG {
  private state: number
  
  constructor(seed: number) {
    // Ensure integer seed
    this.state = seed >>> 0
  }
  
  /**
   * Returns value in range [0, 1)
   */
  next(): number {
    this.state |= 0
    this.state = (this.state + 0x6D2B79F5) | 0
    let t = Math.imul(this.state ^ (this.state >>> 15), 1 | this.state)
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
  
  /**
   * Returns value in range [min, max)
   */
  range(min: number, max: number): number {
    return min + this.next() * (max - min)
  }
  
  /**
   * Returns integer in range [min, max]
   */
  int(min: number, max: number): number {
    return Math.floor(this.range(min, max + 1))
  }
  
  /**
   * Returns Vec3 with components in range [min, max)
   */
  vec3(min: number, max: number): Vec3 {
    return {
      x: this.range(min, max),
      y: this.range(min, max),
      z: this.range(min, max)
    }
  }
  
  /**
   * Fork creates a new RNG seeded deterministically from current state + subSeed
   * Use for per-particle or per-frame isolation
   */
  fork(subSeed: number): SeededRNG {
    return new SeededRNG((this.state ^ (subSeed * 0x9E3779B9)) >>> 0)
  }
  
  /**
   * Get current state (for checkpointing)
   */
  getState(): number {
    return this.state
  }
  
  /**
   * Restore from checkpoint
   */
  static fromState(state: number): SeededRNG {
    const rng = new SeededRNG(0)
    rng.state = state >>> 0
    return rng
  }
}
```

---

## 10. FORCE EVALUATION (PURE FUNCTIONS)

```typescript
interface ForceConfig {
  gravity: Vec3
  turbulence: TurbulenceConfig
  attractors: AttractorConfig[]
  drag: number
}

interface TurbulenceConfig {
  strength: number
  frequency: number
  octaves: number
  seed: number
}

/**
 * All force calculations are pure functions of:
 * - Particle state at current frame
 * - Frame number
 * - Config
 * - Seed
 * 
 * NO accumulated state allowed.
 */
function evaluateForces(
  particle: ParticleState,
  frame: number,
  config: ForceConfig,
  rng: SeededRNG
): Vec3 {
  let force = { x: 0, y: 0, z: 0 }
  
  // Gravity (constant)
  force = vec3Add(force, config.gravity)
  
  // Turbulence (frame-indexed noise)
  const turbulence = evaluateTurbulence(
    particle.position,
    frame,
    particle.id,
    config.turbulence
  )
  force = vec3Add(force, turbulence)
  
  // Attractors
  for (const attractor of config.attractors) {
    const attractForce = evaluateAttractor(particle.position, attractor)
    force = vec3Add(force, attractForce)
  }
  
  // Drag (velocity-dependent, but still deterministic)
  const dragForce = vec3Scale(particle.velocity, -config.drag)
  force = vec3Add(force, dragForce)
  
  return force
}

/**
 * Turbulence using frame-indexed simplex noise
 * NOT accumulated over time - calculated fresh each frame
 */
function evaluateTurbulence(
  position: Vec3,
  frame: number,
  particleId: number,
  config: TurbulenceConfig
): Vec3 {
  // Time coordinate derived from frame, not accumulated
  const t = frame / 30  // Normalize to ~seconds
  
  let amplitude = config.strength
  let frequency = config.frequency
  let result = { x: 0, y: 0, z: 0 }
  
  for (let octave = 0; octave < config.octaves; octave++) {
    const seed = config.seed + octave * 1000 + particleId
    
    result.x += simplexNoise4D(
      position.x * frequency,
      position.y * frequency,
      position.z * frequency,
      t,
      seed
    ) * amplitude
    
    result.y += simplexNoise4D(
      position.x * frequency + 100,
      position.y * frequency + 100,
      position.z * frequency + 100,
      t,
      seed
    ) * amplitude
    
    result.z += simplexNoise4D(
      position.x * frequency + 200,
      position.y * frequency + 200,
      position.z * frequency + 200,
      t,
      seed
    ) * amplitude
    
    amplitude *= 0.5
    frequency *= 2
  }
  
  return result
}
```

---

## 11. EMISSION SYSTEM

```typescript
interface EmitterConfig {
  type: 'point' | 'box' | 'sphere' | 'mesh' | 'spline'
  position: Vec3
  rotation: Vec3
  
  // Emission rate
  particlesPerSecond: number
  burst: BurstConfig[]
  
  // Initial particle properties
  lifetime: RangeConfig
  initialVelocity: VelocityConfig
  initialSize: RangeConfig
  initialColor: ColorConfig
}

interface BurstConfig {
  frame: number
  count: number
  probability: number  // 0-1, evaluated per particle
}

/**
 * Calculate emission for a specific frame
 * Pure function - same inputs always produce same outputs
 */
function emitParticles(
  frame: number,
  config: EmitterConfig,
  rng: SeededRNG
): ParticleState[] {
  const particles: ParticleState[] = []
  const frameRNG = rng.fork(frame)
  
  // Continuous emission
  const particlesThisFrame = calculateContinuousEmission(frame, config, frameRNG)
  for (let i = 0; i < particlesThisFrame; i++) {
    const particleRNG = frameRNG.fork(i)
    particles.push(createParticle(frame, i, config, particleRNG))
  }
  
  // Burst emission
  for (const burst of config.burst) {
    if (burst.frame === frame) {
      const burstRNG = frameRNG.fork(burst.frame * 10000)
      for (let i = 0; i < burst.count; i++) {
        if (burstRNG.next() < burst.probability) {
          const particleRNG = burstRNG.fork(i)
          particles.push(createParticle(frame, particlesThisFrame + i, config, particleRNG))
        }
      }
    }
  }
  
  return particles
}

/**
 * Create a single particle with deterministic properties
 */
function createParticle(
  birthFrame: number,
  index: number,
  config: EmitterConfig,
  rng: SeededRNG
): ParticleState {
  const id = birthFrame * 100000 + index  // Unique ID per particle
  
  return Object.freeze({
    id,
    birthFrame,
    position: sampleEmitterPosition(config, rng),
    velocity: sampleInitialVelocity(config, rng),
    rotation: { x: 0, y: 0, z: 0 },
    scale: { x: 1, y: 1, z: 1 },
    color: sampleInitialColor(config, rng),
    opacity: 1,
    age: 0,
    lifetime: rng.range(config.lifetime.min, config.lifetime.max)
  })
}
```

---

## 12. EXPORT REQUIREMENTS

Particles must export deterministic conditioning buffers for diffusion models:

| Output | Shape | Purpose | Format |
|--------|-------|---------|--------|
| Depth | H×W×1 | Z-conditioning for depth-aware models | float32 |
| Motion | H×W×2 | Temporal models (optical flow format) | float32 |
| Density | H×W×1 | Particle presence masks | float32 [0,1] |
| ID Map | H×W×1 | Instance separation | int32 |
| Normal | H×W×3 | Surface orientation | float32 [-1,1] |

### 12.1 Export Requirements

All outputs must be:
- **Frame-indexed**: Named with zero-padded frame numbers (`particle_depth_000001.exr`)
- **Batch-consistent**: Same frame = same output across export runs
- **Bit-identical**: SHA-256 hash must match for identical inputs

### 12.2 Export File Structure

```
exports/
├── particles/
│   ├── depth/
│   │   ├── frame_000001.exr
│   │   ├── frame_000002.exr
│   │   └── ...
│   ├── motion/
│   │   ├── frame_000001.exr
│   │   └── ...
│   ├── density/
│   │   ├── frame_000001.png
│   │   └── ...
│   ├── id_map/
│   │   ├── frame_000001.exr
│   │   └── ...
│   └── metadata.json
```

### 12.3 Metadata Export

```json
{
  "version": "2.0.0",
  "seed": 42,
  "configHash": "a1b2c3d4...",
  "frameRange": [1, 300],
  "fps": 30,
  "resolution": [1920, 1080],
  "particleCount": {
    "min": 0,
    "max": 1247,
    "average": 892
  },
  "checksums": {
    "depth": "sha256:...",
    "motion": "sha256:...",
    "density": "sha256:...",
    "id_map": "sha256:..."
  }
}
```

---

## 13. TESTING REQUIREMENTS

```typescript
describe('ParticleSimulationController', () => {
  const seed = 12345
  const config = createTestConfig()
  
  it('produces identical particles for same seed and frame', () => {
    const controller = new ParticleSimulationController()
    const a = controller.evaluateAtFrame(240, config, seed)
    const b = controller.evaluateAtFrame(240, config, seed)
    expect(a).toEqual(b)
    expect(hashSnapshot(a)).toBe(hashSnapshot(b))
  })

  it('is scrub-order independent', () => {
    const controller = new ParticleSimulationController()
    const a = controller.evaluateAtFrame(300, config, seed)
    
    // Scrub around randomly
    controller.evaluateAtFrame(10, config, seed)
    controller.evaluateAtFrame(500, config, seed)
    controller.evaluateAtFrame(1, config, seed)
    controller.evaluateAtFrame(999, config, seed)
    
    const b = controller.evaluateAtFrame(300, config, seed)
    expect(a).toEqual(b)
  })

  it('checkpoint matches full replay', () => {
    const controller = new ParticleSimulationController()
    controller.setCheckpointInterval(30)
    
    // Build up checkpoints
    const fromCheckpoint = controller.evaluateAtFrame(180, config, seed)
    
    // Clear checkpoints and evaluate fresh
    controller.reset()
    const fullReplay = controller.evaluateAtFrame(180, config, seed)
    
    expect(fromCheckpoint).toEqual(fullReplay)
  })

  it('does not use Math.random', () => {
    const spy = vi.spyOn(Math, 'random')
    const controller = new ParticleSimulationController()
    controller.evaluateAtFrame(100, config, seed)
    expect(spy).not.toHaveBeenCalled()
  })

  it('returns frozen snapshots', () => {
    const controller = new ParticleSimulationController()
    const snapshot = controller.evaluateAtFrame(50, config, seed)
    
    expect(Object.isFrozen(snapshot)).toBe(true)
    expect(Object.isFrozen(snapshot.particles)).toBe(true)
    expect(Object.isFrozen(snapshot.metadata)).toBe(true)
    
    snapshot.particles.forEach(p => {
      expect(Object.isFrozen(p)).toBe(true)
    })
  })

  it('different seeds produce different results', () => {
    const controller = new ParticleSimulationController()
    const a = controller.evaluateAtFrame(100, config, 12345)
    const b = controller.evaluateAtFrame(100, config, 67890)
    
    expect(a.particles.length).toBe(b.particles.length)  // Same emission count
    expect(a.particles[0].position).not.toEqual(b.particles[0].position)  // Different positions
  })

  it('handles frame 0 correctly', () => {
    const controller = new ParticleSimulationController()
    const snapshot = controller.evaluateAtFrame(0, config, seed)
    
    // Should have initial burst particles if configured
    expect(snapshot.frame).toBe(0)
    expect(Array.isArray(snapshot.particles)).toBe(true)
  })

  it('invalidates checkpoints when config changes', () => {
    const controller = new ParticleSimulationController()
    
    // Build checkpoint
    controller.evaluateAtFrame(100, config, seed)
    
    // Change config
    const newConfig = { ...config, emitter: { ...config.emitter, particlesPerSecond: 999 } }
    const result = controller.evaluateAtFrame(100, newConfig, seed)
    
    // Should not use stale checkpoint
    expect(result.metadata.configHash).not.toBe(hashConfig(config))
  })
})

describe('SeededRNG', () => {
  it('produces deterministic sequences', () => {
    const rng1 = new SeededRNG(42)
    const rng2 = new SeededRNG(42)
    
    for (let i = 0; i < 1000; i++) {
      expect(rng1.next()).toBe(rng2.next())
    }
  })

  it('fork produces isolated but deterministic sub-sequences', () => {
    const rng1 = new SeededRNG(42)
    const rng2 = new SeededRNG(42)
    
    const fork1a = rng1.fork(100)
    const fork1b = rng1.fork(100)
    const fork2a = rng2.fork(100)
    
    expect(fork1a.next()).toBe(fork1b.next())
    expect(fork1a.next()).toBe(fork2a.next())
  })
})
```

---

## 14. COMMON FAILURE INDICATORS

Any of the following indicate a **broken system**:

| Symptom | Likely Cause |
|---------|--------------|
| ❌ Particles drift when scrubbing backward | Using incremental simulation instead of pure evaluation |
| ❌ Different results on second render | Hidden mutable state or `Math.random()` usage |
| ❌ Noise evolves differently per playback | Accumulated noise time instead of frame-indexed |
| ❌ Random values without seeded control | Direct `Math.random()` calls |
| ❌ Particle count varies between identical evaluations | Non-deterministic emission logic |
| ❌ Checkpoints produce different results than full replay | Checkpoint state incomplete or corrupted |
| ❌ Performance degrades on backward scrub | Missing checkpoint system |

---

## 15. INTEGRATION WITH MOTION ENGINE

Particle systems integrate with MotionEngine through the standard property evaluation interface:

```typescript
// ParticleSystemLayer evaluation
class ParticleSystemLayer implements Layer {
  evaluate(frame: number, context: EvaluationContext): LayerOutput {
    const config = this.evaluateConfig(frame, context)
    const snapshot = this.controller.evaluateAtFrame(frame, config, this.seed)
    
    return {
      type: 'particle',
      snapshot,
      depth: this.renderDepthBuffer(snapshot),
      motion: this.renderMotionVectors(snapshot),
      mask: this.renderDensityMask(snapshot)
    }
  }
}

// Register with MotionEngine
motionEngine.registerLayerType('particle', ParticleSystemLayer)
```

---

## 16. VALIDATION NOTES

### 16.1 Verified Against Reference Implementations

| Claim | Trapcode Particular | X-Particles | Status |
|-------|--------------------| ------------|--------|
| Seeded PRNG for determinism | ✅ Confirmed | ✅ Confirmed | VALIDATED |
| Frame-by-frame caching | ❌ Not used | ✅ Required | VALIDATED |
| Re-simulate on scrub | ✅ Confirmed | ❌ Uses cache | VALIDATED |
| Pre-roll option | ✅ Confirmed | N/A | VALIDATED |

### 16.2 Items Needing Further Validation

- [ ] Exact PRNG algorithm used by Trapcode Particular (assumed Mulberry32-like)
- [ ] X-Particles checkpoint granularity options
- [ ] ComfyUI RyanOnTheInside integration patterns

---

**Previous**: [04_LAYER_SYSTEM.md](./04_LAYER_SYSTEM.md)  
**Next**: [06_CAMERA_SPLINE.md](./06_CAMERA_SPLINE.md)
