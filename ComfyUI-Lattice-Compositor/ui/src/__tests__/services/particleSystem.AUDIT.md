# PARTICLE SYSTEM AUDIT

**Started:** 2026-01-06
**Last Updated:** 2026-01-06 16:35
**Status:** IN PROGRESS (4 of 22 files fully audited + 1 GPU shader + 3 related fixes)
**Total Lines:** ~13,000 across 22 core files
**Lines Audited:** ~1,818 (1,179 in 4 files + 489 shader + ~150 related)
**Tests Added:** 59 property tests (in 3 test files)
**Bugs Found:** 11 (BUG-085 through BUG-095)
**Bugs Fixed:** 11 (all)

---

## ARCHITECTURE OVERVIEW

### File Hierarchy

```
services/
├── particleSystem.ts (2197 lines) - LEGACY CPU system, SeededRandom, deterministic scrubbing
├── particleGPU.ts - GPU service bridge
├── gpuParticleRenderer.ts - GPU rendering service
├── meshParticleManager.ts - Mesh particle management
└── particles/
    ├── particleTypes.ts - Service-level types
    ├── particleDefaults.ts - Default configurations
    ├── particleRenderer.ts - Canvas rendering
    └── SeededRandom.ts - Deterministic RNG

engine/particles/
├── GPUParticleSystem.ts (1923 lines) - PRIMARY system, 100k+ particles
├── ParticleGPUPhysics.ts (857 lines) - WebGPU/WebGL2 physics
├── ParticleCollisionSystem.ts (388 lines) - Collision detection
├── ParticleForceCalculator.ts (299 lines) - Force field math
├── ParticleFlockingSystem.ts (251 lines) - Boids behavior
├── ParticleTrailSystem.ts (315 lines) - Trail rendering
├── ParticleConnectionSystem.ts (317 lines) - Line connections
├── ParticleSubEmitter.ts (280 lines) - Sub-emitter system
├── ParticleEmitterLogic.ts (303 lines) - Spawn position/direction
├── ParticleAudioReactive.ts (221 lines) - Audio integration
├── ParticleFrameCache.ts (247 lines) - Timeline scrubbing cache
├── ParticleTextureSystem.ts (347 lines) - Texture/sprite management
├── ParticleModulationCurves.ts (282 lines) - Animation curves
├── particleShaders.ts (587 lines) - GLSL shaders
├── webgpuParticleCompute.ts (655 lines) - WebGPU compute
├── SpatialHashGrid.ts (245 lines) - Spatial partitioning
└── types.ts (706 lines) - GPU system types

engine/layers/
└── ParticleLayer.ts (2010 lines) - Three.js layer integration

types/
└── particles.ts (485 lines) - Project-level types
```

---

## CRITICAL INVARIANTS

### 1. DETERMINISM
- Same seed + same config + same frame = IDENTICAL particle state
- Math.random() is NEVER used directly
- SeededRandom must produce reproducible sequences
- Timeline scrubbing to frame N must always produce same state

### 2. PERFORMANCE
- Must handle 100k+ particles at 60fps
- GPU physics preferred (WebGPU > WebGL2 Transform Feedback > CPU)
- Memory bounded by maxParticles config
- Particle pool prevents GC pressure

### 3. PHYSICS CORRECTNESS
- Force fields: gravity, point attractor, vortex, turbulence, drag, wind, lorenz, curl, magnetic, orbit
- Collision: boundary (none/kill/bounce/wrap/clamp/stick), particle-particle
- Flocking: separation, alignment, cohesion with perception cone

### 4. NUMERICAL STABILITY
- No NaN/Infinity in particle state
- No division by zero in physics calculations
- Bounded velocity to prevent explosion
- Safe mass handling (mass=0 → inverseMass=0, not Infinity)

### 5. BROWSER SAFETY
- maxParticles limits GPU buffer allocation
- Pool size capped to prevent memory leak
- Force field count limited (MAX_FORCE_FIELDS = 16)
- Trail buffer bounded

---

## EXPORTED FUNCTIONS & CLASSES

### services/particleSystem.ts

| Export | Type | Description | Testable |
|--------|------|-------------|----------|
| `ParticleSystem` | class | Legacy CPU particle system | ✅ Node |
| `SeededRandom` | class | Deterministic RNG (re-export) | ✅ Node |
| `createDefaultSystemConfig` | function | Default config factory | ✅ Node |
| `createDefaultEmitterConfig` | function | Default emitter factory | ✅ Node |
| `createDefaultRenderOptions` | function | Default render options | ✅ Node |
| `createDefaultGravityWellConfig` | function | Default gravity well | ✅ Node |
| `createDefaultVortexConfig` | function | Default vortex | ✅ Node |
| `createDefaultTurbulenceConfig` | function | Default turbulence | ✅ Node |
| `createDefaultSpriteConfig` | function | Default sprite | ✅ Node |
| `createDefaultSubEmitterConfig` | function | Default sub-emitter | ✅ Node |
| `createDefaultCollisionConfig` | function | Default collision | ✅ Node |
| `createDefaultConnectionConfig` | function | Default connection | ✅ Node |
| `createDefaultSplinePathEmission` | function | Default spline emission | ✅ Node |
| `resetIdCounter` | function | Reset ID counter | ✅ Node |

### engine/particles/GPUParticleSystem.ts

| Export | Type | Description | Testable |
|--------|------|-------------|----------|
| `GPUParticleSystem` | class | Primary GPU particle system | ❌ WebGL |
| `createDefaultConfig` | function | Default GPU config factory | ✅ Node |
| `createDefaultEmitter` | function | Default GPU emitter | ✅ Node |
| `createDefaultForceField` | function | Default force field | ✅ Node |

### engine/particles/ParticleEmitterLogic.ts

| Export | Type | Description | Testable |
|--------|------|-------------|----------|
| `getEmitterPosition` | function | Calculate spawn position | ✅ Node (mock THREE) |
| `getEmissionDirection` | function | Calculate emission direction | ✅ Node (mock THREE) |

### engine/particles/ParticleForceCalculator.ts

| Export | Type | Description | Testable |
|--------|------|-------------|----------|
| `calculateForceField` | function | Force calculation | ✅ Node |
| `getForceFieldTypeIndex` | function | Type to GPU index | ✅ Node |
| `getFalloffTypeIndex` | function | Falloff to GPU index | ✅ Node |

### engine/particles/SpatialHashGrid.ts

| Export | Type | Description | Testable |
|--------|------|-------------|----------|
| `SpatialHashGrid` | class | O(n) spatial queries | ✅ Node |

### engine/particles/ParticleModulationCurves.ts

| Export | Type | Description | Testable |
|--------|------|-------------|----------|
| `ParticleModulationCurves` | class | Animation curve evaluation | ✅ Node |

---

## EDGE CASES TO TEST

### SeededRandom
- [ ] Seed = 0
- [ ] Seed = MAX_SAFE_INTEGER
- [ ] Seed = negative
- [ ] range(min, max) where min > max
- [ ] range() where min === max
- [ ] Very long sequences (10M+ calls)

### Force Fields
- [ ] strength = 0 (should have no effect)
- [ ] strength = Infinity (should clamp or reject)
- [ ] strength = NaN (should reject)
- [ ] position at particle position (avoid divide by zero)
- [ ] falloffStart > falloffEnd
- [ ] Multiple overlapping force fields

### Collision
- [ ] Particle at boundary edge
- [ ] Particle moving faster than boundary (tunneling)
- [ ] Two particles at exact same position
- [ ] Zero-radius collision
- [ ] Particle-particle with mass=0

### Emitter Shapes
- [ ] Circle radius = 0
- [ ] Box size = 0
- [ ] Sphere with emitFromEdge=true, radius=0
- [ ] Line with start === end
- [ ] Cone with angle = 0
- [ ] Cone with angle = 180
- [ ] Image emission with all transparent pixels
- [ ] Spline emission with no spline provider

### Memory/Performance
- [ ] maxParticles = 0
- [ ] maxParticles = 1
- [ ] maxParticles = 10,000,000 (should fail gracefully)
- [ ] Particle pool overflow
- [ ] Trail buffer overflow

---

## PROPERTY TESTS NEEDED

### 1. Determinism Tests
```typescript
// Same seed = same simulation
fc.property(seed, config, frames => {
  const sim1 = new ParticleSystem(config, seed);
  const sim2 = new ParticleSystem(config, seed);
  for (let f = 0; f < frames; f++) {
    sim1.step(1/16);
    sim2.step(1/16);
  }
  return particlesEqual(sim1.getParticles(), sim2.getParticles());
});
```

### 2. Scrub Determinism
```typescript
// Jump to frame N always produces same state
fc.property(seed, config, targetFrame => {
  const sim = new ParticleSystem(config, seed);
  // Method 1: Step to frame
  for (let f = 0; f < targetFrame; f++) sim.step(1/16);
  const state1 = sim.getParticles();
  
  // Method 2: Reset and step again
  sim.reset();
  for (let f = 0; f < targetFrame; f++) sim.step(1/16);
  const state2 = sim.getParticles();
  
  return particlesEqual(state1, state2);
});
```

### 3. Force Field Sanity
```typescript
// Forces should not produce NaN
fc.property(forceFieldConfig, particleState => {
  const force = calculateForceField(forceFieldConfig, particleState);
  return Number.isFinite(force.x) && 
         Number.isFinite(force.y) && 
         Number.isFinite(force.z);
});
```

### 4. Spatial Hash Correctness
```typescript
// All neighbors within radius should be found
fc.property(particles, queryPoint, radius => {
  const grid = new SpatialHashGrid(cellSize);
  particles.forEach(p => grid.insert(p));
  
  const found = grid.queryRadius(queryPoint, radius);
  const expected = particles.filter(p => distance(p, queryPoint) <= radius);
  
  return found.length === expected.length;
});
```

### 5. Collision Response Conservation
```typescript
// Momentum should be conserved in particle-particle collision
fc.property(particle1, particle2 => {
  const beforeMomentum = p1.velocity * p1.mass + p2.velocity * p2.mass;
  applyCollision(particle1, particle2);
  const afterMomentum = p1.velocity * p1.mass + p2.velocity * p2.mass;
  return Math.abs(beforeMomentum - afterMomentum) < EPSILON;
});
```

---

## REAL-WORLD SCENARIOS

### 1. Data Visualization
- Thousands of particles representing data points
- Must render without frame drops
- Color/size modulation by data values
- Export positions for analysis

### 2. Audio Reactive VFX
- Particles pulse to beat
- Emission rate tied to amplitude
- Force field strength modulated by spectrum
- Must not accumulate modifiers over time

### 3. Timeline Scrubbing
- User drags timeline back and forth
- Each frame must render identically
- No state accumulation from previous frames

### 4. Spline Following
- Particles emitted along motion path
- Particles follow spline trajectory
- Export path as trajectory data

### 5. Sub-Particle Cascades
- Explosion: particle death spawns debris
- Fireworks: burst particles spawn trails
- Must not cause memory explosion

### 6. Flocking Simulation
- Birds/fish schooling behavior
- Collision avoidance
- Leader following
- Export trajectories for AI training

---

## BUGS FOUND

| ID | File | Line | Description | Status |
|----|------|------|-------------|--------|
| BUG-083 | particleSystem.ts | 670-671 | Division by zero in pingpong sprite animation when totalFrames=1 | ✅ FIXED |
| BUG-084 | ParticleForceCalculator.ts | 52 | Division by zero in falloff when falloffEnd=falloffStart | ✅ FIXED |
| BUG-085 | ParticleFrameCache.ts | - | Memory exhaustion: 200 caches × 6.4MB = 1.28GB RAM | ✅ FIXED |
| BUG-086 | particleSystem.ts | 1982-1993 | reset() didn't reset RNG, breaking scrub determinism | ✅ FIXED |
| BUG-087 | ParticleForceCalculator.ts | 87 | Division by mass=0 in point force field | ✅ FIXED |
| BUG-088 | ParticleForceCalculator.ts | 138-140 | Drag double-negative accelerates instead of decelerates | ✅ FIXED |
| BUG-089 | GPUParticleSystem.ts | 1172 | Particle size can be zero or negative | ✅ FIXED |
| BUG-090 | SpatialHashGrid.ts | 43 | cellSize=0 causes division by zero | ✅ FIXED |
| BUG-091 | SpatialHashGrid.ts | 67-74 | NaN/Infinity positions create invalid Map keys | ✅ FIXED |
| BUG-092 | ParticleCollisionSystem.ts | 124-245 | Boundary bounce overshoots to opposite side | ✅ FIXED |
| BUG-093 | shaders/particleCompute.glsl | 217 | GPU shader falloff division by zero | ✅ FIXED |
| BUG-094 | shaders/particleCompute.glsl | 350-359 | GPU shader bounce overshoots (same as BUG-092) | ✅ FIXED |
| BUG-095 | particleSystem.ts | 1902-1904 | CPU sub-emitter size=0 division by zero | ✅ FIXED |

### BUG-086: reset() didn't reset RNG, breaking scrub determinism

**Severity:** P0 CRITICAL → FIXED
**Location:** `services/particleSystem.ts` lines 1982-1993
**Found:** 2026-01-06 via property test

**Problem:**
The `reset()` method didn't reset the seeded RNG, meaning:
- Scrub to frame 100: state A
- Scrub forward to 150, then back to 100: state B ≠ A

**Evidence (from property test):**
```
Counterexample: [seed=1, targetFrame=10]
Expected: 0.4896030714957068
Actual:   0.4924940282611796
```

**Root Cause:**
`reset()` cleared particles and emitter state but NOT the RNG state.
There was a separate `resetEmitterSeeds()` method that users had to call manually.

**Impact:**
- Timeline scrubbing produces inconsistent results
- Export at frame N could produce different results each time
- Renders not reproducible

**Fix Applied:**
`reset()` now calls RNG reset internally:
```typescript
reset(): void {
  // ... clear particles, emitters, etc ...
  
  // Reset RNG for deterministic replay (BUG-086 fix)
  this.rng.reset();
  this.noise2D = createNoise2D(() => this.rng.next());
  this.noiseTime = 0;
}
```

**Test:** `particles.property.test.ts` - "INVARIANT: Scrubbing produces identical results"

### BUG-085: Memory Exhaustion Risk from Particle Frame Cache

**Severity:** P0 CRITICAL
**Location:** `engine/particles/GPUParticleSystem.ts` lines 420-424

**Problem:**
```typescript
this.frameCacheSystem = new ParticleFrameCacheSystem(
  this.config.maxParticles,  // 100,000 default
  5,                          // Cache every 5 frames
  200,                        // Max 200 caches
);
```

**Memory Calculation:**
- maxParticles = 100,000 (default)
- PARTICLE_STRIDE = 16 floats × 4 bytes = 64 bytes/particle
- Each cache = 100,000 × 64 = **6.4 MB**
- maxCacheSize = 200 caches
- **TOTAL: 200 × 6.4 MB = 1.28 GB RAM**

**Impact:**
- Browser tab crash on low-memory devices
- System slowdown from swap thrashing
- Mobile devices will OOM immediately
- Background tabs with particle layers consume GB of RAM

**Why Frame Cache Exists:**
- Particles are stateful (frame N depends on frame N-1)
- Timeline scrubbing requires re-simulation from checkpoint
- Without cache: seek to frame 1000 → simulate 1000 frames = SLOW
- With cache: seek to frame 1000 → restore nearest checkpoint → simulate remaining

**Suggested Fix:**
```typescript
// Calculate safe cache size based on available memory
const MB_PER_CACHE = (this.config.maxParticles * PARTICLE_STRIDE * 4) / (1024 * 1024);
const MAX_CACHE_MB = 256; // Max 256MB for particle cache
const safeCacheSize = Math.max(10, Math.floor(MAX_CACHE_MB / MB_PER_CACHE));

this.frameCacheSystem = new ParticleFrameCacheSystem(
  this.config.maxParticles,
  Math.max(5, Math.floor(300 / safeCacheSize)), // Adjust interval based on cache size
  safeCacheSize,
);
```

### BUG-083: Division by Zero in Sprite Pingpong Animation

**Severity:** P1 HIGH
**Location:** `services/particleSystem.ts` lines 670-671

**Code:**
```typescript
case "pingpong": {
  const framesElapsed = Math.floor((p.age * sprite.frameRate) / 60);
  const cycle = Math.floor(framesElapsed / (totalFrames - 1));     // BUG: /0 if totalFrames=1
  const frameInCycle = framesElapsed % (totalFrames - 1);          // BUG: %0 = NaN
  p.spriteIndex =
    cycle % 2 === 0 ? frameInCycle : totalFrames - 1 - frameInCycle;
  break;
}
```

**Problem:**
When `totalFrames = 1`, `totalFrames - 1 = 0`:
- Division by zero: `framesElapsed / 0 = Infinity`
- Modulo zero: `framesElapsed % 0 = NaN`

**Impact:**
- `p.spriteIndex` becomes NaN
- Sprite rendering breaks silently
- Users with single-frame sprites in pingpong mode get broken animation

**Fix:**
```typescript
case "pingpong": {
  if (totalFrames <= 1) {
    p.spriteIndex = 0; // Single frame, no animation
    break;
  }
  const framesElapsed = Math.floor((p.age * sprite.frameRate) / 60);
  const cycle = Math.floor(framesElapsed / (totalFrames - 1));
  const frameInCycle = framesElapsed % (totalFrames - 1);
  p.spriteIndex =
    cycle % 2 === 0 ? frameInCycle : totalFrames - 1 - frameInCycle;
  break;
}
```

---

## AUDIT PROGRESS

- [ ] Read services/particleSystem.ts (2197 lines)
- [ ] Read engine/particles/GPUParticleSystem.ts (1923 lines)
- [ ] Read engine/particles/types.ts (706 lines)
- [ ] Read engine/particles/ParticleGPUPhysics.ts (857 lines)
- [ ] Read engine/particles/ParticleCollisionSystem.ts (388 lines)
- [ ] Read engine/particles/ParticleForceCalculator.ts (299 lines)
- [ ] Read engine/particles/SpatialHashGrid.ts (245 lines)
- [ ] Read engine/particles/ParticleEmitterLogic.ts (303 lines)
- [ ] Read engine/particles/ParticleModulationCurves.ts (282 lines)
- [ ] Document all edge cases
- [ ] Write property tests
- [ ] Verify determinism
- [ ] Check numerical stability
- [ ] Test browser safety limits

---

*Last updated: 2026-01-06*
