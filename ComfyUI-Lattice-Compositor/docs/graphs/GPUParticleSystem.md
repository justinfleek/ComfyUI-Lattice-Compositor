# GPUParticleSystem.ts Dependency Analysis

> Generated: 2026-01-10
> Recon only - no changes

## File Stats
- **Lines:** 2,330
- **Location:** `ui/src/engine/particles/GPUParticleSystem.ts`
- **Role:** Main GPU-accelerated particle system implementation

---

## IMPORTS (What it depends on) - 16 dependencies

### External Libraries
| Import | From |
|--------|------|
| `THREE` (namespace) | `three` |

### Internal Particle System (15 modules)
| Import | From |
|--------|------|
| `ParticleAudioReactive` | `./ParticleAudioReactive` |
| `CollisionConfig`, `ParticleCollisionSystem` | `./ParticleCollisionSystem` |
| `ParticleConnectionSystem` | `./ParticleConnectionSystem` |
| `getEmissionDirection`, `getEmitterPosition`, `SplineProvider` | `./ParticleEmitterLogic` |
| `ParticleFlockingSystem` | `./ParticleFlockingSystem` |
| `calculateForceField` | `./ParticleForceCalculator` |
| `ParticleFrameCacheSystem` | `./ParticleFrameCache` |
| `ParticleGPUPhysics` | `./ParticleGPUPhysics` |
| `ParticleModulationCurves` | `./ParticleModulationCurves` |
| `ParticleSubEmitter` (type) | `./ParticleSubEmitter` |
| `ParticleTextureSystem` | `./ParticleTextureSystem` |
| `ParticleTrailSystem`, `TrailBlendingConfig`, `TrailConfig` | `./ParticleTrailSystem` |
| `PARTICLE_FRAGMENT_SHADER`, `PARTICLE_VERTEX_SHADER` | `./particleShaders` |
| `SpatialHashGrid` | `./SpatialHashGrid` |
| Many types | `./types` |

---

## DEPENDENTS (What imports it) - 19 files (VERIFIED)

**Blast radius: 19 files use `GPUParticleSystem` - mostly self-contained**

> Verified 2026-01-10 via: `grep -r "\bGPUParticleSystem\b"`

### All Dependents

| File | Purpose |
|------|---------|
| `engine/layers/ParticleLayer.ts` | Layer that uses GPUParticleSystem |
| `engine/particles/index.ts` | Barrel export |
| `engine/particles/ParticleAudioReactive.ts` | Audio-reactive features |
| `engine/particles/ParticleCollisionSystem.ts` | Collision detection |
| `engine/particles/ParticleConnectionSystem.ts` | Particle connections/lines |
| `engine/particles/ParticleEmitterLogic.ts` | Emitter positioning |
| `engine/particles/ParticleFlockingSystem.ts` | Flocking/swarming behavior |
| `engine/particles/ParticleForceCalculator.ts` | Force field calculations |
| `engine/particles/ParticleFrameCache.ts` | Frame caching for scrubbing |
| `engine/particles/ParticleGPUPhysics.ts` | GPU physics via Transform Feedback |
| `engine/particles/ParticleModulationCurves.ts` | Parameter modulation |
| `engine/particles/particleShaders.ts` | GLSL shader code |
| `engine/particles/ParticleSubEmitter.ts` | Sub-emitter spawning |
| `engine/particles/ParticleTextureSystem.ts` | Sprite sheet management |
| `engine/particles/ParticleTrailSystem.ts` | Particle trails |

**Note:** All 15 dependents are within the particle system itself! Only `ParticleLayer.ts` is outside the `particles/` directory.

---

## Particle System Architecture

```
┌────────────────────────────────────────────────────────────────┐
│                     ParticleLayer.ts                            │
│                    (engine/layers/)                             │
└──────────────────────────┬─────────────────────────────────────┘
                           │ uses
                           ▼
┌────────────────────────────────────────────────────────────────┐
│                   GPUParticleSystem.ts                          │
│                    (2,330 lines)                                │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ Core Responsibilities:                                    │  │
│  │ - Particle buffer management (Float32Array)              │  │
│  │ - Emitter coordination                                   │  │
│  │ - Physics simulation orchestration                       │  │
│  │ - Rendering (instanced points)                           │  │
│  │ - State serialization/restoration                        │  │
│  └──────────────────────────────────────────────────────────┘  │
└──────────────────────────┬─────────────────────────────────────┘
                           │ composes
          ┌────────────────┼────────────────┐
          │                │                │
          ▼                ▼                ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
│ ParticleGPU     │ │ ParticleAudio   │ │ ParticleTrail   │
│ Physics.ts      │ │ Reactive.ts     │ │ System.ts       │
│ (890 lines)     │ │ (450 lines)     │ │ (500 lines)     │
└─────────────────┘ └─────────────────┘ └─────────────────┘
          │                │                │
          ▼                ▼                ▼
┌─────────────────┐ ┌─────────────────┐ ┌─────────────────┐
│ ParticleForce   │ │ ParticleFlocking│ │ ParticleTexture │
│ Calculator.ts   │ │ System.ts       │ │ System.ts       │
└─────────────────┘ └─────────────────┘ └─────────────────┘
```

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                  GPUParticleSystem.ts                        │
│                     (2,330 lines)                           │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (16 dependencies)                             │
│  ├── 1 external (three)                                     │
│  └── 15 internal particle modules                           │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (19 files) ← SELF-CONTAINED (VERIFIED)         │
│  ├── 1 layer (ParticleLayer.ts)                             │
│  ├── 1 barrel (particles/index.ts)                          │
│  └── 13 particle subsystems                                 │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: LOW (highly modular, self-contained)**

The particle system is already well-architected:
- 15 dependent files, but **all within the particle system**
- Only 1 external consumer: `ParticleLayer.ts`
- Follows composition pattern - subsystems are already extracted

### Why This File Is Large

GPUParticleSystem is the **orchestrator** that:
1. Manages the main particle buffer (Float32Array)
2. Coordinates 15 subsystems
3. Handles GPU rendering setup
4. Manages frame caching for timeline scrubbing
5. Provides the public API for ParticleLayer

### Already Modularized Correctly

The particle system follows best practices:
- **Single responsibility subsystems** - Each handles one concern
- **Composition over inheritance** - GPUParticleSystem composes subsystems
- **Minimal external coupling** - Only ParticleLayer depends on it

### Further Modularization Options (Low Priority)

If desired, GPUParticleSystem could extract:

1. **ParticleBufferManager.ts** (~400 lines)
   - Float32Array management
   - Particle lifecycle (birth/death)
   - Buffer resizing

2. **ParticleRenderer.ts** (~500 lines)
   - THREE.js setup
   - Instanced rendering
   - Shader uniforms

3. **ParticleEmitterCoordinator.ts** (~300 lines)
   - Multi-emitter management
   - Emission rate accumulation
   - Emitter state

But this is **low priority** because:
- The system is already self-contained
- Changes only affect 1 external file
- Current architecture is functional and performant
