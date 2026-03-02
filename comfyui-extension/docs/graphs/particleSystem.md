# particleSystem.ts Dependency Analysis

> Generated: 2026-01-10
> Verified via symbol usage

## File Stats
- **Lines:** 2,299
- **Location:** `ui/src/services/particleSystem.ts`
- **Role:** Legacy CPU particle system (for deterministic scrubbing)

---

## IMPORTS (What it depends on) - 5 dependencies

| Import | From |
|--------|------|
| `createNoise2D` | `simplex-noise` |
| `applyEasing`, `EASING_PRESETS` | `./interpolation` |
| Particle defaults | `./particles/particleDefaults` |
| Particle renderer | `./particles/particleRenderer` |
| Particle types | `./particles/particleTypes` |
| `SeededRandom` | `./particles/SeededRandom` |

---

## EXPORTS (What it provides)

| Export | Type | Purpose |
|--------|------|---------|
| `ParticleSystem` | class | Main CPU particle simulation |
| `SeededRandom` | re-export | Deterministic RNG |
| Various types | re-export | Particle types |

---

## DEPENDENTS (What imports it) - 5 files (VERIFIED)

**Blast radius: 5 files - LOW**

> Verified 2026-01-10 via: `grep -r "\bParticleSystem\b" | grep -v GPUParticleSystem`

| File | Purpose |
|------|---------|
| `engine/ParticleSimulationController.ts` | Wraps for deterministic evaluation |
| `services/index.ts` | Barrel export |
| `services/matteExporter.ts` | Uses for matte generation |
| `services/particles/particleRenderer.ts` | CPU rendering |
| `services/particleSystem.ts` | Self (definition) |

---

## Architecture Context

This is the **legacy CPU implementation** kept for:
1. **Deterministic scrubbing** - GPU can't rewind, CPU can
2. **Fallback** - When WebGL2 unavailable
3. **Export** - Frame-by-frame rendering

The **primary implementation** is `engine/particles/GPUParticleSystem.ts` (19 users).

```
Timeline scrub → ParticleSimulationController
                         ↓
          ┌──────────────┴──────────────┐
          ↓                              ↓
   ParticleSystem (CPU)         GPUParticleSystem
   - Deterministic               - 100k+ particles
   - Can rewind                  - Transform Feedback
   - Slow (~50k max)             - Can't rewind
```

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                    particleSystem.ts                         │
│                     (2,299 lines)                           │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (5 dependencies)                              │
│  ├── simplex-noise (external)                               │
│  ├── ./interpolation                                        │
│  └── ./particles/* (4 internal modules)                     │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (5 files) ← LOW BLAST RADIUS                   │
│  ├── ParticleSimulationController.ts                        │
│  ├── services/index.ts (barrel)                             │
│  ├── matteExporter.ts                                       │
│  └── particles/particleRenderer.ts                          │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: LOW**

- Only 5 files use it
- CPU implementation is secondary to GPUParticleSystem
- Well-isolated in particle subsystem

### Why This File Is Large

Full particle simulation including:
- Emitter logic (~400 lines)
- Physics simulation (~500 lines)
- Force fields (~300 lines)
- Collision detection (~300 lines)
- Color/size interpolation (~200 lines)
- Seeded random (~100 lines)
- State management (~500 lines)

### Modularization Strategy

Similar to GPUParticleSystem, extract to subsystems:
```
services/particles/
├── ParticleSystem.ts      (orchestrator ~500 lines)
├── CPUPhysics.ts          (~500 lines)
├── CPUEmitter.ts          (~400 lines)
├── CPUForceFields.ts      (~300 lines)
├── CPUCollision.ts        (~300 lines)
└── CPUInterpolation.ts    (~200 lines)
```

**Note:** This may not be worth doing if GPU system is primary.
