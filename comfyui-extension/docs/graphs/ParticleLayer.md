# ParticleLayer.ts Dependency Analysis

> Generated: 2026-01-10
> Verified via symbol usage

## File Stats
- **Lines:** 2,201
- **Location:** `ui/src/engine/layers/ParticleLayer.ts`
- **Role:** Layer type that renders particle systems

---

## IMPORTS (What it depends on) - 6 dependencies

| Import | From |
|--------|------|
| `THREE` (namespace) | `three` |
| Layer/particle types | `@/types/project` |
| `GPUParticleSystem` + types | `../particles/GPUParticleSystem` |
| Particle types | `../particles/types` |
| `BaseLayer` | `./BaseLayer` |
| `PropertyEvaluator` | `@/services/animation/PropertyEvaluator` |

---

## EXPORTS (What it provides)

| Export | Type | Purpose |
|--------|------|---------|
| `ParticleLayer` | class | Layer implementation for particles |

---

## DEPENDENTS (What imports it) - 5 files (VERIFIED)

**Blast radius: 5 files - LOW**

> Verified 2026-01-10 via: `grep -r "\bParticleLayer\b" | grep -v __tests__`

| File | Purpose |
|------|---------|
| `components/panels/PreviewPanel.vue` | Type check for particles |
| `engine/core/LayerManager.ts` | Creates ParticleLayer instances |
| `engine/index.ts` | Barrel export |
| `engine/layers/ParticleLayer.ts` | Self (definition) |
| `engine/layers/PathLayer.ts` | Spline emission reference |

---

## Class Hierarchy

```
BaseLayer (2,120 lines)
    ↑ extends
ParticleLayer (2,201 lines)
    │
    ├── GPUParticleSystem (composition)
    ├── Audio reactive bindings
    ├── Spline path emission
    └── Frame caching for scrubbing
```

---

## Why This File Is Large

ParticleLayer bridges the layer system with the particle system:

1. **GPUParticleSystem management** (~400 lines)
   - Create, configure, dispose
   - Multi-emitter coordination

2. **Audio reactive** (~300 lines)
   - Bind audio features to particle params
   - Beat-triggered bursts

3. **Spline emission** (~200 lines)
   - Emit along path layers
   - Velocity from path tangent

4. **Frame evaluation** (~400 lines)
   - Deterministic scrubbing
   - State restoration

5. **Property animation** (~300 lines)
   - Animate emitter params
   - Keyframe evaluation

6. **Rendering coordination** (~300 lines)
   - Canvas output for compositing
   - Blend mode integration

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                     ParticleLayer.ts                         │
│                      (2,201 lines)                          │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (6 dependencies)                              │
│  ├── three                                                  │
│  ├── @/types/project                                        │
│  ├── ../particles/GPUParticleSystem                         │
│  ├── ../particles/types                                     │
│  ├── ./BaseLayer (extends)                                  │
│  └── @/services/animation/PropertyEvaluator                 │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (5 files) ← LOW BLAST RADIUS                   │
│  ├── PreviewPanel.vue (type check)                          │
│  ├── LayerManager.ts (factory)                              │
│  ├── engine/index.ts (barrel)                               │
│  └── PathLayer.ts (spline emission)                         │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: LOW**

- Only 5 files use it directly
- Changes contained to particle subsystem
- Well-structured with clear responsibilities

### Modularization Strategy

Extract functionality to mixins/helpers:

```
engine/layers/particle/
├── ParticleLayer.ts           (main class ~500 lines)
├── ParticleAudioBinding.ts    (~300 lines)
├── ParticleSplineEmission.ts  (~200 lines)
├── ParticleFrameCache.ts      (~400 lines)
└── ParticlePropertyAnim.ts    (~300 lines)
```

Or use composition:
```typescript
class ParticleLayer extends BaseLayer {
  private audioBinding = new ParticleAudioBinding(this);
  private splineEmitter = new ParticleSplineEmission(this);
  private frameCache = new ParticleFrameCache(this);
}
```
