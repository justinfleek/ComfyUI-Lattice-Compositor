# ParticleProperties.vue Dependency Analysis

> Generated: 2026-01-10
> Verified via symbol usage

## File Stats
- **Lines:** 2,683
- **Location:** `ui/src/components/properties/ParticleProperties.vue`
- **Role:** UI panel for editing particle layer properties

---

## IMPORTS (What it depends on) - ~15 dependencies

### Vue
| Import | From |
|--------|------|
| `computed`, `onMounted`, `ref`, `watch` | `vue` |

### Services
| Import | From |
|--------|------|
| `ParticleGPUCompute` | `@/services/particleGPU` |

### Stores
| Import | From |
|--------|------|
| `useCompositorStore` | `@/stores/compositorStore` |
| `usePresetStore` | `@/stores/presetStore` |

### Types
| Import | From |
|--------|------|
| `ParticlePreset` | `@/types/presets` |
| Various particle types | `@/types/project` |

### Sub-components (8+)
| Import | From |
|--------|------|
| `ParticleLODSection` | `./particle/ParticleLODSection.vue` |
| `ParticleDOFSection` | `./particle/ParticleDOFSection.vue` |
| `ParticleCollisionPlanesSection` | `./particle/ParticleCollisionPlanesSection.vue` |
| `ParticleGroupsSection` | `./particle/ParticleGroupsSection.vue` |
| + more particle section components | `./particle/*.vue` |

---

## DEPENDENTS (What imports it) - 2 files (VERIFIED)

**Blast radius: 2 files - VERY LOW**

> Verified 2026-01-10 via: `grep -r "ParticleProperties" | grep -v __tests__`

| File | Purpose |
|------|---------|
| `components/panels/PropertiesPanel.vue` | Parent panel that conditionally renders this |
| `components/properties/particle/index.ts` | Barrel export |

---

## Component Structure

This is a **monolithic property editor** with many sections:

```vue
<template>
  <!-- Emitter Settings -->
  <section>Shape, Rate, Lifetime, Size, Color...</section>

  <!-- Physics Settings -->
  <section>Gravity, Forces, Turbulence, Collision...</section>

  <!-- Rendering Settings -->
  <section>Blend Mode, Sprites, Trails...</section>

  <!-- Audio Reactive -->
  <section>Audio bindings, Beat detection...</section>

  <!-- Sub-emitters -->
  <section>Birth, Death, Collision triggers...</section>

  <!-- Presets -->
  <section>Save/Load particle presets...</section>
</template>
```

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                  ParticleProperties.vue                      │
│                     (2,683 lines)                           │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (~15 dependencies)                            │
│  ├── vue (reactivity)                                       │
│  ├── 1 service (particleGPU)                                │
│  ├── 2 stores                                               │
│  ├── 2+ type modules                                        │
│  └── 8+ sub-components (particle sections)                  │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (2 files) ← VERY LOW BLAST RADIUS              │
│  ├── PropertiesPanel.vue (parent)                           │
│  └── particle/index.ts (barrel)                             │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: VERY LOW**

This component is only used in one place (PropertiesPanel) and is already partially modularized with sub-components in `particle/`.

### Why This File Is Large

The particle system has **many configurable parameters**:
- Emitter shape, rate, burst
- Particle lifetime, size, color (with variance)
- Physics: gravity, forces, turbulence, collision
- Rendering: sprites, trails, connections
- Audio reactivity
- Sub-emitters
- Presets

### Already Partially Modularized

Sub-components already extracted to `components/properties/particle/`:
- `ParticleLODSection.vue`
- `ParticleDOFSection.vue`
- `ParticleCollisionPlanesSection.vue`
- `ParticleGroupsSection.vue`
- `ParticleAudioBindingsSection.vue`
- `ParticleCollisionSection.vue`
- `ParticleFlockingSection.vue`
- `ParticleForceFieldsSection.vue`
- `ParticleModulationsSection.vue`
- `ParticleRenderSection.vue`
- `ParticleSPHSection.vue`
- `ParticleSpringSection.vue`
- `ParticleSubEmittersSection.vue`
- `ParticleTurbulenceSection.vue`

### Further Modularization

Extract remaining inline sections to sub-components:
- `ParticleEmitterSection.vue` (~300 lines)
- `ParticlePhysicsSection.vue` (~300 lines)
- `ParticlePresetsSection.vue` (~200 lines)

**Estimated effort:** Low
**Estimated risk:** Very Low (only 2 consumers)
