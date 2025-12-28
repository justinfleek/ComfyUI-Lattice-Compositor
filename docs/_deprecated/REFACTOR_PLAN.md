# Large File Refactor Plan

**Goal:** Break files >1500 lines into smaller, focused modules (<500 lines each) for LLM comprehension.

**Target:** 500 lines max per file (ideal: 300-400 lines)

---

## Files Requiring Refactor (26 files, 47k+ lines)

| File | Lines | Priority | Complexity |
|------|-------|----------|------------|
| `stores/compositorStore.ts` | 2777 | HIGH | High |
| `types/project.ts` | 2076 | HIGH | Medium |
| `components/canvas/ThreeCanvas.vue` | 2068 | HIGH | High |
| `stores/actions/keyframeActions.ts` | 2012 | HIGH | Medium |
| `services/particleSystem.ts` | 2009 | MEDIUM | High |
| `engine/layers/BaseLayer.ts` | 1956 | HIGH | High |
| `stores/actions/layerActions.ts` | 1918 | HIGH | Medium |
| `components/properties/ParticleProperties.vue` | 1916 | MEDIUM | Medium |
| `engine/layers/ParticleLayer.ts` | 1840 | MEDIUM | High |
| `components/curve-editor/CurveEditor.vue` | 1806 | MEDIUM | Medium |
| `components/panels/AudioPanel.vue` | 1783 | LOW | Medium |
| `services/index.ts` | 1763 | HIGH | Low |
| `services/ai/actionExecutor.ts` | 1751 | MEDIUM | Medium |
| `services/physics/PhysicsEngine.ts` | 1721 | MEDIUM | High |
| `engine/LatticeEngine.ts` | 1704 | HIGH | High |
| `engine/particles/GPUParticleSystem.ts` | 1701 | MEDIUM | High |
| `services/depthflow.ts` | 1650 | LOW | Medium |
| `components/layout/WorkspaceLayout.vue` | 1649 | MEDIUM | Medium |
| `services/export/wanMoveExport.ts` | 1647 | LOW | Medium |
| `services/shapeOperations.ts` | 1643 | LOW | Medium |
| `services/audioFeatures.ts` | 1614 | LOW | Medium |
| `engine/layers/SplineLayer.ts` | 1613 | MEDIUM | High |
| `composables/useKeyboardShortcuts.ts` | 1612 | MEDIUM | Low |
| `services/effects/colorRenderer.ts` | 1590 | LOW | Medium |
| `components/properties/TextProperties.vue` | 1570 | LOW | Medium |
| `components/dialogs/TemplateBuilderDialog.vue` | 1560 | LOW | Medium |

---

## Refactor Strategies

### 1. STORES - Split by Domain

#### `compositorStore.ts` (2777 lines) → 6 files

```
stores/
├── compositorStore.ts          (300) - Core state, imports actions
├── state/
│   ├── projectState.ts         (200) - Project/composition state
│   ├── selectionState.ts       (150) - Selection state
│   ├── viewportState.ts        (200) - Viewport/camera state
│   └── playbackState.ts        (150) - Timeline playback state
└── actions/
    ├── projectActions.ts       (300) - Save/load/export
    ├── selectionActions.ts     (250) - Select/deselect layers
    ├── viewportActions.ts      (200) - Pan/zoom/camera
    └── (existing action files)
```

**Pattern:** Main store file defines state shape, imports action modules that operate on it.

#### `keyframeActions.ts` (2012 lines) → 4 files

```
stores/actions/keyframes/
├── index.ts                    (100) - Re-exports
├── keyframeCRUD.ts             (400) - Add/remove/update keyframes
├── keyframeSelection.ts        (300) - Select/copy/paste keyframes
├── keyframeInterpolation.ts    (400) - Easing, bezier handles
└── keyframeBatch.ts            (300) - Batch operations, undo grouping
```

#### `layerActions.ts` (1918 lines) → 4 files

```
stores/actions/layers/
├── index.ts                    (100) - Re-exports
├── layerCRUD.ts                (400) - Add/remove/duplicate layers
├── layerHierarchy.ts           (300) - Parent/child, ordering
├── layerTransform.ts           (400) - Position/scale/rotation
└── layerProperties.ts          (300) - Type-specific properties
```

---

### 2. TYPES - Split by Category (Already Partially Done)

#### `types/project.ts` (2076 lines) → Already split, verify imports

Check if existing split files are being used:
- `types/assets.ts` - Asset types
- `types/effects.ts` - Effect types
- `types/text.ts` - Text types
- `types/camera.ts` - Camera types
- `types/transform.ts` - Transform types

**Action:** Remove duplicates from project.ts, ensure all imports updated.

---

### 3. ENGINE - Split by Responsibility

#### `LatticeEngine.ts` (1704 lines) → 4 files

```
engine/
├── LatticeEngine.ts            (400) - Main orchestrator, lifecycle
├── core/
│   ├── EngineState.ts          (200) - State management
│   ├── EngineRenderer.ts       (400) - Render loop, frame output
│   └── EngineCompositor.ts     (300) - Layer compositing
```

#### `BaseLayer.ts` (1956 lines) → 5 files

```
engine/layers/
├── BaseLayer.ts                (400) - Core class, abstract methods
├── base/
│   ├── LayerTransform.ts       (300) - Transform matrix, 3D positioning
│   ├── LayerEffects.ts         (300) - Effect chain processing
│   ├── LayerMasking.ts         (250) - Masks, track mattes
│   ├── LayerBlending.ts        (200) - Blend modes, opacity
│   └── LayerAnimation.ts       (300) - Property animation evaluation
```

#### `ParticleLayer.ts` (1840 lines) → 4 files

```
engine/layers/particle/
├── ParticleLayer.ts            (400) - Main layer class
├── ParticleEmitter.ts          (400) - Emitter logic
├── ParticleRenderer.ts         (400) - GPU rendering
└── ParticlePhysics.ts          (300) - Force/collision calculations
```

#### `SplineLayer.ts` (1613 lines) → 3 files

```
engine/layers/spline/
├── SplineLayer.ts              (400) - Main layer class
├── SplineGeometry.ts           (400) - Path/bezier calculations
└── SplineRenderer.ts           (400) - Stroke/fill rendering
```

---

### 4. SERVICES - Split by Feature

#### `services/index.ts` (1763 lines) → Barrel file only

This should ONLY be re-exports. Move actual code to dedicated files.

```
services/
├── index.ts                    (100) - ONLY re-exports
├── (move any actual code to appropriate service files)
```

#### `particleSystem.ts` (2009 lines) → 4 files

```
services/particles/
├── index.ts                    (50)  - Re-exports
├── particleEmission.ts         (400) - Spawn logic, rates
├── particleUpdate.ts           (400) - Position/velocity updates
├── particleForces.ts           (400) - Gravity, turbulence, attractors
└── particleLifecycle.ts        (300) - Birth/death, pooling
```

#### `PhysicsEngine.ts` (1721 lines) → 4 files

```
services/physics/
├── PhysicsEngine.ts            (400) - Main engine class
├── PhysicsWorld.ts             (300) - World setup, gravity
├── PhysicsBodies.ts            (400) - Body creation, properties
└── PhysicsConstraints.ts       (300) - Joints, springs
```

#### `GPUParticleSystem.ts` (1701 lines) → 4 files

```
engine/particles/
├── GPUParticleSystem.ts        (400) - Main system
├── GPUParticleShaders.ts       (400) - Shader code
├── GPUParticleBuffers.ts       (300) - Buffer management
└── GPUParticleCompute.ts       (300) - Compute shader logic
```

---

### 5. COMPONENTS - Extract Logic to Composables

#### `ThreeCanvas.vue` (2068 lines) → 4 files

```
components/canvas/
├── ThreeCanvas.vue             (400) - Template + setup orchestration
├── composables/
│   ├── useCanvasRenderer.ts    (400) - Three.js setup, render loop
│   ├── useCanvasInteraction.ts (400) - Mouse/touch handlers
│   └── useCanvasGizmos.ts      (400) - Transform gizmos, overlays
```

#### `CurveEditor.vue` (1806 lines) → 4 files

```
components/curve-editor/
├── CurveEditor.vue             (300) - Template + setup
├── composables/
│   ├── useCurveState.ts        (300) - State management
│   ├── useCurveDrawing.ts      (400) - Canvas rendering
│   └── useCurveInteraction.ts  (400) - Handle dragging, selection
```

#### `ParticleProperties.vue` (1916 lines) → 5 files

```
components/properties/particle/
├── ParticleProperties.vue      (300) - Main container
├── ParticleEmitterSection.vue  (400) - Emitter settings
├── ParticleAppearanceSection.vue (400) - Size/color/texture
├── ParticlePhysicsSection.vue  (300) - Forces, collisions
└── ParticleLifecycleSection.vue (300) - Spawn/death settings
```

#### `AudioPanel.vue` (1783 lines) → 4 files

```
components/panels/audio/
├── AudioPanel.vue              (300) - Main container
├── AudioWaveform.vue           (400) - Waveform display
├── AudioControls.vue           (300) - Playback controls
└── AudioAnalysis.vue           (400) - Frequency analysis, beats
```

#### `WorkspaceLayout.vue` (1649 lines) → 4 files

```
components/layout/
├── WorkspaceLayout.vue         (300) - Main layout shell
├── composables/
│   ├── usePanelLayout.ts       (400) - Panel positioning/resizing
│   ├── usePanelDocking.ts      (400) - Drag-to-dock logic
│   └── useWorkspacePresets.ts  (200) - Layout presets
```

#### `useKeyboardShortcuts.ts` (1612 lines) → 4 files

```
composables/shortcuts/
├── index.ts                    (100) - Main composable, combines all
├── shortcutRegistry.ts         (300) - Shortcut definitions
├── shortcutHandlers.ts         (500) - Handler implementations
└── shortcutContext.ts          (300) - Context-aware shortcuts
```

---

## Execution Order

### Phase 1: Types & Services Index (Low Risk)
1. ✅ Verify `types/` split is complete
2. Clean `services/index.ts` to be barrel-only

### Phase 2: Store Actions (Medium Risk)
3. Split `keyframeActions.ts`
4. Split `layerActions.ts`
5. Split `compositorStore.ts` state

### Phase 3: Engine Core (Medium Risk)
6. Split `BaseLayer.ts`
7. Split `LatticeEngine.ts`
8. Split particle/spline layers

### Phase 4: Components (Higher Risk)
9. Extract composables from `ThreeCanvas.vue`
10. Extract composables from `CurveEditor.vue`
11. Split large property panels
12. Split `WorkspaceLayout.vue`

---

## Rules for Each Refactor

1. **One file at a time** - Complete one refactor before starting next
2. **Run build after each** - `npm run build` must pass
3. **Update imports immediately** - Fix all import paths in same commit
4. **Preserve exports** - Original file re-exports everything for backwards compatibility
5. **Add barrel files** - Each new directory gets an `index.ts`
6. **Keep related code together** - Don't split logical units

---

## File Size Targets

| Category | Max Lines | Ideal Lines |
|----------|-----------|-------------|
| Types | 400 | 200-300 |
| Store State | 300 | 150-200 |
| Store Actions | 500 | 300-400 |
| Services | 500 | 300-400 |
| Engine Classes | 500 | 300-400 |
| Vue Components | 400 | 200-300 |
| Composables | 400 | 200-300 |

---

## Success Criteria

- [ ] No file exceeds 500 lines
- [ ] Build passes with 0 errors
- [ ] All imports resolve correctly
- [ ] Functionality unchanged
- [ ] Each file has single responsibility
- [ ] File names clearly indicate purpose
