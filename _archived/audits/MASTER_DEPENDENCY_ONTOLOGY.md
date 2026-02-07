# Master Dependency & Ontology Graph

> **Purpose:** Single source of truth for system architecture, dependencies, and domain ontology
> **Generated:** 2026-01-22
> **Status:** ⚠️ **INCOMPLETE** - High-level overview only. Comprehensive audit needed.
> **Coverage:** ~30% complete. Missing: detailed service catalog, component inventory, type system completeness, engine modules, Python backend.

**⚠️ CRITICAL:** This document is a HIGH-LEVEL OVERVIEW, not a complete ontology. A comprehensive audit of the entire 800k+ LOC codebase is required.

---

## Table of Contents

1. [System Architecture Overview](#1-system-architecture-overview)
2. [Domain Ontology](#2-domain-ontology)
3. [Dependency Graphs](#3-dependency-graphs)
4. [Store Dependency Graph](#4-store-dependency-graph)
5. [Service Dependency Graph](#5-service-dependency-graph)
6. [Schema Dependency Graph](#6-schema-dependency-graph)
7. [Cross-Domain Actions](#7-cross-domain-actions)
8. [Consumer Mapping](#8-consumer-mapping)

---

## 1. System Architecture Overview

### Layer Hierarchy

```
┌─────────────────────────────────────────────────────────────┐
│ PRESENTATION LAYER (Vue 3.5 + TypeScript)                    │
│ - 157 Vue Components                                         │
│ - User interactions, UI state                                 │
└─────────────────────────────────────────────────────────────┘
                          ↓ (calls)
┌─────────────────────────────────────────────────────────────┐
│ STATE LAYER (Pinia 2.2 → Haskell State Modules)             │
│ - 13 Domain Stores                                           │
│ - Project state, CRUD operations                             │
└─────────────────────────────────────────────────────────────┘
                          ↓ (calls)
┌─────────────────────────────────────────────────────────────┐
│ ENGINE LAYER (Three.js r170 → PureScript/Haskell)            │
│ - LatticeEngine, MotionEngine, LayerManager                   │
│ - Rendering, frame evaluation                                 │
└─────────────────────────────────────────────────────────────┘
                          ↓ (calls)
┌─────────────────────────────────────────────────────────────┐
│ SERVICE LAYER (181 Services → Haskell)                       │
│ - Animation, Audio, Particles, Camera, Effects, Export      │
│ - Business logic, transformations                            │
└─────────────────────────────────────────────────────────────┘
                          ↓ (calls)
┌─────────────────────────────────────────────────────────────┐
│ BACKEND (Python + ComfyUI)                                   │
│ - compositor_node.py, lattice_api_proxy.py                   │
│ - AI model integration                                       │
└─────────────────────────────────────────────────────────────┘
```

### Data Flow

**Project Load:**
```
User → projectActions.importProject() → projectMigration.migrateProject() 
→ security.validateProjectStructure() → compositorStore.project 
→ LatticeEngine.render()
```

**Frame Evaluation:**
```
playbackStore.currentFrame → MotionEngine.evaluate(frame) 
→ For each layer: evaluatePropertyAtFrame() → interpolateKeyframes() 
→ applyEffects() → renderToScene()
```

**Export:**
```
User → Export service → MotionEngine.evaluate(frame) for each frame 
→ renderToOffscreenCanvas() → encodeToFormat() → saveFile()
```

---

## 2. Domain Ontology

### Core Domains

| Domain | Description | Current Store | Target Haskell Module | Status |
|--------|-------------|---------------|----------------------|--------|
| **Project** | Project file, metadata, compositions | `compositorStore` | `Lattice.State.Project` | ⏳ 0% |
| **Composition** | Multi-comp navigation, active comp | `compositorStore` | `Lattice.State.Composition` | ⏳ 0% |
| **Layer** | Layer CRUD, hierarchy, text animators | `compositorStore` | `Lattice.State.Layer.*` | 🔄 12 modules exist |
| **Keyframe** | Keyframe CRUD, interpolation | `keyframeStore` | `Lattice.State.Keyframe.*` | ✅ 98% |
| **Animation** | Playback, frame, time, work area | `animationStore` | `Lattice.State.Animation.*` | ✅ 95% |
| **Expression** | Expressions, drivers, property links | `expressionStore` | `Lattice.State.Expression.*` | ✅ 100% |
| **Audio** | Audio buffer, analysis, reactive mappings | `audioStore` | `Lattice.State.Audio.*` | ⏳ 0% |
| **Effect** | Effects, styles, parameters | `compositorStore` | `Lattice.State.Effect.*` | ⏳ 0% |
| **Camera** | 3D cameras, viewports, trajectories | `compositorStore` | `Lattice.State.Camera.*` | ⏳ 0% |
| **Physics** | Physics simulation, forces | `compositorStore` | `Lattice.State.Physics.*` | ⏳ 0% |
| **Asset** | Assets, imports, file references | `assetStore` | `Lattice.State.Asset.*` | ⏳ 0% |
| **Selection** | Selection state (UI) | `selectionStore` | `Lattice.State.Selection.*` | ⏳ 0% |
| **History** | Undo/redo snapshots | `historyStore` | `Lattice.State.History.*` | ⏳ 0% |
| **UI** | Tools, panels, preferences, segmentation | `toolStore`, `uiStore` | `Lattice.State.UI.*` | ⏳ 0% |

### Entity Relationships

```
Project
  ├── compositions: Composition[]
  │     ├── layers: Layer[]
  │     │     ├── keyframes: Keyframe[]
  │     │     ├── expressions: Expression[]
  │     │     ├── effects: Effect[]
  │     │     └── data: LayerData (union of 26 types)
  │     ├── cameras: Camera3D[]
  │     ├── audio: AudioLayerData
  │     └── assets: AssetReference[]
  └── metadata: ProjectMeta
```

### Layer Types (26 Total)

1. `image` - ImageLayerData
2. `video` - VideoData
3. `text` - TextData
4. `spline` - SplineData
5. `path` - PathLayerData
6. `shape` - ShapeLayerData (22 ShapeContent types)
7. `particles` - ParticleSystemLayerConfig
8. `particle` - LegacyParticleLayerData
9. `camera` - CameraLayerData
10. `light` - LightLayerData
11. `audio` - AudioLayerData
12. `depth` - DepthLayerData
13. `normal` - NormalLayerData
14. `matte` - MatteLayerData
15. `proceduralMatte` - ProceduralMatteParams
16. `depthflow` - DepthflowLayerData
17. `model` - ModelLayerData
18. `pointCloud` - PointCloudLayerData
19. `pose` - PoseLayerData
20. `generated` - GeneratedLayerData
21. `solid` - SolidLayerData
22. `group` - GroupLayerData
23. `effect` - EffectLayerData
24. `nestedComp` - NestedCompData
25. `control` - ControlLayerData
26. `null` - NullLayerData (deprecated)

---

## 3. Dependency Graphs

### Import Dependency Rules

**Rule 1: Stores Can Read Freely**
- Any store can call getters on other stores
- ✅ `keyframeStore` reads from `layerStore`
- ✅ `audioStore` reads from `keyframeStore`

**Rule 2: Stores Write to Own Domain**
- A store should only mutate its own state
- ✅ `keyframeStore` mutates keyframes
- ❌ `keyframeStore` mutates layers (use `layerStore` API)

**Rule 3: Cross-Domain Writes Use Public API**
- When a store needs to trigger changes in another domain, call that store's action
- ✅ `audioStore` calls `keyframeStore.addKeyframe()`
- ❌ `audioStore` directly mutates keyframe state

**Rule 4: History is Explicit**
- The store that initiates the user action pushes to history
- ✅ `layerStore.deleteLayer()` → `historyStore.pushState()`

**Rule 5: No Circular Action Chains**
- ❌ `layerStore` → `selectionStore` → `layerStore`
- ✅ Unidirectional: `layerStore` → clears own state → done

---

## 4. Store Dependency Graph

### Target Architecture (Post-Migration)

```
                    historyStore
                         ↑
                         │ (pushState)
    ┌────────────────────┼────────────────────┐
    │                    │                    │
layerStore ←──── keyframeStore ←──── audioStore
    ↑                    ↑                    ↑
    │                    │                    │
    └────────────────────┼────────────────────┘
                         │
                  expressionStore
                         │
                         ↓
              animationStore (currentFrame)
                         │
                         ↓
                selectionStore (read-only from others)
                         │
                         ↓
                    uiStore (clipboard, tools)
                         │
                         ↓
                  projectStore (project root)
```

**Direction:** Arrows show "can call into"
- All stores can read from any other store
- Writes flow upward toward historyStore
- No cycles

### Current State (Pre-Migration)

```
                    compositorStore (GOD OBJECT)
                         ↑
                         │ (all routes through here)
    ┌────────────────────┼────────────────────┐
    │                    │                    │
keyframeStore    layerStore    audioStore
    │                    │                    │
    └────────────────────┴────────────────────┘
                         │
                    (all imports)
```

**Problem:** 101 files depend on `compositorStore`, creating circular dependencies and tight coupling.

---

## 5. Service Dependency Graph

### Service Categories

**Animation Services:**
- `interpolation.ts` → Uses: keyframeStore, animationStore
- `easing.ts` → Pure function (no dependencies)
- `expressions.ts` → Uses: keyframeStore, expressionStore
- `propertyDriver.ts` → Uses: audioStore, expressionStore

**Audio Services:**
- `audioFeatures.ts` → Uses: audioStore
- `audioReactiveMapping.ts` → Uses: audioStore, keyframeStore
- `audioPathAnimator.ts` → Uses: audioStore, layerStore

**Export Services:**
- `wanMoveExport.ts` → Uses: layerStore, keyframeStore
- `atiExport.ts` → Uses: layerStore, keyframeStore
- `cameraExportFormats.ts` → Uses: cameraStore, keyframeStore
- `exportPipeline.ts` → Uses: all export services

**Effect Services:**
- `effectProcessor.ts` → Uses: layerStore, effectStore
- `blurRenderer.ts` → Uses: layerStore
- `colorRenderer.ts` → Uses: layerStore

**AI Services:**
- `actionExecutor.ts` → Uses: all stores (orchestration)
- `systemPrompt.ts` → Uses: projectStore
- `cameraTrackingAI.ts` → Uses: cameraStore

### Service Dependency Pattern

```
Pure Functions (no dependencies)
  ↓
Domain Services (depend on one store)
  ↓
Cross-Domain Services (depend on multiple stores)
  ↓
Orchestration Services (depend on all stores)
```

---

## 6. Schema Dependency Graph

### Schema Migration Order

**Phase 1.1: Foundation (No Dependencies)**
1. ✅ `shared-validation.ts` → Dhall + Haskell
2. ✅ `layers/primitives-schema.ts` → Dhall + Haskell

**Phase 1.2: Layer Schemas (Depends on Primitives)**
3. `layers/animation-schema.ts` → Depends on primitives
4. `layers/transform-schema.ts` → Depends on primitives, animation
5. `layers/shapes-schema.ts` → Depends on primitives, transform
6. `layers/layer-data-schema.ts` → Depends on all layer schemas
7. `layers/layer-schema.ts` → Depends on all layer schemas

**Phase 1.3: Project Schema (Depends on Layers)**
8. `project-schema.ts` → Depends on layers, shared validation

**Phase 1.4: Export Schemas (Depends on Primitives)**
9. Simple exports (camera, depth, normal)
10. Complex exports (wanmove, ati, controlnet)

**Phase 1.5: Other Schemas**
11. Settings schemas
12. Masks, effects, assets schemas
13. Physics, presets, templateBuilder schemas

### Schema Dependency Tree

```
shared-validation.ts (foundation)
  ↑
primitives-schema.ts
  ↑
animation-schema.ts
  ↑
transform-schema.ts
  ↑
shapes-schema.ts
  ↑
layer-data-schema.ts
  ↑
layer-schema.ts
  ↑
project-schema.ts
  ↑
export-schemas/*.ts
```

---

## 7. Cross-Domain Actions

### Critical Cross-Domain Actions (19 Total)

**Audio → Keyframe:**
1. `convertAudioToKeyframes` - Owner: audioStore, Needs: layerStore (read), keyframeStore (write), historyStore (write)
2. `createAudioPropertyDriver` - Owner: audioStore, Needs: expressionStore (write)
3. `getAudioReactiveValuesForLayer` - Owner: audioStore, Pure read

**Expression → Keyframe:**
4. `convertExpressionToKeyframes` - Owner: expressionStore, Needs: keyframeStore (write), animationStore (read), historyStore (write)

**Layer → Selection:**
5. `nestSelectedLayers` - Owner: layerStore, Needs: selectionStore (read), historyStore (write)
6. `reverseSelectedLayers` - Owner: layerStore, Needs: selectionStore (read), historyStore (write)
7. `duplicateSelectedLayers` - Owner: layerStore, Needs: selectionStore (read/write), historyStore (write)
8. `deleteSelectedLayers` - Owner: layerStore, Needs: selectionStore (read/write), historyStore (write)
9. `copySelectedLayers` / `cutSelectedLayers` / `pasteLayers` - Owner: layerStore, Needs: uiStore (clipboard)

**Layer → Animation:**
10. `splitLayerAtPlayhead` - Owner: layerStore, Needs: animationStore (read), historyStore (write)
11. `freezeFrameAtPlayhead` - Owner: layerStore, Needs: animationStore (read), historyStore (write)
12. `timeStretchLayer` - Owner: layerStore, Needs: animationStore (read), historyStore (write)

**Keyframe → Selection:**
13. `copyKeyframes` / `pasteKeyframes` - Owner: keyframeStore, Needs: uiStore (clipboard)
14. `timeReverseKeyframes` - Owner: keyframeStore, Needs: selectionStore (read), historyStore (write)

**Animation → Keyframe:**
15. `jumpToNextKeyframe` / `jumpToPrevKeyframe` - Owner: animationStore, Needs: keyframeStore (read)

**Property Evaluation (Complex):**
16. `evaluatePropertyAtFrame` - Owner: **Dedicated Service** (`propertyEvaluator.ts`), Needs: layerStore, keyframeStore, expressionStore, audioStore

**Orchestration (Component-Level):**
17-19. Various component-level orchestrations (better handled in components than stores)

### Cross-Domain Coordination Patterns

**Pattern A: Action Needs Data From Other Store (READ)**
```haskell
-- Owner store reads from other store
convertAudioToKeyframes :: LayerId -> PropertyPath -> AudioToKeyframeOptions -> StateM ()
convertAudioToKeyframes layerId propPath opts = do
  analysis <- gets audioAnalysis  -- Read from self
  layer <- lift $ getLayerById layerId  -- Read from layerStore
  -- ... create keyframes via keyframeStore API
```

**Pattern B: Action Mutates Other Store (WRITE)**
```haskell
-- Owner store calls other store's action
convertAudioToKeyframes :: LayerId -> PropertyPath -> AudioToKeyframeOptions -> StateM ()
convertAudioToKeyframes layerId propPath opts = do
  peaks <- gets peakData
  -- Write to keyframeStore via its public API
  lift $ forM_ peaks $ \peak ->
    addKeyframe layerId propPath peak.amplitude peak.frame
  -- Explicit history push
  lift $ pushHistoryState "Convert audio to keyframes"
```

**Pattern C: Atomic Multi-Store Update**
```haskell
-- Dedicated service orchestrates multiple stores
evaluatePropertyAtFrame :: LayerId -> PropertyPath -> Frame -> StateM Value
evaluatePropertyAtFrame layerId propPath frame = do
  -- Check expression first
  expr <- lift $ getPropertyExpression layerId propPath
  case expr of
    Just e -> evaluateExpression e frame
    Nothing -> do
      -- Check audio mapping
      audioVal <- lift $ getAudioMappedValue layerId propPath frame
      case audioVal of
        Just v -> return v
        Nothing -> lift $ interpolateKeyframeValue layerId propPath frame
```

---

## 8. Consumer Mapping

### Store Method Usage Statistics

**Total Consumer Files:** 99 files calling `compositorStore` methods

**By Domain:**

| Domain | Methods | Usage Count | Consumer Files |
|--------|---------|-------------|----------------|
| **Layer** | 45 | ~2,500 | 77 components, 9 services |
| **Keyframe** | 35 | ~1,200 | 77 components, 9 services |
| **Animation** | 12 | ~400 | 77 components, 8 composables |
| **Audio** | 8 | ~150 | 9 services, 3 components |
| **Camera** | 15 | ~200 | 12 components, 2 services |
| **Project** | 10 | ~300 | 15 components, 5 services |
| **Effect** | 20 | ~180 | 8 components, 4 services |

**Migration Priority:**
1. **P0:** Layer (979 uses of `createLayer` alone)
2. **P0:** Keyframe (393 uses of `addKeyframe`)
3. **P1:** Animation (frequently used with keyframes)
4. **P1:** Expression (needed for property evaluation)
5. **P2:** Audio, Camera, Project, Effect

### Consumer File Breakdown

**Components:** 77 files (696 matches)
- TimelinePanel.vue, ThreeCanvas.vue, PropertiesPanel.vue, etc.

**Services:** 9 files (130 matches)
- interpolation.ts, audioFeatures.ts, exportPipeline.ts, etc.

**Composables:** 8 files (152 matches)
- useShapeDrawing.ts, useSplineInteraction.ts, etc.

**Tests:** 12 files (2,649 matches)
- keyframeActions.test.ts, projectActions.test.ts, etc.

---

## ⚠️ Missing from This Document

### Services (Incomplete)
- **Found:** 20 service subdirectories + 100+ individual service files
- **Documented:** Only high-level categories
- **Missing:** Complete catalog of all 181 services with dependencies

### Components (Incomplete)
- **Found:** 157 Vue components mentioned in docs
- **Documented:** Only layer hierarchy
- **Missing:** Complete component inventory, props, events, dependencies

### Types (Incomplete)
- **Found:** 50+ type definitions in `ui/src/types/`
- **Documented:** Only 26 layer types
- **Missing:** Complete type catalog, all interfaces, all enums, all unions

### Engine Modules (Missing)
- **Found:** Engine layer mentioned but not cataloged
- **Missing:** All engine modules, renderers, managers, utilities

### Python Backend (Missing)
- **Found:** Python nodes, scripts, backend services
- **Missing:** Complete Python module catalog, dependencies, FFI boundaries

### Test Files (Missing)
- **Found:** 146 test files
- **Missing:** Test coverage map, test dependencies

### Build/Infrastructure (Missing)
- **Found:** Nix, Dhall, build scripts
- **Missing:** Build dependency graph, infrastructure modules

---

## Comprehensive Audit Needed

To create a complete ontology, we need to:

1. **Catalog ALL Services** (181 files)
   - Read each service file
   - Document dependencies
   - Map to domains

2. **Catalog ALL Components** (157 Vue files)
   - Read each component
   - Document props, events, dependencies
   - Map to stores/services

3. **Catalog ALL Types** (50+ type files)
   - Read each type file
   - Document all interfaces, enums, unions
   - Map relationships

4. **Catalog Engine Modules**
   - Read all engine files
   - Document rendering pipeline
   - Map dependencies

5. **Catalog Python Backend**
   - Read all Python files
   - Document FFI boundaries
   - Map dependencies

6. **Create Dependency Graph**
   - Map all imports/exports
   - Create visual graph
   - Identify cycles

**Estimated Effort:** 40-60 hours for complete audit

---

## Related Documents

| Document | Purpose |
|----------|---------|
| [ARCHITECTURE.md](ARCHITECTURE.md) | High-level system architecture |
| [CROSS_DOMAIN_ACTIONS.md](CROSS_DOMAIN_ACTIONS.md) | Detailed cross-domain action patterns |
| [STORE_MIGRATION_CONSUMERS.md](STORE_MIGRATION_CONSUMERS.md) | Complete consumer file manifest |
| [SCHEMA_DEPENDENCY_ANALYSIS.md](migrations/SCHEMA_DEPENDENCY_ANALYSIS.md) | Schema migration order |
| [COMPREHENSIVE_CONSUMER_AUDIT.md](COMPREHENSIVE_CONSUMER_AUDIT.md) | Consumer audit status |

---

*Document Version: 1.0*
*Last Updated: 2026-01-22*
*Next Update: After each major migration phase*
