# System Architecture

> Last Updated: December 2025

---

## Overview

Lattice Compositor is a motion graphics engine built as a ComfyUI extension. It uses a layered architecture with clear separation between presentation, state, engine, and service layers.

---

## Architecture Diagram

```
+-------------------------------------------------------------------------+
|  PRESENTATION LAYER (Vue 3.5 + TypeScript)                              |
|  +-------------------------------------------------------------------+  |
|  | 157 Vue Components                                                 |  |
|  | - WorkspaceLayout.vue    Main application layout                  |  |
|  | - TimelinePanel.vue      Timeline and keyframe editing            |  |
|  | - ThreeCanvas.vue        WebGL viewport                           |  |
|  | - PropertiesPanel.vue    Layer property editing                   |  |
|  | - EffectsPanel.vue       Effect stack management                  |  |
|  +-------------------------------------------------------------------+  |
+---------+---------------------------------------------------------------+
          |
          v
+-------------------------------------------------------------------------+
|  STATE LAYER (Pinia 2.2)                                                |
|  +-------------------------------------------------------------------+  |
|  | compositorStore    Main project state, compositions, layers       |  |
|  | playbackStore      Timeline playback, current frame              |  |
|  | historyStore       Undo/redo (50 snapshots)                      |  |
|  | audioStore         Audio analysis, beat detection                |  |
|  | assetStore         Asset management, file references             |  |
|  | toolStore          Current tool, selection state                 |  |
|  +-------------------------------------------------------------------+  |
+---------+---------------------------------------------------------------+
          |
          v
+-------------------------------------------------------------------------+
|  ENGINE LAYER (Three.js r170)                                           |
|  +-------------------------------------------------------------------+  |
|  | LatticeEngine       Main rendering facade, scene management       |  |
|  | MotionEngine        Deterministic frame evaluation               |  |
|  | LayerManager        26 layer type implementations                |  |
|  | ParticleSystem      Checkpoint-based particle simulation         |  |
|  | EffectProcessor     Canvas-based effect pipeline                 |  |
|  | CameraController    3D camera with camera-controls library       |  |
|  +-------------------------------------------------------------------+  |
+---------+---------------------------------------------------------------+
          |
          v
+-------------------------------------------------------------------------+
|  SERVICE LAYER (181 Services)                                           |
|  +-------------------------------------------------------------------+  |
|  | Animation      interpolation, easing, expressions, propertyDriver |  |
|  | Audio          fftAnalyzer, beatDetection, stemSeparation        |  |
|  | Particles      cpuSimulation, gpuRenderer, presets               |  |
|  | Camera         trajectoryExport, cameraPresets, depthParallax    |  |
|  | Effects        blur, color, distort, generate renderers          |  |
|  | Export         videoExport, matteExport, trajectoryExport        |  |
|  | Security       urlValidator, jsonSanitizer, sesEvaluator         |  |
|  | AI             agentTools, promptBuilder, stateSerializer        |  |
|  +-------------------------------------------------------------------+  |
+---------+---------------------------------------------------------------+
          |
          v
+-------------------------------------------------------------------------+
|  BACKEND (Python + ComfyUI)                                             |
|  +-------------------------------------------------------------------+  |
|  | compositor_node.py         Main ComfyUI node                      |  |
|  | lattice_api_proxy.py       API proxy to frontend                  |  |
|  | controlnet_preprocessors.py ControlNet preprocessing              |  |
|  | lattice_layer_decomposition.py AI layer decomposition             |  |
|  +-------------------------------------------------------------------+  |
+-------------------------------------------------------------------------+
```

---

## Key Directories

```
compositor/
+-- nodes/                  Python ComfyUI nodes (21 files)
+-- scripts/                Python utilities
+-- ui/                     Frontend source
|   +-- src/
|       +-- components/     Vue components (157 files)
|       +-- stores/         Pinia stores
|       +-- services/       Business logic (181 files)
|       +-- types/          TypeScript definitions (23 files)
|       +-- utils/          Utility functions
|       +-- engine/         Three.js rendering
|       +-- __tests__/      Unit tests
|       +-- e2e/            End-to-end tests
+-- web/                    Built output (served by ComfyUI)
+-- templates/              Project templates
```

---

## Data Flow

### Project Load
```
1. User opens project file
2. projectActions.importProject() parses JSON
3. projectMigration.migrateProject() upgrades schema if needed
4. security.validateProjectStructure() validates data
5. compositorStore.project = project
6. LatticeEngine renders first frame
```

### Frame Evaluation
```
1. playbackStore.currentFrame changes
2. MotionEngine.evaluate(frame) called
3. For each layer:
   a. Evaluate property expressions
   b. Interpolate keyframed values
   c. Apply effects
4. Render to Three.js scene
5. Composite to canvas
```

### Export
```
1. User selects export format
2. Export service iterates all frames
3. MotionEngine.evaluate(frame) for each
4. Render to offscreen canvas
5. Encode to output format
6. Save/download file
```

---

## State Management

### compositorStore
Primary state container for project data.

```typescript
interface CompositorState {
  project: LatticeProject;
  activeCompositionId: string;
  selectedLayerIds: string[];
  hasUnsavedChanges: boolean;
}
```

### playbackStore
Timeline and playback state.

```typescript
interface PlaybackState {
  currentFrame: number;
  isPlaying: boolean;
  playbackSpeed: number;
  loopEnabled: boolean;
}
```

### historyStore
Undo/redo with snapshot-based history.

```typescript
interface HistoryState {
  past: ProjectSnapshot[];
  future: ProjectSnapshot[];
  maxSnapshots: 50;
}
```

---

## Security Architecture

### Expression Sandbox
Expressions run in SES (Secure EcmaScript) compartments:
- No access to global objects
- No network access
- CPU time limits
- Memory limits

### Data Validation
All external data passes through validation:
- `validateProjectStructure()` - NaN/Infinity rejection
- `safeJSONParse()` - Error handling
- `sanitizeString()` - XSS prevention

### Template Verification
Official templates are cryptographically signed:
- Ed25519 signatures
- Public key verification
- Tamper detection

---

## Determinism Guarantee

For AI video generation, every frame must be reproducible:

> `evaluate(frame, project)` always returns identical results for identical inputs.

This is achieved through:
- **Seeded RNG** - Mulberry32 algorithm
- **Checkpoint System** - Particles restore state on scrub
- **Pure Evaluation** - No `Math.random()`, no `Date.now()`
