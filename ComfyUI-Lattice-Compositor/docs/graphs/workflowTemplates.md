# workflowTemplates.ts Dependency Analysis

> Generated: 2026-01-10
> Verified via symbol usage

## File Stats
- **Lines:** 2,715
- **Location:** `ui/src/services/comfyui/workflowTemplates.ts`
- **Role:** ComfyUI workflow JSON generators for AI video models

---

## IMPORTS (What it depends on) - 1 dependency

| Import | From |
|--------|------|
| `ComfyUINode`, `ComfyUIWorkflow`, `ExportTarget`, `MotionCtrlSVDPreset`, `NodeConnection`, `Uni3CTrajType`, `Wan22CameraMotion` | `@/types/export` |

**Note:** This file has minimal dependencies - it's mostly self-contained template generation.

---

## EXPORTS (What it provides) - 20 exports

### Types
| Export | Purpose |
|--------|---------|
| `WorkflowParams` | Interface for all workflow parameters |

### Validation
| Export | Purpose |
|--------|---------|
| `validateWorkflowParams()` | Validates params before generation |
| `validateWorkflow()` | Validates generated workflow structure |

### Workflow Generators (16 functions)
| Export | Target Model |
|--------|--------------|
| `generateWan22I2VWorkflow()` | Wan 2.2 Image-to-Video |
| `generateWan22FunCameraWorkflow()` | Wan 2.2 Fun Camera |
| `generateWan22FirstLastWorkflow()` | Wan 2.2 First/Last Frame |
| `generateUni3CWorkflow()` | Uni3C Controlnet |
| `generateMotionCtrlWorkflow()` | MotionCtrl SVD |
| `generateControlNetDepthWorkflow()` | ControlNet Depth |
| `generateAnimateDiffCameraCtrlWorkflow()` | AnimateDiff Camera Control |
| `generateCogVideoXWorkflow()` | CogVideoX |
| `generateTTMWorkflow()` | Time-to-Move |
| `generateSCAILWorkflow()` | SCAIL Pose-driven |
| `generateControlNetWorkflow()` | Generic ControlNet |
| `generateLightXWorkflow()` | Light-X LoRA |
| `generateWanMoveWorkflow()` | WanMove Tracks |
| `generateATIWorkflow()` | ATI Tracks |
| `generateCameraComfyUIWorkflow()` | Camera trajectory |
| `generateWorkflowForTarget()` | Dispatcher for all targets |

### Utilities
| Export | Purpose |
|--------|---------|
| `injectParameters()` | Inject params into existing workflow |

---

## DEPENDENTS (What imports it) - 2 files (VERIFIED)

**Blast radius: 2 files - VERY LOW**

> Verified 2026-01-10 via: `grep -r "from.*workflowTemplates" | grep -v __tests__`

| File | Imports |
|------|---------|
| `services/comfyui/index.ts` | Re-exports all workflow functions |
| `services/export/exportPipeline.ts` | Uses `generateWorkflowForTarget`, `WorkflowParams` |

### Usage Flow

```
User clicks Export →
  exportPipeline.ts calls generateWorkflowForTarget() →
    workflowTemplates.ts generates ComfyUI JSON →
      Sent to ComfyUI backend
```

---

## File Structure Analysis

The file is large (2,715 lines) because it contains **16 workflow generators**, each building complete ComfyUI node graphs:

```typescript
// ~100 lines: Types and validation
export interface WorkflowParams { ... }
export function validateWorkflowParams() { ... }

// ~150 lines: Node factory helpers (internal)
function createNode() { ... }
function connectNodes() { ... }
function createLoadImageNode() { ... }
function createSaveVideoNode() { ... }

// ~150 lines per workflow generator × 16 = ~2,400 lines
export function generateWan22I2VWorkflow() {
  // Build node graph for Wan 2.2 I2V
  const loadImage = createNode("LoadImage", ...);
  const sampler = createNode("KSampler", ...);
  // ... 20-30 nodes per workflow
  return { nodes, connections };
}

// Repeat for each supported model...
```

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                  workflowTemplates.ts                        │
│                     (2,715 lines)                           │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (1 dependency)                                │
│  └── @/types/export (type definitions only)                 │
├─────────────────────────────────────────────────────────────┤
│  EXPORTS (20 items)                                         │
│  ├── 1 type (WorkflowParams)                                │
│  ├── 2 validators                                           │
│  ├── 16 workflow generators                                 │
│  └── 1 utility (injectParameters)                           │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (2 files) ← VERY LOW BLAST RADIUS              │
│  ├── services/comfyui/index.ts (re-export)                  │
│  └── services/export/exportPipeline.ts (main consumer)      │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: VERY LOW**

This is the **safest P0 file to modularize**:
- Only 2 files depend on it
- Pure functions with no side effects
- Each workflow generator is independent
- No state management
- Minimal imports

### Why This File Is Large

Each AI video model requires a different ComfyUI node graph:
- Different nodes (samplers, VAEs, controlnets)
- Different connections
- Different parameters
- Some models need 30+ nodes

16 models × ~150 lines each = 2,400+ lines

### Modularization Strategy

**Split by model family:**

```
services/comfyui/workflows/
├── index.ts                 (~100 lines - types, validation, dispatcher)
├── wan22.ts                 (~400 lines - Wan 2.2 variants)
├── uni3c.ts                 (~150 lines)
├── motionCtrl.ts            (~150 lines)
├── controlNet.ts            (~300 lines - depth, generic)
├── animateDiff.ts           (~150 lines)
├── cogVideoX.ts             (~150 lines)
├── ttm.ts                   (~200 lines - Time-to-Move)
├── scail.ts                 (~150 lines)
├── lightX.ts                (~150 lines)
├── wanMove.ts               (~150 lines)
├── ati.ts                   (~150 lines)
├── camera.ts                (~200 lines - camera trajectory)
└── helpers.ts               (~150 lines - shared node factories)
```

**Benefits:**
1. Each model family in its own file (~150-400 lines)
2. Shared helpers extracted to `helpers.ts`
3. `index.ts` re-exports everything for backwards compatibility
4. Easy to add new models without touching existing code
5. Only 2 files need updating (and one is just re-exports)

### Implementation Steps

1. Create `services/comfyui/workflows/` directory
2. Extract shared helpers to `helpers.ts`
3. Move each `generate*Workflow` to appropriate model file
4. Update `index.ts` to re-export all
5. Update `workflowTemplates.ts` to re-export from new location (or delete)
6. Verify `exportPipeline.ts` and `comfyui/index.ts` still work
7. Run tests

**Estimated effort:** Low (pure refactor, no logic changes)
**Estimated risk:** Very Low (only 2 consumers)
