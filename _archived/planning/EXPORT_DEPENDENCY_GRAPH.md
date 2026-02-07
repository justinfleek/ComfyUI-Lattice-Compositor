# EXPORT SYSTEM DEPENDENCY GRAPH

> **Created:** 2026-01-11
> **Purpose:** Document the current state architecture before Phase 1 migration
> **Status:** CURRENT STATE (before Kijai-compatible wiring)

---

## 1. HIGH-LEVEL DATA FLOW

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           USER INTERACTION                                    │
│                                                                               │
│   Layer Creation → Keyframe Animation → Position/Transform Changes           │
└───────────────────────────────────┬───────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                              STORES                                          │
│                                                                               │
│   compositorStore ─────┬───── layers: Layer[]                                │
│                        ├───── cameras: Map<string, Camera3D>                 │
│                        ├───── cameraKeyframes: Map<string, CameraKeyframe[]> │
│                        └───── composition: {width, height, fps, frameCount}  │
└───────────────────────────────────┬───────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                         EVALUATION LAYER                                     │
│                                                                               │
│   interpolateProperty() ←── Keyframe[] ──→ value at frame N                  │
│           │                                                                   │
│           ▼                                                                   │
│   evaluateLayerCached() ←── Layer + frame ──→ EvaluatedLayer                 │
│           │                                                                   │
│           ▼                                                                   │
│   EvaluatedLayer {                                                           │
│     transform: {position: {x,y,z}, scale: {x,y,z}, rotation: number}        │
│     opacity: number                                                          │
│     properties: {...}                                                        │
│   }                                                                          │
└───────────────────────────────────┬───────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                       TRAJECTORY EXTRACTION                                  │
│                                                                               │
│   extractLayerTrajectory(layer, startFrame, endFrame, getPositionAtFrame)   │
│           │                                                                   │
│           ▼                                                                   │
│   PointTrajectory {                                                          │
│     id: string                                                               │
│     points: [{frame, x, y, z?}]    ← INTERMEDIATE FORMAT                    │
│     visibility: boolean[]                                                    │
│     rotation?: [{frame, x, y, z}]                                           │
│     scale?: [{frame, x, y}]                                                  │
│   }                                                                          │
└───────────────────────────────────┬───────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                        FORMAT EXPORTERS                                      │
│                                                                               │
│   ┌─────────────────────┐   ┌─────────────────────┐   ┌──────────────────┐  │
│   │ exportWanMove       │   │ exportATI           │   │ exportCamera     │  │
│   │ Trajectories()      │   │ Trajectory()        │   │ Trajectory()     │  │
│   │                     │   │                     │   │                  │  │
│   │ IN: PointTrajectory │   │ IN: PointTrajectory │   │ IN: Camera3D[]   │  │
│   │ OUT: number[][][]   │   │ OUT: ATIInstruction │   │ OUT: number[][]  │  │
│   │      [x,y] arrays   │   │      semantic type  │   │      4x4 matrix  │  │
│   └─────────────────────┘   └─────────────────────┘   └──────────────────┘  │
│              │                        │                        │             │
│              │    OLD FORMAT          │    OLD FORMAT          │ OLD FORMAT  │
│              ▼                        ▼                        ▼             │
│   WanMoveTrajectoryExport    ATITrajectoryInstruction   CameraTrajectory    │
│   {                          {                          Export {            │
│     trajectories: [[[x,y]]]    type: "pan"|"free"|...    matrices: [[4x4]] │
│     visibility: [[0|1]]        panSpeed?: {x,y}          metadata: {...}   │
│     metadata: {...}            points?: [{x,y}]        }                    │
│   }                          }                                              │
└───────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────────────┐
│                        NEW KIJAI EXPORTERS                                   │
│                    (Created but NOT wired to pipeline)                       │
│                                                                               │
│   ┌─────────────────────┐   ┌─────────────────────┐   ┌──────────────────┐  │
│   │ exportAsKijai       │   │ exportAsKijaiATI()  │   │ exportAsCamera   │  │
│   │ WanMoveJSON()       │   │                     │   │ CtrlPoses()      │  │
│   │                     │   │ IN: WanMoveTraject  │   │                  │  │
│   │ IN: WanMoveTraject  │   │ OUT: JSON string    │   │ IN: Camera3D[]   │  │
│   │ OUT: JSON string    │   │      121 frames     │   │ OUT: text string │  │
│   │      [{x,y}] objs   │   │      {x,y} objects  │   │      pose format │  │
│   └─────────────────────┘   └─────────────────────┘   └──────────────────┘  │
│                                                                               │
│   File: wanMoveExport.ts     File: atiExport.ts      File: cameraExport     │
│                                                             Formats.ts       │
└───────────────────────────────────────────────────────────────────────────────┘
```

---

## 2. INTERNAL DATA FORMATS

### 2.1 Source Format: Layer Transform

**File:** `ui/src/types/project.ts` (lines 506-615)

```typescript
Layer {
  transform: LayerTransform {
    position: AnimatableProperty<{x: number, y: number, z?: number}>
    scale: AnimatableProperty<{x: number, y: number, z?: number}>
    rotation: AnimatableProperty<number>  // degrees
    origin: AnimatableProperty<{x: number, y: number, z?: number}>
  }
}

AnimatableProperty<T> {
  value: T                    // Default/constant value
  keyframes?: Keyframe[]      // Animation keyframes
  expression?: Expression     // Custom evaluator
  propertyDriver?: Driver     // Property linking
}

Keyframe {
  frame: number
  value: number
  interpolationType: "linear" | "bezier" | "hold" | "easing"
  inHandle?: BezierHandle
  outHandle?: BezierHandle
}
```

### 2.2 Intermediate Format: PointTrajectory

**File:** `ui/src/services/modelExport.ts` (lines 115-122)

```typescript
PointTrajectory {
  id: string
  points: Array<{
    frame: number
    x: number        // Pixels (screen space)
    y: number        // Pixels (screen space)
    z?: number       // Optional depth
  }>
  visibility: boolean[]
  rotation?: Array<{frame: number, x: number, y: number, z: number}>
  scale?: Array<{frame: number, x: number, y: number}>
}
```

**Created by:** `extractLayerTrajectory()` at modelExport.ts:204-272

### 2.3 OLD Output Format: WanMoveTrajectoryExport

**File:** `ui/src/services/modelExport.ts` (lines 128-147)

```typescript
WanMoveTrajectoryExport {
  trajectories: number[][][]   // [num_points][num_frames][2 or 3]
                               // Inner arrays: [x, y] or [x, y, z]
  visibility: number[][]       // [num_points][num_frames] with 0 or 1
  rotations?: number[][][]     // [num_points][num_frames][3]
  scales?: number[][][]        // [num_points][num_frames][2]
  metadata: {
    numPoints: number
    numFrames: number
    imageWidth: number         // NOTE: imageWidth, NOT width
    imageHeight: number        // NOTE: imageHeight, NOT height
    is3D: boolean
    hasRotation: boolean
    hasScale: boolean
  }
}
```

**Created by:** `exportWanMoveTrajectories()` at modelExport.ts:322-399

### 2.4 OLD Output Format: ATITrajectoryInstruction

**File:** `ui/src/services/modelExport.ts` (lines 420-428)

```typescript
ATITrajectoryInstruction {
  type: "free" | "circular" | "static" | "pan"  // Semantic classification
  points?: Array<{x: number, y: number}>        // For "free" type only
  center?: {x: number, y: number}               // For "circular" type
  radius?: number                               // For "circular" type
  panSpeed?: {x: number, y: number}             // For "pan" type (px/frame)
}
```

**Created by:** `exportATITrajectory()` at modelExport.ts:454-503

### 2.5 OLD Output Format: CameraTrajectoryExport

**File:** `ui/src/services/modelExport.ts` (lines 71-82)

```typescript
CameraTrajectoryExport {
  matrices: number[][][]       // [frame][4][4] row-major transformation matrices
  metadata: {
    frameCount: number
    fps: number
    fov: number
    nearClip: number
    farClip: number
    width: number
    height: number
  }
}
```

**Created by:** `exportCameraTrajectory()` at modelExport.ts:84-104

---

## 3. NEW KIJAI-COMPATIBLE FORMATS

### 3.1 NEW: WanMove JSON (Kijai expects)

**File:** `ui/src/services/export/wanMoveExport.ts`

```typescript
// OUTPUT: JSON string
// Format: [[{x, y}, {x, y}, ...], ...]
//         ^track   ^frame points

// Example:
[
  [{"x": 100, "y": 200}, {"x": 110, "y": 205}, {"x": 120, "y": 210}],
  [{"x": 500, "y": 300}, {"x": 510, "y": 305}, {"x": 520, "y": 310}]
]
```

**Key difference:** `{x, y}` objects instead of `[x, y]` arrays

### 3.2 NEW: ATI JSON (Kijai expects)

**File:** `ui/src/services/export/atiExport.ts`

```typescript
// OUTPUT: JSON string
// Format: [[{x, y}, ...121 frames...], ...]
// ALWAYS exactly 121 frames (padded with last position if shorter)
// Coordinates in PIXEL space (Kijai normalizes internally)

ATI_FIXED_FRAMES = 121
```

**Key differences:**
- Fixed 121 frames (not variable)
- Raw pixel coordinates (not semantic type)
- `{x, y}` objects (not type classification)

### 3.3 NEW: CameraCtrl Poses (Kijai expects)

**File:** `ui/src/services/export/cameraExportFormats.ts`

```typescript
// OUTPUT: Text string, one line per frame
// Format: "time fx fy cx cy aspect flag1 flag2 w2c[0] ... w2c[11]"
//
// time: frame number
// fx, fy: focal length in pixels
// cx, cy: principal point (usually 0.5, 0.5)
// aspect: width/height
// flags: unused (0, 0)
// w2c[12]: 3x4 world-to-camera matrix, row-major

// Example line:
"0 1000.5 1000.5 0.5 0.5 1.777 0 0 1 0 0 0 0 1 0 0 0 0 1 -500"
```

**Key differences:**
- Text format (not JSON object)
- Intrinsics included inline (not separate metadata)
- 3x4 matrix (not 4x4)

---

## 4. STORES & DATA PROVIDERS

### 4.1 compositorStore (Primary)

**File:** `ui/src/stores/compositorStore.ts`

**Provides:**
| Data | Type | Used By |
|------|------|---------|
| `project.compositions[].layers` | `Layer[]` | All exports |
| `cameras` | `Map<string, Camera3D>` | Camera exports |
| `cameraKeyframes` | `Map<string, CameraKeyframe[]>` | Camera interpolation |
| `composition.width` | `number` | Dimension metadata |
| `composition.height` | `number` | Dimension metadata |
| `composition.fps` | `number` | Frame timing |
| `composition.frameCount` | `number` | Range calculation |

### 4.2 layerEvaluationCache (Evaluation)

**File:** `ui/src/services/layerEvaluationCache.ts`

**Provides:**
| Function | Returns | Used By |
|----------|---------|---------|
| `evaluateLayerCached(layer, frame, fps)` | `EvaluatedLayer` | Position accessor |

**Cache key:** `${layerId}:${frame}`
**Invalidation:** On layer version change via `markLayerDirty()`

### 4.3 interpolation (Pure Functions)

**File:** `ui/src/services/interpolation.ts`

**Provides:**
| Function | Returns | Used By |
|----------|---------|---------|
| `interpolateProperty(prop, frame)` | `number \| object` | Layer evaluation |
| `interpolateKeyframes(keyframes, frame)` | `number` | Direct keyframe access |

**No state, no side effects, deterministic**

---

## 5. DATA FLOW: LAYER → TRAJECTORY EXPORT

### Step-by-Step Flow

```
1. USER CREATES LAYER
   └─→ Layer added to compositorStore.project.compositions[].layers
   └─→ Layer has transform.position.value = {x: 100, y: 200}

2. USER ADDS KEYFRAMES
   └─→ Keyframes added to layer.transform.position.keyframes[]
   └─→ Example: [{frame: 0, value: {x:100, y:200}}, {frame: 30, value: {x:500, y:400}}]

3. USER TRIGGERS EXPORT
   └─→ ComfyUIExportDialog calls exportToComfyUI(layers, cameraKeyframes, config)
   └─→ Creates ExportPipeline with layers array

4. PIPELINE EXTRACTS TRAJECTORIES (modelExport.ts:862-907)
   └─→ For each animated layer:
       └─→ Creates position accessor function:
           getPositionAtFrame = (layer, frame) => {
             const evaluated = evaluateLayerCached(layer, frame, fps)
             return {x: evaluated.transform.position.x, y: evaluated.transform.position.y}
           }
       └─→ Calls extractLayerTrajectory(layer, startFrame, endFrame, getPositionAtFrame)
       └─→ Returns PointTrajectory

5. PIPELINE FORMATS EXPORT (modelExport.ts:878-882)
   └─→ Calls exportWanMoveTrajectories(trajectories, width, height)
   └─→ Converts PointTrajectory[] to WanMoveTrajectoryExport
   └─→ Trajectories become number[][][] with [x, y] arrays

6. CURRENT OUTPUT (OLD FORMAT - BROKEN)
   └─→ {
         trajectories: [[[100, 200], [113, 207], ..., [500, 400]]],
         visibility: [[1, 1, 1, ...]],
         metadata: {numPoints: 1, numFrames: 31, imageWidth: 1920, imageHeight: 1080, ...}
       }

7. KIJAI EXPECTS (NEW FORMAT - NOT WIRED)
   └─→ JSON string: [[{"x":100,"y":200}, {"x":113,"y":207}, ..., {"x":500,"y":400}]]
```

---

## 6. CRITICAL CONVERSION POINTS

### 6.1 Where Format Changes

| Step | Current Function | Output Format | Needs Change |
|------|-----------------|---------------|--------------|
| 4 | `extractLayerTrajectory()` | `PointTrajectory` (internal) | ❌ Keep |
| 5 | `exportWanMoveTrajectories()` | `[x, y]` arrays | ✅ **REPLACE** |
| 5 | `exportATITrajectory()` | Semantic type | ✅ **REPLACE** |
| 5 | `exportCameraTrajectory()` | 4x4 matrices | ✅ **REPLACE** |

### 6.2 What the Adapters Bridge

```
PointTrajectory (internal)
       │
       ├──→ OLD: exportWanMoveTrajectories() → number[][][] [x,y]
       │
       └──→ NEW: legacyWanMoveExport() → string [[{x,y}]]
                        │
                        └─→ convertPointTrajectoriesToWanMove()
                        └─→ exportAsKijaiWanMoveJSON()
```

---

## 7. FILE REFERENCE MAP

### Export Entry Points
| File | Key Exports |
|------|-------------|
| `services/export/index.ts` | Re-exports everything (150+ symbols) |
| `services/export/exportPipeline.ts` | `ExportPipeline`, `exportToComfyUI()` |
| `services/modelExport.ts` | OLD format functions (to deprecate) |

### NEW Kijai-Compatible Exporters
| File | Key Exports |
|------|-------------|
| `services/export/wanMoveExport.ts` | `exportAsKijaiWanMoveJSON()` |
| `services/export/atiExport.ts` | `exportAsKijaiATI()` |
| `services/export/cameraExportFormats.ts` | `exportAsCameraCtrlPoses()` |

### Data Types
| File | Key Types |
|------|-----------|
| `types/project.ts` | `Layer`, `LayerTransform`, `AnimatableProperty` |
| `types/camera.ts` | `Camera3D`, `CameraKeyframe` |
| `services/modelExport.ts` | `PointTrajectory`, `WanMoveTrajectoryExport` |

### Evaluation
| File | Key Functions |
|------|---------------|
| `services/layerEvaluationCache.ts` | `evaluateLayerCached()` |
| `services/interpolation.ts` | `interpolateProperty()` |
| `engine/MotionEngine.ts` | `FrameState`, `EvaluatedLayer` |

---

## 8. MIGRATION IMPACT ANALYSIS

### 8.1 Functions to Replace

| Old Function | Location | New Function | New Location |
|--------------|----------|--------------|--------------|
| `exportWanMoveTrajectories()` | modelExport.ts:322 | `exportAsKijaiWanMoveJSON()` | wanMoveExport.ts |
| `exportATITrajectory()` | modelExport.ts:454 | `exportAsKijaiATI()` | atiExport.ts |
| `exportCameraTrajectory()` | modelExport.ts:84 | `exportAsCameraCtrlPoses()` | cameraExportFormats.ts |

### 8.2 Call Sites to Update

| File | Line | Current Call | New Call |
|------|------|--------------|----------|
| modelExport.ts | 878 | `exportWanMoveTrajectories(...)` | `legacyWanMoveExport(...)` |
| modelExport.ts | 923 | `exportATITrajectory(...)` | `legacyATIExport(...)` |
| modelExport.ts | 842 | `exportCameraTrajectory(...)` | Keep (internal use) |
| modelExport.ts | 1118 | `exportWanMoveTrajectories(...)` | `legacyWanMoveExport(...)` |

### 8.3 Type Signature Changes

**WanMove:**
- OLD: `(trajectories: PointTrajectory[], width, height) => WanMoveTrajectoryExport`
- NEW: `(trajectory: WanMoveTrajectory) => string`

**ATI:**
- OLD: `(trajectory: PointTrajectory, width, height) => ATITrajectoryInstruction`
- NEW: `(trajectory: WanMoveTrajectory) => string`

**Camera:**
- OLD: `(cameras: Camera3D[], fps, width, height) => CameraTrajectoryExport`
- NEW: `(cameras: Camera3D[], width, height, fps) => string`

---

## 9. VERIFICATION QUERIES

```bash
# Find all usages of old export functions
grep -rn "exportWanMoveTrajectories\|exportATITrajectory\|exportCameraTrajectory" \
  ui/src/services/ --include="*.ts"

# Find all imports of old functions
grep -rn "import.*exportWanMoveTrajectories\|import.*exportATITrajectory" \
  ui/src/ --include="*.ts"

# Verify new functions exist
ls -la ui/src/services/export/wanMoveExport.ts
ls -la ui/src/services/export/atiExport.ts
ls -la ui/src/services/export/cameraExportFormats.ts
```

---

*Document Version: 1.0*
*Last Updated: 2026-01-11*
