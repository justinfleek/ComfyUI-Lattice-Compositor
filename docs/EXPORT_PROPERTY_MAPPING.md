# Export Property Name Mapping

> **CRITICAL:** This document defines the EXACT property names each export model requires.
> 
> **Purpose:** Prevent export failures by ensuring property names match model expectations exactly.
> **Status:** INCOMPLETE - Need to verify all mappings against actual export functions

---

## The Problem

**If a user works for hours and can't export because property names don't match, that's a critical failure.**

Different export targets require DIFFERENT property names for the same internal data:
- Internal: `layer.transform.position.value.x` (camelCase, nested)
- WanMove: `tracks[N][T][0]` (array indices)
- ATI: `[[{x, y}, ...], ...]` (JSON string, object format)
- MotionCtrl: `camera_poses[frame].RT[0][3]` (snake_case, matrix)

**We MUST document these mappings BEFORE fixing lazy code patterns.**

---

## Export Targets (20+ formats)

### 1. Wan-Move (`wan-move`)

**Export Function:** `exportWanMoveTrackCoordsPackage()` in `wanMoveExport.ts`

**Internal Property:**
```typescript
layer.transform.position.value.x  // camelCase, nested object
layer.transform.position.value.y
```

**Export Property Names:**
```typescript
{
  trackCoords: string;  // JSON string: "[[[x,y],...],...]"
  metadata: {
    numPoints: number;  // camelCase
    numFrames: number;
    width: number;
    height: number;
    fps: number;
  }
}
```

**Schema:** `WanMoveExportPackageSchema` in `wanmove-schema.ts`
- ✅ Schema exists
- ✅ Property names match export function

**ComfyUI Node Input:** `track_coords` (snake_case parameter name)

---

### 2. ATI (`ati`)

**Export Function:** `exportATIPackage()` in `atiExport.ts`

**Internal Property:**
```typescript
layer.transform.position.value.x
layer.transform.position.value.y
```

**Export Property Names:**
```typescript
{
  tracks: string;  // JSON string: "[[{x, y}, ...], ...]"
  width: number;
  height: number;
  numTracks: number;
  originalFrames: number;
}
```

**Schema:** `ATIExportResultSchema` in `ati-schema.ts`
- ✅ Schema exists
- ✅ Property names match export function

**ComfyUI Node Input:** `track_coords` (snake_case parameter name)
**Format:** Fixed 121 frames, `{x, y}` object format (NOT `[x, y]` tuple)

---

### 3. MotionCtrl (`motionctrl`)

**Export Function:** `exportToMotionCtrl()` in `cameraExportFormats.ts`

**Internal Property:**
```typescript
camera.position.x
camera.position.y
camera.position.z
camera.orientation.x
camera.orientation.y
camera.orientation.z
```

**Export Property Names:**
```typescript
{
  camera_poses: Array<{  // snake_case!
    RT: number[][];  // 4x4 matrix
  }>;
}
```

**Schema:** `MotionCtrlOutputSchema` in `camera-schema.ts`
- ✅ Schema exists
- ✅ Property names match export function (`camera_poses`)

**ComfyUI Node Input:** `camera_poses` (snake_case)

---

### 4. MotionCtrl-SVD (`motionctrl-svd`)

**Export Function:** `exportToMotionCtrlSVD()` in `cameraExportFormats.ts`

**Export Property Names:**
```typescript
{
  motion_camera: "zoom_in" | "zoom_out" | "pan_left" | ...;  // snake_case preset
  camera_poses?: string;  // Optional JSON string if complex motion
}
```

**Schema:** Need to check if schema exists
- ⚠️ Need to verify schema matches

---

### 5. CameraCtrl (`animatediff-cameractrl`)

**Export Function:** `exportToCameraCtrl()` in `cameraExportFormats.ts`

**Export Property Names:**
```typescript
{
  poses: Array<{  // camelCase!
    frame: number;
    position: [number, number, number];
    rotation: [number, number, number];
    focal_length: number;  // snake_case!
    frame_length: number;  // snake_case!
  }>;
}
```

**Schema:** Need to check if schema exists
- ⚠️ Need to verify schema matches

**Note:** Mixed naming convention (camelCase `poses`, snake_case `focal_length`)

---

### 6. Wan 2.2 Fun Camera (`wan22-fun-camera`)

**Export Function:** `exportFunCameraPackage()` in `cameraExportFormats.ts`

**Export Property Names:**
```typescript
{
  poses: CameraCtrlPoseEntry[];  // camelCase
  metadata: {
    frameCount: number;  // camelCase
    width: number;
    height: number;
    focalLength: number;  // camelCase
  };
}
```

**Schema:** Need to check if schema exists
- ⚠️ Need to verify schema matches

---

### 7. TTM (`ttm`, `ttm-wan`, `ttm-cogvideox`, `ttm-svd`)

**Export Function:** `exportTTMLayer()` in `modelExport.ts`

**Export Property Names:**
```typescript
{
  layers: Array<{
    layerId: string;  // camelCase
    layerName: string;
    motionMask: string;  // Base64 PNG
    trajectory: Array<{
      frame: number;
      x: number;
      y: number;
    }>;
  }>;
  combinedMask?: string;  // Optional combined mask
}
```

**Schema:** Need to check if schema exists
- ⚠️ Need to verify schema matches

---

### 8. SCAIL (`scail`)

**Export Function:** Need to find

**Export Property Names:**
```typescript
{
  reference_image: string;  // snake_case
  pose_video: string;
  pose_directory?: string;
}
```

**Schema:** Need to check if schema exists
- ⚠️ Need to verify schema matches

---

### 9. Light-X (`light-x`)

**Export Function:** `detectMotionStyle()` in `modelExport.ts`

**Export Property Names:**
```typescript
{
  relighting: {
    source: "sun" | "moon" | "fire" | ...;
    intensity: number;
  };
  motion_style: string;  // snake_case
}
```

**Schema:** Need to check if schema exists
- ⚠️ Need to verify schema matches

---

### 10. Camera-ComfyUI (`camera-comfyui`)

**Export Function:** `exportCameraMatrices()` in `cameraExportFormats.ts`

**Export Property Names:**
```typescript
{
  frames: Array<{
    frame: number;
    view_matrix: number[][];  // snake_case
    projection_matrix: number[][];  // snake_case
  }>;
  metadata: {
    width: number;
    height: number;
    fps: number;
  };
}
```

**Schema:** `CameraExportOutputSchema` in `camera-schema.ts`
- ✅ Schema exists
- ⚠️ Need to verify property names match exactly

---

## Critical Gaps

### ❌ Missing Property Name Mappings

1. **No comprehensive mapping document** showing:
   - Internal property → Export property name
   - Naming convention per target (camelCase vs snake_case)
   - Structure differences (object vs array vs matrix)

2. **Schemas don't document transformations:**
   - Schemas validate structure
   - But don't show HOW internal properties map to export properties
   - Don't show naming convention requirements

3. **Inconsistent naming conventions:**
   - MotionCtrl: `camera_poses` (snake_case)
   - CameraCtrl: `poses` (camelCase) but `focal_length` (snake_case)
   - WanMove: `trackCoords` (camelCase)
   - ATI: `tracks` (camelCase)

---

## What We Need

### 1. Complete Property Mapping Table

| Internal Property | WanMove | ATI | MotionCtrl | CameraCtrl | TTM | SCAIL |
|-------------------|---------|-----|------------|------------|-----|-------|
| `layer.transform.position.value.x` | `tracks[N][T][0]` | `[[{x, y}, ...], ...]` | `camera_poses[].RT[0][3]` | `poses[].position[0]` | `layers[].trajectory[].x` | ? |
| `layer.transform.position.value.y` | `tracks[N][T][1]` | `[[{x, y}, ...], ...]` | `camera_poses[].RT[1][3]` | `poses[].position[1]` | `layers[].trajectory[].y` | ? |
| `camera.position.z` | N/A | N/A | `camera_poses[].RT[2][3]` | `poses[].position[2]` | N/A | ? |

### 2. Naming Convention Documentation

| Export Target | Naming Convention | Examples |
|---------------|-------------------|----------|
| WanMove | camelCase | `trackCoords`, `numPoints` |
| ATI | camelCase | `tracks`, `numTracks` |
| MotionCtrl | snake_case | `camera_poses`, `focal_length` |
| CameraCtrl | Mixed | `poses` (camelCase), `focal_length` (snake_case) |
| TTM | camelCase | `layers`, `layerId`, `motionMask` |
| SCAIL | snake_case | `reference_image`, `pose_video` |

### 3. Schema Validation of Export Names

Schemas should validate that export functions produce the EXACT property names models expect.

---

## Current Status

### ✅ What We Have

- Export schemas exist for: WanMove, ATI, Camera (partial)
- Export functions exist for all targets
- Some schemas match export function outputs

### ❌ What We're Missing

- **Complete property name mapping** (internal → export)
- **Naming convention documentation** per target
- **Verification that schemas enforce exact property names**
- **Schemas for all 20+ export targets**

---

## Next Steps

1. **Audit all export functions** - Document exact property names they produce
2. **Create property mapping table** - Internal → Export for all targets
3. **Verify schemas match export functions** - Ensure schemas enforce exact names
4. **Document naming conventions** - Per export target
5. **THEN fix lazy code patterns** - Use correct property names globally

---

*Document Status: INCOMPLETE - Need to audit all export functions*
