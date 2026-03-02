# Import/Export Types Reference

Complete catalog of all types that can be imported or exported from the Lattice Compositor system.

> **Last Updated:** 2026-01-18  
> **Status:** Complete reference for all import/export types and formats

## Table of Contents
1. [Project Import/Export](#project-importexport)
2. [Template Import/Export](#template-importexport)
3. [Asset Import/Export](#asset-importexport)
4. [Camera Data Import/Export](#camera-data-importexport)
5. [Model-Specific Exports](#model-specific-exports)
6. [Plugin System Types](#plugin-system-types)
7. [Data Import Types](#data-import-types)
8. [Serialization Types](#serialization-types)

---

## Project Import/Export

### `LatticeProject`
**Location:** `ui/src/types/project.ts`

Complete project structure containing compositions, assets, and metadata.

```typescript
export interface LatticeProject {
  meta: ProjectMeta;
  compositions: Composition[];
  assets: Record<string, AssetReference>;
  workflows?: Record<string, ComfyUIWorkflow>;
}
```

**Export Functions:**
- `exportProjectAsFile(project: LatticeProject, filename?: string): void` - Exports as `.lattice.json`

**Import Functions:**
- `importProjectFromFile(file: File): Promise<LatticeProject>` - Imports from `.lattice.json`

**File Format:** `.lattice.json`

---

## Template Import/Export

### `LatticeTemplate`
**Location:** `ui/src/types/templateBuilder.ts`

Template structure for sharing reusable compositions with exposed properties.

```typescript
export interface LatticeTemplate {
  formatVersion: string;
  templateConfig: TemplateConfig;
  composition: any; // Serialized composition
  assets: TemplateAsset[];
  fonts: TemplateFont[];
  posterImage: string; // Base64 encoded
}
```

**Related Types:**
- `TemplateConfig` - Template metadata and exposed properties
- `TemplateAsset` - Embedded asset references
- `TemplateFont` - Font references

**Export Functions:**
- `exportTemplate(composition: Composition, assets: Record<string, AssetReference>, posterImageData: string): Promise<Blob | null>`

**File Format:** `.lattice.json` (template variant)

---

## Asset Import/Export

### `AssetReference`
**Location:** `ui/src/types/assets.ts`

Asset metadata and data references.

```typescript
export interface AssetReference {
  id: string;
  type: AssetType;
  source: "comfyui_node" | "file" | "generated" | "url";
  nodeId?: string;
  width: number;
  height: number;
  data: string; // Base64 or URL
  filename?: string;
  // Video/Audio metadata
  frameCount?: number;
  duration?: number;
  fps?: number;
  hasAudio?: boolean;
  // ... more metadata
}
```

**Asset Types:**
- `"image"` - Standard images (PNG, JPG, WebP)
- `"video"` - Video files (MP4, WebM)
- `"audio"` - Audio files (MP3, WAV, OGG)
- `"model"` - 3D models (GLTF, OBJ, FBX, USD)
- `"depth_map"` - Depth map images

**Import Functions:**
- `importDataAsset(file: File): Promise<DataAssetReference>` - Imports data files (CSV, JSON, TSV, MGJSON)

---

## Camera Data Import/Export

### Camera Export Formats

**Location:** `ui/src/types/export.ts` and `ui/src/services/export/cameraExportFormats.ts`

#### `MotionCtrlCameraData`
MotionCtrl camera pose format (4x4 matrices).

```typescript
export interface MotionCtrlPose {
  RT: number[][]; // 4x4 camera extrinsic matrix
}

export interface MotionCtrlCameraData {
  camera_poses: MotionCtrlPose[];
}
```

#### `MotionCtrlSVDCameraData`
MotionCtrl-SVD preset format.

```typescript
export interface MotionCtrlSVDCameraData {
  motion_camera: MotionCtrlSVDPreset;
  camera_poses?: string;
}
```

#### `Wan22FunCameraData`
Wan 2.2 Fun Camera motion format.

```typescript
export interface Wan22FunCameraData {
  camera_motion: Wan22CameraMotion;
}
```

#### `Uni3CCameraData`
Uni3C camera trajectory format.

```typescript
export interface Uni3CCameraTrajectory {
  zoom: number;
  x_offset: number;
  y_offset: number;
  z_offset: number;
  pitch: number;
  yaw: number;
  roll: number;
}

export interface Uni3CCameraData {
  traj_type: Uni3CTrajType;
  custom_trajectory?: Uni3CCameraTrajectory[];
  keyframes?: Array<{
    frame: number;
    params: Uni3CCameraTrajectory;
    interpolation: "linear" | "bezier";
  }>;
}
```

#### `CameraCtrlPoses`
AnimateDiff CameraCtrl format.

```typescript
export interface CameraCtrlPoses {
  motion_type: CameraCtrlMotionType;
  speed: number;
  frame_length: number;
  prev_poses?: number[][];
}
```

#### `FullCameraExport`
Generic full camera export format.

```typescript
export interface FullCameraFrame {
  frame: number;
  timestamp: number;
  view_matrix: number[][];
  projection_matrix: number[][];
  position: [number, number, number];
  rotation: [number, number, number];
  fov: number;
  focal_length: number;
  focus_distance: number;
}

export interface FullCameraExport {
  frames: FullCameraFrame[];
  metadata: {
    width: number;
    height: number;
    fps: number;
    total_frames: number;
    camera_type: string;
    film_size: number;
  };
}
```

**Export Functions:**
- `exportToMotionCtrl(...)` - MotionCtrl format
- `exportToMotionCtrlSVD(...)` - MotionCtrl-SVD format
- `exportToUni3C(...)` - Uni3C format
- `exportToCameraCtrl(...)` - CameraCtrl format
- `exportCameraMatrices(...)` - Generic 4x4 matrices
- `exportCameraJSON(...)` - JSON format
- `exportToJSX(...)` - JSX automation script

**Import Functions:**
- `importCameraJSON(json: string): Camera3D[]` - Import camera data from JSON
- `importCameraTracking(file: File): Promise<void>` - Import camera tracking data

---

## Model-Specific Exports

### Export Targets
**Location:** `ui/src/types/export.ts`

```typescript
export type ExportTarget =
  | "wan22-i2v" // Wan 2.2 Image-to-Video
  | "wan22-t2v" // Wan 2.2 Text-to-Video
  | "wan22-fun-camera" // Wan 2.2 Fun Camera Control
  | "wan22-first-last" // Wan 2.2 First+Last Frame
  | "uni3c-camera" // Uni3C Camera Control
  | "uni3c-motion" // Uni3C Human Motion + Camera
  | "motionctrl" // MotionCtrl camera poses
  | "motionctrl-svd" // MotionCtrl for SVD
  | "cogvideox" // CogVideoX I2V
  | "controlnet-depth" // Depth map for ControlNet
  | "controlnet-canny" // Canny edge for ControlNet
  | "controlnet-lineart" // Line art for ControlNet
  | "controlnet-pose" // Pose skeleton for ControlNet
  | "animatediff-cameractrl" // AnimateDiff CameraCtrl
  | "custom-workflow" // User's custom workflow
  | "light-x" // Light-X relighting + camera
  | "wan-move" // Wan-Move point trajectories
  | "ati" // ATI Any Trajectory Instruction
  | "ttm" // TTM Time-to-Move cut-and-drag
  | "ttm-wan" // TTM with Wan 2.1 backend
  | "ttm-cogvideox" // TTM with CogVideoX backend
  | "ttm-svd" // TTM with SVD backend
  | "scail" // SCAIL pose-driven video
  | "camera-comfyui"; // camera-comfyUI 4x4 matrices
```

### `ExportConfig`
Complete export configuration.

```typescript
export interface ExportConfig {
  target: ExportTarget;
  width: number;
  height: number;
  frameCount: number;
  fps: number;
  startFrame: number;
  endFrame: number;
  outputDir: string;
  filenamePrefix: string;
  exportDepthMap: boolean;
  exportControlImages: boolean;
  exportCameraData: boolean;
  exportReferenceFrame: boolean;
  exportLastFrame: boolean;
  depthFormat: DepthMapFormat;
  controlType?: ControlType;
  prompt: string;
  negativePrompt: string;
  seed?: number;
  steps?: number;
  cfgScale?: number;
  comfyuiServer?: string;
  autoQueueWorkflow: boolean;
  workflowTemplate?: string;
}
```

### `ExportResult`
Export operation result.

```typescript
export interface ExportResult {
  success: boolean;
  outputFiles: {
    referenceImage?: string;
    lastImage?: string;
    depthSequence?: string[];
    controlSequence?: string[];
    cameraData?: string;
    workflowJson?: string;
    promptId?: string;
  };
  errors: string[];
  warnings: string[];
  duration: number; // milliseconds
}
```

### Wan-Move Export
**Location:** `ui/src/services/export/wanMoveExport.ts`

```typescript
export interface WanMoveTrajectory {
  trajectory: number[][][]; // (N, T, 2) - N points, T frames, x/y coords
  visibility: number[][]; // (N, T) - boolean visibility per point/frame
}
```

**Export Functions:**
- `exportAsJSON(trajectory: WanMoveTrajectory): string`
- `exportAsNPYData(trajectory: WanMoveTrajectory): { data: ArrayBuffer; shape: number[] }`
- `exportWanMovePackage(trajectory: WanMoveTrajectory): Promise<Blob>`
- `exportWanMoveTrackCoordsJSON(trajectory: WanMoveTrajectory): string`
- `exportWanMoveVisibility(trajectory: WanMoveTrajectory): string`

### ATI Export
**Location:** `ui/src/services/export/atiExport.ts`

```typescript
export function exportATITrackCoordsJSON(trajectory: WanMoveTrajectory): string
export function exportATIPackage(trajectory: WanMoveTrajectory): Promise<Blob>
export function exportAsNormalizedATI(trajectory: WanMoveTrajectory): { data: ArrayBuffer; shape: number[] }
```

### TTM Export
**Location:** `ui/src/services/modelExport.ts`

```typescript
export function exportTTMLayer(...): TTMExportData
```

### Pose Export
**Location:** `ui/src/services/export/poseExport.ts`

```typescript
export interface OpenPoseJSON {
  version: number;
  people: Array<{
    person_id: number[];
    pose_keypoints_2d: number[];
    face_keypoints_2d: number[];
    hand_left_keypoints_2d: number[];
    hand_right_keypoints_2d: number[];
  }>;
}
```

**Export Functions:**
- `exportToOpenPoseJSON(poses: Pose[]): OpenPoseJSON`
- `exportPoseSequence(...): string`
- `exportPoseForControlNet(...): string`

**Import Functions:**
- `importFromOpenPoseJSON(json: OpenPoseJSON): Pose[]`
- `importPoseSequence(...): Pose[]`

### Mesh Deform Export
**Location:** `ui/src/services/export/meshDeformExport.ts`

**Export Functions:**
- `exportPinsAsTrajectory(...): WanMoveTrajectory`
- `exportPinsAsTrajectoryWithMetadata(...): { trajectory: WanMoveTrajectory; metadata: {...} }`
- `exportOverlapAsDepth(...): ArrayBuffer`
- `exportDeformedMeshMask(...): ImageData`
- `exportDeformedMeshMaskBinary(...): ArrayBuffer`
- `exportPinPositionsPerFrame(...): number[][][]`
- `exportOverlapDepthSequence(...): ArrayBuffer[]`
- `exportMeshMaskSequence(...): ImageData[]`

---

## Plugin System Types

**Location:** `ui/src/services/plugins/PluginManager.ts`

### `PluginManifest`
Plugin registration manifest.

```typescript
export interface PluginManifest {
  id: string;
  name: string;
  version: string;
  description: string;
  type: PluginType;
  author?: string;
  homepage?: string;
  apiVersion?: string;
  permissions?: PluginPermission[];
  entryPoint: string;
}
```

### `LatticePluginAPI`
Plugin API surface.

```typescript
export interface LatticePluginAPI {
  getProject(): LatticeProject;
  getCurrentFrame(): number;
  getSelectedLayers(): string[];
  getLayer(id: string): Layer;
  getComposition(id: string): Composition;
  getAsset(id: string): AssetReference;
  on<T extends PluginEvent>(event: T, callback: PluginEventCallback<T>): () => void;
  off<T extends PluginEvent>(event: T, callback: PluginEventCallback<T>): void;
  registerPanel(panel: PanelDefinition): void;
  registerMenuItem(item: MenuItemDefinition): void;
  registerContextMenu(menu: ContextMenuDefinition): void;
  registerEffect?(effect: EffectDefinition): void;
  registerExporter?(exporter: ExporterDefinition): void;
  registerTool?(tool: ToolDefinition): void;
  showNotification(message: string, type?: "info" | "success" | "warning" | "error"): void;
  log: { debug(...args: LoggableValue[]): void; ... };
}
```

### `ExporterDefinition`
Plugin exporter registration.

```typescript
export interface ExporterDefinition {
  id: string;
  name: string;
  extension: string;
  export: (project: LatticeProject, options: ExportOptions) => Promise<Blob>;
}
```

### `ExportOptions`
Options passed to exporter plugins.

```typescript
export interface ExportOptions {
  fps: number;
  quality: number;
  [key: string]: string | number | boolean | string[] | number[];
}
```

---

## Data Import Types

**Location:** `ui/src/services/dataImport.ts`

### `DataAssetReference`
Data file asset (CSV, JSON, TSV, MGJSON).

```typescript
export interface DataAssetReference {
  id: string;
  name: string;
  type: "json" | "csv" | "tsv" | "mgjson";
  rawContent: string;
  lastModified: number;
  sourceData?: any; // Parsed JSON
  headers?: string[]; // CSV/TSV headers
  rows?: string[][]; // CSV/TSV rows
  numRows?: number;
  numColumns?: number;
}
```

**Import Functions:**
- `importDataFromFile(file: File): Promise<DataParseResult>`

### Track Points Import/Export
**Location:** `ui/src/services/trackPointService.ts`

```typescript
export interface TrackPoint2D {
  id: string;
  x: number;
  y: number;
  frame: number;
}

export interface TrackPoint3D {
  id: string;
  x: number;
  y: number;
  z: number;
  frame: number;
}
```

**Export Functions:**
- `exportTrackPoints2D(): TrackPoint2D[]`

**Import Functions:**
- `importTrackPoints2D(points: TrackPoint2D[]): void`
- `importTrackPoints3D(points: TrackPoint3D[]): void`

---

## Serialization Types

### Project State Serialization
**Location:** `ui/src/services/ai/stateSerializer.ts`

**Export Functions:**
- `serializeProjectState(includeKeyframes?: boolean): string`
- `serializeLayerList(): string`
- `serializeLayerDetails(layerId: string): string`
- `serializeProjectStateMinimal(): string`

### Global Light Serialization
**Location:** `ui/src/services/globalLight.ts`

**Export Functions:**
- `serializeGlobalLight(): string`

**Import Functions:**
- `deserializeGlobalLight(json: string): GlobalLightSettings`

### Persistence Service
**Location:** `ui/src/services/persistenceService.ts`

**Export Functions:**
- `exportAllData(): Promise<Blob>` - Exports all application data

**Import Functions:**
- `importData(blob: Blob): Promise<void>` - Imports all application data

### Audit Log Export
**Location:** `ui/src/services/security/auditLog.ts`

**Export Functions:**
- `exportAuditLog(query?: AuditLogQuery): Promise<string>`

---

## Video/Frame Export Types

### `VideoFormat`
```typescript
export type VideoFormat = "mp4" | "webm" | "gif" | "webp" | "image_sequence";
```

### `FrameSequenceFormat`
```typescript
export type FrameSequenceFormat =
  | "png" // Lossless, 8-bit RGBA
  | "jpeg" // Lossy, 8-bit RGB
  | "webp" // Modern format
  | "tiff" // 8/16-bit
  | "exr" // HDR 16/32-bit float
  | "dpx"; // Film 10/16-bit
```

### `FrameSequenceOptions`
```typescript
export interface FrameSequenceOptions {
  format: FrameSequenceFormat;
  quality: number; // 0-100
  filenamePattern: string;
  outputDir: string;
  bitDepth?: 8 | 10 | 16 | 32;
  colorSpace?: "sRGB" | "Linear" | "ACEScg" | "Rec709";
}
```

**Export Functions:**
- `exportCanvasToBlob(...): Promise<Blob>`
- `exportCanvasToDataURL(...): string`
- `exportViaBackend(...): Promise<Blob>`
- `exportFrameSequence(...): Promise<void>`

---

## SVG Export

**Location:** `ui/src/services/svgExport.ts`

**Export Functions:**
- `exportSplineLayerToSVG(...): string`
- `exportCompositionToSVG(...): string`
- `exportSplineLayer(...): string`
- `exportLayers(...): string`

---

## ComfyUI Integration Types

### `ComfyUIWorkflow`
**Location:** `ui/src/types/export.ts`

```typescript
export interface ComfyUINode {
  class_type: string;
  inputs: Record<string, any>;
  _meta?: {
    title: string;
  };
}

export interface ComfyUIWorkflow {
  [nodeId: string]: ComfyUINode;
}
```

### `ComfyUIPromptResult`
```typescript
export interface ComfyUIPromptResult {
  prompt_id: string;
  number: number;
  node_errors?: Record<string, string>;
}
```

**Export Functions:**
- `exportToComfyUI(...): Promise<ComfyUIWorkflow>`

---

## Summary

### File Formats Supported

1. **`.lattice.json`** - Project and template files
2. **`.json`** - Camera data, poses, trajectories, workflows
3. **`.npy`** - NumPy array data (Wan-Move, ATI)
4. **`.csv`** - CSV data files
5. **`.tsv`** - TSV data files
6. **`.mgjson`** - Motion Graphics JSON
7. **`.svg`** - SVG vector graphics
8. **Video formats** - MP4, WebM, GIF, WebP
9. **Image sequences** - PNG, JPEG, WebP, TIFF, EXR, DPX

### Main Export Categories

1. **Project Export** - Complete project state
2. **Template Export** - Reusable composition templates
3. **Camera Export** - Camera trajectories in various formats
4. **Model Export** - Format-specific exports for AI models
5. **Trajectory Export** - Point trajectories (Wan-Move, ATI, TTM)
6. **Pose Export** - Human pose data (OpenPose format)
7. **Depth Export** - Depth map sequences
8. **Control Export** - ControlNet control images
9. **Mesh Export** - Mesh deformation data
10. **Frame Export** - Video/image sequence export
11. **SVG Export** - Vector graphics export

### Main Import Categories

1. **Project Import** - Complete project state
2. **Camera Import** - Camera tracking data
3. **Data Import** - CSV, JSON, TSV, MGJSON files
4. **Pose Import** - OpenPose JSON format
5. **Track Points Import** - 2D/3D tracking points
6. **Asset Import** - Media files (images, video, audio, 3D models)
