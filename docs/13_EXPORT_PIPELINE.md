# WEYL COMPOSITOR — EXPORT PIPELINE

**Document ID**: 13_EXPORT_PIPELINE  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md), [02_MOTION_ENGINE.md](./02_MOTION_ENGINE.md)

> Weyl is a **conditioning compiler**, not a renderer.
> Exports are deterministic buffers for diffusion models.

---

## 1. CORE PHILOSOPHY

Weyl exports **conditioning data**, not final images.

```
Weyl Project
       ↓
MotionEngine.evaluate() per frame
       ↓
Export Buffers (Depth, Motion, Mask, etc.)
       ↓
ComfyUI / Diffusion Pipeline
       ↓
Final Rendered Output
```

**Weyl's job ends at conditioning buffers. Rendering is done by diffusion models.**

---

## 2. EXPORT ARTIFACTS

### 2.1 Required Exports

| Artifact | Shape | Format | Description |
|----------|-------|--------|-------------|
| **RGBA** | H×W×4 | PNG/EXR | Color + alpha |
| **Depth** | H×W×1 | EXR (float32) | Z-depth normalized [0,1] |
| **Motion** | H×W×2 | EXR (float32) | Optical flow (dx, dy) |
| **Mask** | H×W×1 | PNG (uint8) | Binary/soft masks |
| **Normal** | H×W×3 | EXR (float32) | Surface normals [-1,1] |
| **ID Map** | H×W×1 | PNG (uint16) | Instance segmentation |

### 2.2 Optional Exports

| Artifact | Shape | Format | Description |
|----------|-------|--------|-------------|
| **Camera** | N×10 | NPY/JSON | Position, forward, up, fov per frame |
| **Audio** | N×F | NPY | Audio features per frame |
| **Particles** | N×P×7 | NPY | Particle positions per frame |
| **Edges** | H×W×1 | PNG | Edge detection |
| **Semantic** | H×W×1 | PNG | Semantic segmentation |

---

## 3. FILE NAMING CONVENTION

```
exports/
├── project_name/
│   ├── rgba/
│   │   ├── frame_000001.exr
│   │   ├── frame_000002.exr
│   │   └── ...
│   ├── depth/
│   │   ├── frame_000001.exr
│   │   └── ...
│   ├── motion/
│   │   ├── frame_000001.exr
│   │   └── ...
│   ├── mask/
│   │   ├── layer_fg/
│   │   │   ├── frame_000001.png
│   │   │   └── ...
│   │   └── layer_bg/
│   │       └── ...
│   ├── normal/
│   │   └── ...
│   ├── camera/
│   │   └── trajectory.json
│   ├── audio/
│   │   └── features.npz
│   └── metadata.json
```

### 3.1 Frame Padding

```typescript
const FRAME_PADDING = 6  // 000001, 000002, etc.

function formatFrameNumber(frame: number): string {
  return frame.toString().padStart(FRAME_PADDING, '0')
}
```

---

## 4. EXPORT CONFIGURATION

```typescript
interface ExportConfig {
  readonly outputPath: string
  readonly frameRange: [number, number]
  readonly resolution: { width: number, height: number }
  readonly framePadding: number
  
  // Which buffers to export
  readonly artifacts: {
    readonly rgba: boolean
    readonly depth: boolean
    readonly motion: boolean
    readonly mask: boolean | string[]  // true = all layers, string[] = specific layers
    readonly normal: boolean
    readonly idMap: boolean
    readonly camera: boolean
    readonly audio: boolean
    readonly particles: boolean
  }
  
  // Format options
  readonly formats: {
    readonly colorFormat: 'exr' | 'png'
    readonly floatFormat: 'exr' | 'npy'
    readonly maskFormat: 'png' | 'exr'
  }
  
  // Quality options
  readonly depthRange: [number, number]  // Near, far for normalization
  readonly motionScale: number           // Scale factor for motion vectors
}
```

---

## 5. EXPORT PIPELINE

### 5.1 Main Export Function

```typescript
async function exportProject(
  project: WeylProject,
  config: ExportConfig,
  onProgress?: (frame: number, total: number) => void
): Promise<ExportResult> {
  const [startFrame, endFrame] = config.frameRange
  const totalFrames = endFrame - startFrame + 1
  
  // Create output directories
  await createExportDirectories(config)
  
  // Export each frame
  const checksums: Record<string, string[]> = {}
  
  for (let frame = startFrame; frame <= endFrame; frame++) {
    // 1. Evaluate frame through MotionEngine
    const frameState = motionEngine.evaluate(
      frame,
      project,
      project.audioAnalysis
    )
    
    // 2. Render buffers
    const buffers = renderExportBuffers(frameState, config)
    
    // 3. Save buffers to disk
    const frameChecksums = await saveFrameBuffers(
      buffers,
      frame,
      config
    )
    
    // 4. Accumulate checksums
    for (const [type, checksum] of Object.entries(frameChecksums)) {
      checksums[type] = checksums[type] || []
      checksums[type].push(checksum)
    }
    
    // 5. Report progress
    onProgress?.(frame - startFrame + 1, totalFrames)
  }
  
  // Export non-frame data
  if (config.artifacts.camera) {
    await exportCameraTrajectory(project, config)
  }
  
  if (config.artifacts.audio && project.audioAnalysis) {
    await exportAudioFeatures(project.audioAnalysis, config)
  }
  
  // Generate metadata
  const metadata = generateExportMetadata(project, config, checksums)
  await saveMetadata(metadata, config)
  
  return { success: true, metadata }
}
```

### 5.2 Buffer Rendering

```typescript
interface ExportBuffers {
  rgba?: ImageBuffer
  depth?: Float32Array
  motion?: Float32Array  // Interleaved dx, dy
  mask?: Map<string, ImageBuffer>  // Per-layer masks
  normal?: Float32Array
  idMap?: Uint16Array
}

function renderExportBuffers(
  frameState: FrameState,
  config: ExportConfig
): ExportBuffers {
  const { width, height } = config.resolution
  const buffers: ExportBuffers = {}
  
  // RGBA
  if (config.artifacts.rgba) {
    buffers.rgba = renderRGBA(frameState, width, height)
  }
  
  // Depth
  if (config.artifacts.depth) {
    buffers.depth = renderDepth(
      frameState,
      width,
      height,
      config.depthRange
    )
  }
  
  // Motion vectors
  if (config.artifacts.motion) {
    buffers.motion = renderMotionVectors(
      frameState,
      width,
      height,
      config.motionScale
    )
  }
  
  // Masks (per layer or all)
  if (config.artifacts.mask) {
    const layerIds = config.artifacts.mask === true
      ? frameState.layers.map(l => l.id)
      : config.artifacts.mask
    
    buffers.mask = new Map()
    for (const layerId of layerIds) {
      const layer = frameState.layers.find(l => l.id === layerId)
      if (layer) {
        buffers.mask.set(layerId, renderLayerMask(layer, width, height))
      }
    }
  }
  
  // Normals
  if (config.artifacts.normal) {
    buffers.normal = renderNormals(frameState, width, height)
  }
  
  // ID Map
  if (config.artifacts.idMap) {
    buffers.idMap = renderIDMap(frameState, width, height)
  }
  
  return buffers
}
```

---

## 6. DEPTH EXPORT

### 6.1 Depth Normalization

```typescript
function renderDepth(
  frameState: FrameState,
  width: number,
  height: number,
  depthRange: [number, number]
): Float32Array {
  const [near, far] = depthRange
  const buffer = new Float32Array(width * height)
  
  // Initialize to far plane
  buffer.fill(1.0)
  
  // Render each layer's depth contribution
  for (const layer of frameState.layers) {
    if (!layer.visible) continue
    
    const layerDepth = layer.transform.position.z
    const normalizedDepth = (layerDepth - near) / (far - near)
    const clampedDepth = Math.max(0, Math.min(1, normalizedDepth))
    
    // Apply to layer mask
    const mask = getLayerMask(layer, width, height)
    for (let i = 0; i < buffer.length; i++) {
      if (mask[i] > 0) {
        buffer[i] = Math.min(buffer[i], clampedDepth)
      }
    }
  }
  
  return buffer
}
```

### 6.2 Depth Format

- **EXR** (float32): Full precision, recommended
- **PNG** (uint16): 65,536 levels, acceptable for most use cases

---

## 7. MOTION VECTOR EXPORT

### 7.1 Motion Vector Computation

```typescript
function renderMotionVectors(
  frameState: FrameState,
  width: number,
  height: number,
  scale: number
): Float32Array {
  const buffer = new Float32Array(width * height * 2)  // dx, dy interleaved
  
  for (const layer of frameState.layers) {
    if (!layer.visible) continue
    
    // Compute per-pixel motion from transform animation
    const prevTransform = layer.prevFrameTransform
    const currTransform = layer.transform
    
    if (prevTransform) {
      const dx = (currTransform.position.x - prevTransform.position.x) * scale
      const dy = (currTransform.position.y - prevTransform.position.y) * scale
      
      // Apply to layer bounds
      applyMotionToMask(buffer, layer, width, height, dx, dy)
    }
  }
  
  return buffer
}
```

### 7.2 Motion Format

Motion vectors are stored as:
- **dx**: Horizontal displacement in pixels (scaled)
- **dy**: Vertical displacement in pixels (scaled)
- Format: EXR with 2 channels or NPY array

---

## 8. MASK EXPORT

### 8.1 Mask Types

| Type | Description | Format |
|------|-------------|--------|
| **Binary** | 0 or 255 | PNG uint8 |
| **Soft** | 0-255 (antialiased) | PNG uint8 |
| **Float** | 0.0-1.0 (full precision) | EXR float32 |

### 8.2 Per-Layer Masks

```typescript
function exportLayerMasks(
  frameState: FrameState,
  layerIds: string[],
  config: ExportConfig
): Map<string, ImageBuffer> {
  const masks = new Map<string, ImageBuffer>()
  const { width, height } = config.resolution
  
  for (const layerId of layerIds) {
    const layer = frameState.layers.find(l => l.id === layerId)
    if (!layer) continue
    
    const mask = new Uint8Array(width * height)
    
    // Render layer silhouette
    renderLayerSilhouette(layer, mask, width, height)
    
    // Apply layer opacity
    const opacity = layer.opacity
    for (let i = 0; i < mask.length; i++) {
      mask[i] = Math.round(mask[i] * opacity)
    }
    
    masks.set(layerId, { data: mask, width, height, channels: 1 })
  }
  
  return masks
}
```

---

## 9. CAMERA TRAJECTORY EXPORT

```typescript
interface CameraTrajectoryExport {
  readonly version: string
  readonly frameRate: number
  readonly frameCount: number
  readonly frames: readonly CameraFrame[]
}

interface CameraFrame {
  readonly frame: number
  readonly position: [number, number, number]
  readonly forward: [number, number, number]
  readonly up: [number, number, number]
  readonly fov: number
}

async function exportCameraTrajectory(
  project: WeylProject,
  config: ExportConfig
): Promise<void> {
  const [startFrame, endFrame] = config.frameRange
  const frames: CameraFrame[] = []
  
  for (let frame = startFrame; frame <= endFrame; frame++) {
    const frameState = motionEngine.evaluate(frame, project)
    const camera = frameState.camera
    
    frames.push({
      frame,
      position: [camera.position.x, camera.position.y, camera.position.z],
      forward: [camera.forward.x, camera.forward.y, camera.forward.z],
      up: [camera.up.x, camera.up.y, camera.up.z],
      fov: camera.fov
    })
  }
  
  const trajectory: CameraTrajectoryExport = {
    version: '1.0.0',
    frameRate: project.composition.frameRate,
    frameCount: frames.length,
    frames
  }
  
  await writeFile(
    path.join(config.outputPath, 'camera', 'trajectory.json'),
    JSON.stringify(trajectory, null, 2)
  )
}
```

---

## 10. METADATA EXPORT

```typescript
interface ExportMetadata {
  readonly version: string
  readonly projectId: string
  readonly projectName: string
  readonly exportedAt: string
  
  // Frame info
  readonly frameRange: [number, number]
  readonly frameRate: number
  readonly resolution: { width: number, height: number }
  
  // Artifact info
  readonly artifacts: string[]
  readonly formats: Record<string, string>
  
  // Checksums for verification
  readonly checksums: {
    readonly [artifact: string]: {
      readonly files: string[]
      readonly hashes: string[]
      readonly combined: string  // Hash of all hashes
    }
  }
  
  // ComfyUI compatibility
  readonly comfyui: {
    readonly compatible: boolean
    readonly recommendedNodes: string[]
  }
}
```

---

## 11. COMFYUI COMPATIBILITY

### 11.1 Compatible Models

| Model | Required Artifacts | Notes |
|-------|-------------------|-------|
| **ATI** | RGBA, Audio | Audio-to-Image |
| **Wan** | RGBA, Depth, Motion | Video generation |
| **Uni3C** | Depth, Normal | 3D-aware diffusion |
| **DepthAnything** | RGBA | Depth estimation |
| **NormalCrafter** | RGBA | Normal estimation |
| **ControlNet** | Depth, Canny, Pose | Various conditioning |
| **AnimateDiff** | RGBA, Motion | Video diffusion |

### 11.2 Recommended Workflow

```
Weyl Export
       ↓
ComfyUI Load Image Sequence
       ↓
ControlNet / IP-Adapter / Regional Prompting
       ↓
Diffusion Model (SD, SDXL, Wan, etc.)
       ↓
Final Output
```

---

## 12. DETERMINISM VERIFICATION

### 12.1 Checksum Generation

```typescript
async function generateFrameChecksum(
  buffer: ArrayBuffer | Uint8Array | Float32Array
): Promise<string> {
  const data = buffer instanceof ArrayBuffer 
    ? new Uint8Array(buffer) 
    : buffer
  
  const hashBuffer = await crypto.subtle.digest('SHA-256', data)
  const hashArray = new Uint8Array(hashBuffer)
  return Array.from(hashArray)
    .map(b => b.toString(16).padStart(2, '0'))
    .join('')
}
```

### 12.2 Export Verification

```typescript
async function verifyExport(
  metadata: ExportMetadata,
  exportPath: string
): Promise<boolean> {
  for (const [artifact, info] of Object.entries(metadata.checksums)) {
    for (let i = 0; i < info.files.length; i++) {
      const filePath = path.join(exportPath, artifact, info.files[i])
      const fileBuffer = await readFile(filePath)
      const hash = await generateFrameChecksum(fileBuffer)
      
      if (hash !== info.hashes[i]) {
        console.error(`Checksum mismatch: ${artifact}/${info.files[i]}`)
        return false
      }
    }
  }
  
  return true
}
```

---

## 13. TESTING REQUIREMENTS

```typescript
describe('Export Pipeline', () => {
  it('produces identical output for same project', async () => {
    const config = createExportConfig()
    
    const result1 = await exportProject(project, config)
    const result2 = await exportProject(project, config)
    
    expect(result1.metadata.checksums).toEqual(result2.metadata.checksums)
  })

  it('exports all requested artifacts', async () => {
    const config = {
      ...defaultConfig,
      artifacts: {
        rgba: true,
        depth: true,
        motion: true,
        mask: true,
        normal: true,
        idMap: true,
        camera: true,
        audio: true
      }
    }
    
    const result = await exportProject(project, config)
    
    expect(await fileExists('rgba/frame_000001.exr')).toBe(true)
    expect(await fileExists('depth/frame_000001.exr')).toBe(true)
    expect(await fileExists('motion/frame_000001.exr')).toBe(true)
    expect(await fileExists('camera/trajectory.json')).toBe(true)
  })

  it('generates valid checksums', async () => {
    const result = await exportProject(project, config)
    
    const verified = await verifyExport(result.metadata, config.outputPath)
    expect(verified).toBe(true)
  })

  it('respects frame range', async () => {
    const config = {
      ...defaultConfig,
      frameRange: [10, 20] as [number, number]
    }
    
    await exportProject(project, config)
    
    expect(await fileExists('rgba/frame_000010.exr')).toBe(true)
    expect(await fileExists('rgba/frame_000020.exr')).toBe(true)
    expect(await fileExists('rgba/frame_000009.exr')).toBe(false)
    expect(await fileExists('rgba/frame_000021.exr')).toBe(false)
  })
})
```

---

## 14. AUDIT CHECKLIST

Claude Code must verify:

- [ ] All exports go through MotionEngine.evaluate()
- [ ] Frame numbers use consistent padding (6 digits)
- [ ] Depth is normalized to [0,1] range
- [ ] Motion vectors are properly scaled
- [ ] Per-layer masks are exported correctly
- [ ] Camera trajectory includes all frames
- [ ] Checksums are generated for all artifacts
- [ ] Metadata includes ComfyUI compatibility info
- [ ] Export is deterministic (same inputs = same outputs)
- [ ] File formats match configuration

**Any export that bypasses MotionEngine is a violation.**

---

**Previous**: [12_COMPOSITION_IMPORT.md](./12_COMPOSITION_IMPORT.md)  
**Next**: [14_VISION_AUTHORING.md](./14_VISION_AUTHORING.md)
