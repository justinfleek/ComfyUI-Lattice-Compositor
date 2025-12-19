# WEYL COMPOSITOR — COMPOSITION & IMPORT

**Document ID**: 12_COMPOSITION_IMPORT  
**Version**: 1.0.0  
**Status**: CANONICAL  
**Depends On**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md)

> Compositions are deterministic containers with explicit settings.
> Import creates assets with verifiable hashes.

---

## 1. COMPOSITION DEFINITION

```typescript
interface Composition {
  readonly id: string
  readonly name: string
  readonly width: number
  readonly height: number
  readonly frameRate: number
  readonly frameCount: number
  readonly startFrame: number  // Always 0
  readonly backgroundColor: Color
  readonly layers: readonly Layer[]
  readonly activeCameraId?: string
}
```

---

## 2. DEFAULT COMPOSITION SETTINGS

### 2.1 Image-Based Composition (Image → Video)

When the first imported asset is a **single image**:

```typescript
const imageCompositionDefaults = {
  frameRate: 16,        // WAN / AnimateDiff standard
  frameCount: 81,       // ~5 seconds at 16fps
  width: image.width,   // Match source
  height: image.height, // Match source
  startFrame: 0
}
```

### 2.2 Video-Based Composition (Video → Video)

When the first imported asset is a **video**:

```typescript
const videoCompositionDefaults = {
  frameRate: video.frameRate,    // Source FPS
  frameCount: video.frameCount,  // Exact frame count
  width: video.width,            // Match source
  height: video.height,          // Match source
  startFrame: 0
}
```

**Rule**: Composition duration must **exactly** match the video length. No padding, trimming, or looping.

### 2.3 Standard Presets

```typescript
const COMPOSITION_PRESETS = {
  // WAN / AnimateDiff
  wan_16fps: { frameRate: 16, frameCount: 81 },
  
  // Longer WAN
  wan_16fps_long: { frameRate: 16, frameCount: 161 },
  
  // Standard video
  video_24fps: { frameRate: 24, frameCount: 240 },
  video_30fps: { frameRate: 30, frameCount: 300 },
  
  // High frame rate
  video_60fps: { frameRate: 60, frameCount: 600 }
}
```

---

## 3. PROJECT STRUCTURE

```typescript
interface WeylProject {
  readonly id: string
  readonly name: string
  readonly version: string
  readonly createdAt: string
  readonly modifiedAt: string
  
  // Compositions
  readonly mainCompositionId: string
  readonly compositions: readonly Composition[]
  
  // Assets
  readonly assets: readonly Asset[]
  
  // Audio
  readonly audioAssetId?: string
  readonly audioAnalysis?: AudioAnalysis
  
  // Settings
  readonly settings: ProjectSettings
}

interface ProjectSettings {
  readonly exportPath: string
  readonly framePadding: number  // e.g., 6 for 000001
  readonly exportFormats: ExportFormatConfig
}
```

---

## 4. ASSET SYSTEM

### 4.1 Base Asset Interface

```typescript
interface Asset {
  readonly id: string
  readonly name: string
  readonly type: AssetType
  readonly sourcePath: string
  readonly hash: string  // SHA-256 of source file
  readonly importedAt: string
}

type AssetType = 'image' | 'video' | 'audio' | 'font' | 'svg' | 'lottie'
```

### 4.2 Image Asset

```typescript
interface ImageAsset extends Asset {
  readonly type: 'image'
  readonly width: number
  readonly height: number
  readonly format: 'png' | 'jpg' | 'webp' | 'exr' | 'tiff'
  readonly hasAlpha: boolean
  readonly colorSpace: 'srgb' | 'linear' | 'display-p3'
}
```

### 4.3 Video Asset

```typescript
interface VideoAsset extends Asset {
  readonly type: 'video'
  readonly width: number
  readonly height: number
  readonly frameRate: number
  readonly frameCount: number
  readonly duration: number  // Seconds
  readonly codec: string
  readonly hasAudio: boolean
}
```

### 4.4 Audio Asset

```typescript
interface AudioAsset extends Asset {
  readonly type: 'audio'
  readonly sampleRate: number
  readonly channels: number
  readonly duration: number  // Seconds
  readonly format: 'wav' | 'mp3' | 'aac' | 'flac'
  
  // Pre-computed visualization
  readonly waveform?: Float32Array
  readonly peaks?: Float32Array
}
```

### 4.5 Font Asset

```typescript
interface FontAsset extends Asset {
  readonly type: 'font'
  readonly family: string
  readonly style: string        // 'normal', 'italic'
  readonly weight: number       // 100-900
  readonly format: 'ttf' | 'otf' | 'woff' | 'woff2'
  readonly variationAxes?: Readonly<Record<string, VariationAxis>>
}

interface VariationAxis {
  readonly name: string
  readonly min: number
  readonly max: number
  readonly default: number
}
```

---

## 5. IMPORT PIPELINE

### 5.1 Import Flow

```
File Selected
       ↓
Compute SHA-256 Hash
       ↓
Check for Duplicate (by hash)
       ↓
Extract Metadata
       ↓
Create Asset Entry
       ↓
[If Audio] Trigger Analysis
       ↓
Add to Project
```

### 5.2 Import Implementation

```typescript
async function importAsset(
  filePath: string,
  project: WeylProject
): Promise<Asset> {
  // 1. Read file and compute hash
  const fileBuffer = await readFile(filePath)
  const hash = await computeSHA256(fileBuffer)
  
  // 2. Check for duplicate
  const existing = project.assets.find(a => a.hash === hash)
  if (existing) {
    console.log(`Asset already imported: ${existing.name}`)
    return existing
  }
  
  // 3. Detect type and extract metadata
  const type = detectAssetType(filePath)
  const metadata = await extractMetadata(filePath, type)
  
  // 4. Create asset
  const asset: Asset = {
    id: generateId(),
    name: getFileName(filePath),
    type,
    sourcePath: filePath,
    hash,
    importedAt: new Date().toISOString(),
    ...metadata
  }
  
  // 5. Trigger audio analysis if needed
  if (type === 'audio') {
    scheduleAudioAnalysis(asset as AudioAsset, project)
  }
  
  return Object.freeze(asset)
}
```

### 5.3 Hash Verification

```typescript
async function verifyAssetIntegrity(asset: Asset): Promise<boolean> {
  try {
    const fileBuffer = await readFile(asset.sourcePath)
    const currentHash = await computeSHA256(fileBuffer)
    
    if (currentHash !== asset.hash) {
      console.error(`Asset integrity check failed: ${asset.name}`)
      console.error(`Expected: ${asset.hash}`)
      console.error(`Got: ${currentHash}`)
      return false
    }
    
    return true
  } catch (error) {
    console.error(`Cannot verify asset: ${asset.name}`, error)
    return false
  }
}
```

---

## 6. VIDEO FRAME EXTRACTION

### 6.1 Frame Access

```typescript
interface VideoFrameCache {
  getFrame(assetId: string, frame: number): Promise<ImageData>
  preloadRange(assetId: string, startFrame: number, endFrame: number): void
  clearCache(): void
}
```

### 6.2 Implementation

```typescript
class VideoFrameCacheImpl implements VideoFrameCache {
  private cache = new Map<string, ImageData>()
  private maxCacheSize = 100  // Frames
  
  async getFrame(assetId: string, frame: number): Promise<ImageData> {
    const key = `${assetId}:${frame}`
    
    if (this.cache.has(key)) {
      return this.cache.get(key)!
    }
    
    // Extract frame using FFmpeg or similar
    const imageData = await extractVideoFrame(assetId, frame)
    
    // Cache with LRU eviction
    if (this.cache.size >= this.maxCacheSize) {
      const firstKey = this.cache.keys().next().value
      this.cache.delete(firstKey)
    }
    
    this.cache.set(key, imageData)
    return imageData
  }
}
```

---

## 7. SVG AND LOTTIE IMPORT

### 7.1 SVG Import

```typescript
interface SVGAsset extends Asset {
  readonly type: 'svg'
  readonly viewBox: { x: number, y: number, width: number, height: number }
  readonly paths: readonly BezierPath[]  // Extracted at import
}

async function importSVG(filePath: string): Promise<SVGAsset> {
  const svgContent = await readFile(filePath, 'utf-8')
  const parsed = parseSVG(svgContent)
  
  return {
    id: generateId(),
    name: getFileName(filePath),
    type: 'svg',
    sourcePath: filePath,
    hash: await computeSHA256(svgContent),
    importedAt: new Date().toISOString(),
    viewBox: parsed.viewBox,
    paths: extractPaths(parsed)  // Convert to Bezier paths
  }
}
```

### 7.2 Lottie Import

```typescript
interface LottieAsset extends Asset {
  readonly type: 'lottie'
  readonly width: number
  readonly height: number
  readonly frameRate: number
  readonly frameCount: number
  readonly duration: number
}

// Lottie is evaluated per-frame like a precomp
// Each frame extracts shapes as Bezier paths
```

---

## 8. PROJECT FILE FORMAT

### 8.1 File Structure

```
project.weyl (JSON)
├── id
├── name
├── version
├── compositions[]
├── assets[] (metadata only, not file contents)
├── settings
└── audioAnalysis (optional, embedded)

assets/ (folder)
├── image_abc123.png
├── video_def456.mp4
├── font_ghi789.ttf
└── audio_jkl012.wav
```

### 8.2 Portable Project Export

```typescript
async function exportPortableProject(
  project: WeylProject,
  outputPath: string
): Promise<void> {
  // 1. Create output directory
  const assetsDir = path.join(outputPath, 'assets')
  await mkdir(assetsDir, { recursive: true })
  
  // 2. Copy all assets
  for (const asset of project.assets) {
    const destPath = path.join(assetsDir, `${asset.id}${getExtension(asset)}`)
    await copyFile(asset.sourcePath, destPath)
  }
  
  // 3. Update asset paths in project
  const portableProject = {
    ...project,
    assets: project.assets.map(a => ({
      ...a,
      sourcePath: `./assets/${a.id}${getExtension(a)}`
    }))
  }
  
  // 4. Save project file
  await writeFile(
    path.join(outputPath, 'project.weyl'),
    JSON.stringify(portableProject, null, 2)
  )
}
```

---

## 9. TESTING REQUIREMENTS

```typescript
describe('Import', () => {
  it('computes correct hash', async () => {
    const asset = await importAsset('test.png', project)
    
    // Re-import should find duplicate
    const duplicate = await importAsset('test.png', project)
    expect(duplicate.id).toBe(asset.id)
  })

  it('extracts video metadata', async () => {
    const asset = await importAsset('test.mp4', project) as VideoAsset
    
    expect(asset.frameRate).toBe(30)
    expect(asset.frameCount).toBe(150)
    expect(asset.width).toBe(1920)
    expect(asset.height).toBe(1080)
  })

  it('triggers audio analysis', async () => {
    const spy = vi.spyOn(audioAnalyzer, 'analyze')
    
    await importAsset('test.wav', project)
    
    expect(spy).toHaveBeenCalled()
  })

  it('verifies asset integrity', async () => {
    const asset = await importAsset('test.png', project)
    
    expect(await verifyAssetIntegrity(asset)).toBe(true)
    
    // Modify file
    await modifyFile(asset.sourcePath)
    
    expect(await verifyAssetIntegrity(asset)).toBe(false)
  })
})

describe('Composition', () => {
  it('matches video dimensions', () => {
    const comp = createCompositionFromVideo(videoAsset)
    
    expect(comp.width).toBe(videoAsset.width)
    expect(comp.height).toBe(videoAsset.height)
    expect(comp.frameRate).toBe(videoAsset.frameRate)
    expect(comp.frameCount).toBe(videoAsset.frameCount)
  })

  it('uses image defaults', () => {
    const comp = createCompositionFromImage(imageAsset)
    
    expect(comp.frameRate).toBe(16)
    expect(comp.frameCount).toBe(81)
  })
})
```

---

## 10. AUDIT CHECKLIST

Claude Code must verify:

- [ ] All assets have SHA-256 hashes computed at import
- [ ] Duplicate detection uses hash comparison
- [ ] Video compositions exactly match source frame count
- [ ] Image compositions use correct defaults (16fps, 81 frames)
- [ ] Font assets include hash for verification
- [ ] Video frame extraction is deterministic
- [ ] Project files are valid JSON
- [ ] Asset paths are relative in portable exports
- [ ] Audio analysis is triggered on audio import

**Any asset without a verified hash is a violation.**

---

**Previous**: [11_PRECOMPOSITION.md](./11_PRECOMPOSITION.md)  
**Next**: [13_EXPORT_PIPELINE.md](./13_EXPORT_PIPELINE.md)
