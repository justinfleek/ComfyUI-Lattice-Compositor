# FPS ARCHITECTURE - Complete Audit

**Generated:** 2025-12-25
**Files Audited:** 143 files with fps-related code
**Status:** AUDIT COMPLETE - Ready for coordinated fixes

---

## EXECUTIVE SUMMARY

### Key Findings

1. **System Default FPS: 16** (for WAN AI models with 4n+1 frame pattern)
2. **Inconsistent Fallback Defaults:** Various files use 16, 24, 30, or 60 as fallbacks
3. **Video Import Does NOT Set Composition FPS:** Videos import using composition fps, dropping frames
4. **143 files** contain fps-related code across stores, engine, services, and components

### Critical Issues

| Priority | Issue | Impact |
|----------|-------|--------|
| **CRITICAL** | Video import uses comp fps (16) instead of video fps (24/30) | Drops 40-50% of video frames |
| **HIGH** | Inconsistent default fps across files (16/24/30/60) | Animation timing bugs |
| **HIGH** | Sprite animation hardcoded to 60fps base | Sprite desync at other fps |
| **MEDIUM** | Echo effect time assumes 30fps | Wrong echo timing |
| **MEDIUM** | Motion blur presets fps-specific but not enforced | Wrong blur intensity |

---

## FPS DATA FLOW DIAGRAM

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           FPS DATA FLOW                                      │
└─────────────────────────────────────────────────────────────────────────────┘

SOURCES (where fps is SET):
┌────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─────────────────────┐    ┌─────────────────────┐    ┌────────────────┐ │
│  │ New Composition     │    │ Video Import        │    │ Export Preset  │ │
│  │ DEFAULT: 16 fps     │    │ SHOULD SET: video   │    │ TARGET-BASED   │ │
│  │ (types/project.ts)  │    │ CURRENT: uses comp  │    │ (exportPresets)│ │
│  └─────────┬───────────┘    └─────────┬───────────┘    └───────┬────────┘ │
│            │                          │ BUG!                    │          │
│            ▼                          ▼                         ▼          │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │              composition.settings.fps                                │  │
│  │              (Single Source of Truth for Runtime)                    │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
└────────────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
DISTRIBUTION (how fps FLOWS):
┌────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  compositorStore.fps getter                                                 │
│            │                                                                │
│            ├──────────────────────┬────────────────────┬─────────────────┐ │
│            ▼                      ▼                    ▼                 │ │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐      │ │
│  │ MotionEngine    │    │ playbackStore   │    │ audioStore      │      │ │
│  │ evaluate(frame) │    │ play(fps,...)   │    │ loadAudio(fps)  │      │ │
│  └────────┬────────┘    └────────┬────────┘    └────────┬────────┘      │ │
│           │                      │                      │                │ │
│           ▼                      ▼                      ▼                │ │
│  ┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐      │ │
│  │ interpolate     │    │ frameDuration   │    │ samplesPerFrame │      │ │
│  │ Property(fps)   │    │ = 1000/fps      │    │ = sampleRate/fps│      │ │
│  └────────┬────────┘    └─────────────────┘    └─────────────────┘      │ │
│           │                                                              │ │
│           ▼                                                              │ │
│  ┌─────────────────────────────────────────────────────────────────┐    │ │
│  │                    LayerManager                                  │    │ │
│  │                 setCompositionFPS(fps)                          │    │ │
│  └────────┬───────────────┬───────────────┬───────────────┬────────┘    │ │
│           │               │               │               │             │ │
│           ▼               ▼               ▼               ▼             │ │
│  ┌──────────────┐ ┌──────────────┐ ┌──────────────┐ ┌──────────────┐   │ │
│  │ VideoLayer   │ │ ParticleLayer│ │ ModelLayer   │ │NestedCompLyr │   │ │
│  │setFPS(fps)   │ │setFPS(fps)   │ │compositionFps│ │setFPS(fps)   │   │ │
│  │DEFAULT: 30   │ │DEFAULT: 60   │ │DEFAULT: 30   │ │DEFAULT: 30   │   │ │
│  └──────────────┘ └──────────────┘ └──────────────┘ └──────────────┘   │ │
│                                                                         │ │
└─────────────────────────────────────────────────────────────────────────┘

CONSUMERS (where fps is USED):
┌────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │ Time Calculations                                                    │  │
│  │   time = frame / fps                                                 │  │
│  │   frame = time * fps                                                 │  │
│  │   duration = frameCount / fps                                        │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │ Animation Timing                                                     │  │
│  │   deltaTime = 1 / fps                                                │  │
│  │   velocity = (v2 - v1) / (2 * deltaTime) * fps                       │  │
│  │   samplesPerFrame = sampleRate / fps                                 │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │ Export                                                               │  │
│  │   frameRate in video encoder                                         │  │
│  │   timestamp = (frameIndex * 1_000_000) / fps                         │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
└────────────────────────────────────────────────────────────────────────────┘
```

---

## DEFAULT FPS VALUES BY LOCATION

### Composition/Project Defaults

| File | Line | Default | Context |
|------|------|---------|---------|
| `types/project.ts` | 1972 | **16** | `createEmptyProject()` |
| `compositionActions.ts` | 63 | **16** | `createComposition()` |

### Layer Class Defaults

| Layer | File | Line | Default | Issue |
|-------|------|------|---------|-------|
| BaseLayer | `BaseLayer.ts` | 94 | **30** | Inconsistent with project default |
| VideoLayer | `VideoLayer.ts` | 78 | **30** | Inconsistent |
| ParticleLayer | `ParticleLayer.ts` | 44 | **60** | Very inconsistent |
| NestedCompLayer | `NestedCompLayer.ts` | 69 | **30** | Inconsistent |
| ModelLayer | Uses BaseLayer | - | **30** | Inconsistent |

### Function Parameter Defaults

| Function | File | Line | Default | Issue |
|----------|------|------|---------|-------|
| `interpolateProperty()` | `interpolation.ts` | 207 | **30** | Inconsistent |
| `processEffectStack()` | `effectProcessor.ts` | 407 | **30** | Inconsistent |
| `simulateToFrame()` | `GPUParticleSystem.ts` | 1376 | **30** | Inconsistent |
| `createSpeedRampPreset()` | `timewarp.ts` | 276 | **30** | Inconsistent |
| `inertia()/bounce()/elastic()` | `motionExpressions.ts` | 43,90,151 | **30** | Inconsistent |

### Store Action Defaults

| Action | File | Line | Default | Issue |
|--------|------|------|---------|-------|
| `freezeFrameAtPlayhead()` | `layerActions.ts` | 1447 | **30** | Inconsistent |
| `splitLayerAtPlayhead()` | `layerActions.ts` | 1539 | **30** | Inconsistent |
| `applyKeyframeVelocity()` | `keyframeActions.ts` | 1329 | **30** | Inconsistent |

### Export Preset Defaults

| Preset Category | FPS | Count |
|-----------------|-----|-------|
| WAN models | **16** | 8 presets |
| MotionCtrl | **24** | 2 presets |
| AnimateDiff | **8** | 1 preset |
| Standard video | **24-30** | Variable |

---

## CRITICAL BUG: VIDEO IMPORT FPS

### Current Behavior (WRONG)

**File:** `videoActions.ts` lines 89-107

```typescript
// Line 91 - Uses COMPOSITION fps, not VIDEO fps
calculateCompositionFromVideo(metadata, store.project.composition.fps)

// Line 137 - Video frame count calculated with COMPOSITION fps
const videoFrameCount = Math.ceil(metadata.duration * store.project.composition.fps);
```

**Result:**
- 30fps video (5 seconds = 150 frames) imported to 16fps comp
- Frame count becomes: `5 * 16 = 80 frames`
- **47% of video frames are DROPPED**

### Expected Behavior

```
Import 30fps video
    ↓
SET composition.fps = 30 (from video)
    ↓
SET composition.frameCount = 150 (from video)
    ↓
ALL video frames shown on timeline 1:1
```

### Files to Fix

1. `videoActions.ts` - `createVideoLayer()` and `calculateCompositionFromVideo()`
2. `VideoLayer.ts` - `extractVideoMetadata()` hardcoded 30fps estimate

---

## HARDCODED FPS VALUES

### Critical (Breaks Functionality)

| File | Line | Value | Impact |
|------|------|-------|--------|
| `VideoLayer.ts` | 959-960 | `fps: 30` | Video metadata always assumes 30fps |
| `particleSystem.ts` | 603,609,615 | `/60` | Sprite animation assumes 60fps base |
| `timeRenderer.ts` | 211 | `-0.033` | Echo time assumes 30fps (1/30=0.033) |

### Medium (Timing Issues)

| File | Line | Value | Context |
|------|------|-------|---------|
| `interpolation.ts` | 294 | `81 / fps` | Assumes 81-frame comp duration |
| `motionBlur.ts` | 540 | `24 / fps` | Film standard ratio |
| `ParticleSimulationController.ts` | 161 | `30` frames | Checkpoint interval |

### Export Presets (Intentional)

| File | Lines | Values | Notes |
|------|-------|--------|-------|
| `exportPresets.ts` | 19-319 | 8,16,24 | Target-specific, intentional |
| `wanMoveExport.ts` | 314,699,768,834,1077,1231 | 16 | WAN model standard |

---

## FPS BY SUBSYSTEM

### 1. Timeline/Playback

**Source:** `playbackStore.ts`
```typescript
// Line 90
const frameDuration = 1000 / fps;  // milliseconds per frame
```

**Frame advancement:** `elapsed / frameDuration = frames to advance`

### 2. Audio Analysis

**Source:** `audioFeatures.ts`, `audioWorker.ts`
```typescript
const samplesPerFrame = Math.floor(sampleRate / fps);
const frameCount = Math.ceil(duration * fps);
```

All audio analysis arrays have length = `frameCount`

### 3. Animation/Expressions

**Source:** `interpolation.ts`, `expressionEvaluator.ts`
```typescript
const time = frame / fps;           // frame to seconds
const velocity = delta * fps;        // per-frame to per-second
```

### 4. Video Playback

**Source:** `VideoLayer.ts`
```typescript
// Line 492
let videoTime = (layerFrame / compFps) * effectiveSpeed;
```

Uses composition fps for playback timing, NOT video native fps.

### 5. Particles

**Source:** `GPUParticleSystem.ts`, `particleSystem.ts`
```typescript
// Fixed delta time
fixedDeltaTime: 1 / 60  // Assumes 60fps

// Frame-based simulation
simulateToFrame(targetFrame, fps = 30)
```

### 6. Effects

**Source:** `effectProcessor.ts`, `timeRenderer.ts`
```typescript
// Effect context
params._fps = context?.fps ?? fps ?? 30;

// Posterize time
const frameRatio = fps / targetFps;
```

### 7. Export

**Source:** `exportPipeline.ts`, `videoEncoder.ts`
```typescript
// Validation
fps >= 1 && fps <= 120

// Frame timestamp
timestamp = (frameIndex * 1_000_000) / frameRate;
```

---

## RECOMMENDED FIXES

### Phase 1: Consistency (HIGH Priority)

1. **Standardize all defaults to 16fps** (or make configurable)
   - BaseLayer, VideoLayer, ParticleLayer: Change 30/60 → 16
   - interpolateProperty, effectProcessor: Change 30 → 16
   - Store actions: Change 30 → 16

2. **Remove hardcoded assumptions**
   - VideoLayer.ts:959 - Detect video fps or prompt user
   - particleSystem.ts - Use composition fps for sprite timing
   - timeRenderer.ts:211 - Calculate from fps: `1/fps` not `-0.033`

### Phase 2: Video Import (CRITICAL)

1. **Detect video fps during import** (or use metadata)
2. **Ask user or auto-set composition fps** from first imported video
3. **Preserve all frames** - no dropping

### Phase 3: Architecture Improvements

1. **Add fps to interfaces** that currently lack it
2. **Validate fps** before division (prevent division by zero)
3. **Document fps requirements** for each function
4. **Add fps to MotionBlurSettings** to enforce preset/fps matching

---

## FILE-BY-FILE REFERENCE

### Types & Interfaces

| File | FPS Properties | Notes |
|------|----------------|-------|
| `types/project.ts` | CompositionSettings.fps, AssetReference.fps, NestedCompData.frameRate | Core definitions |

### Stores

| File | FPS Usage | Notes |
|------|-----------|-------|
| `compositorStore.ts` | fps getter, currentTime calculation | Central fps source |
| `playbackStore.ts` | frameDuration calculation | Playback timing |
| `audioStore.ts` | getBeats, loadAudio | Audio sync |

### Store Actions

| File | FPS Functions | Notes |
|------|---------------|-------|
| `compositionActions.ts` | createComposition, updateCompositionSettings | Duration calculations |
| `videoActions.ts` | createVideoLayer, calculateCompositionFromVideo | **BUG: Uses wrong fps** |
| `layerActions.ts` | freezeFrameAtPlayhead, splitLayerAtPlayhead | Timing calculations |
| `keyframeActions.ts` | applyKeyframeVelocity, getKeyframeVelocity | Velocity units |

### Engine

| File | FPS Role | Notes |
|------|----------|-------|
| `MotionEngine.ts` | Retrieves fps, passes to all evaluation | Central distribution |
| `LayerManager.ts` | setCompositionFPS, distributes to layers | Layer fps sync |
| `NestedCompRenderer.ts` | Sets fps for nested compositions | Isolated fps per comp |

### Layer Classes

| File | FPS Property | Default | Notes |
|------|--------------|---------|-------|
| `BaseLayer.ts` | compositionFps | 30 | Parent class |
| `VideoLayer.ts` | compositionFPS | 30 | Video playback |
| `ParticleLayer.ts` | fps | 60 | Particle timing |
| `NestedCompLayer.ts` | parentFPS | 30 | Frame rate conversion |
| `ModelLayer.ts` | (inherited) | 30 | 3D animation |

### Services

| File | FPS Role | Notes |
|------|----------|-------|
| `interpolation.ts` | time/velocity calculations | Expression context |
| `effectProcessor.ts` | Effect context fps | Time-based effects |
| `timewarp.ts` | Speed integration | No fps in core function |
| `motionBlur.ts` | Shutter angle scaling | suggestSettings(fps) |
| `audioFeatures.ts` | samplesPerFrame calculation | Audio frame alignment |

### Components

| File | FPS UI | Notes |
|------|--------|-------|
| `CompositionSettingsDialog.vue` | Dropdown: 8-60 fps | User-configurable |
| `ExportDialog.vue` | Input: 1-120 fps | Export-specific |
| `TimelinePanel.vue` | Display, timecode | Read-only |

---

## VALIDATION CHECKLIST

Before implementing fixes, verify each change against:

- [ ] Does it maintain determinism? (same frame = same result)
- [ ] Does it preserve video frames? (no dropping)
- [ ] Does it respect composition fps as source of truth?
- [ ] Does it use consistent defaults? (16 for new comps)
- [ ] Does it validate fps > 0 before division?
- [ ] Does it update all dependent calculations?

---

## APPENDIX: All Files with FPS References

```
components/canvas/ThreeCanvas.vue
components/curve-editor/CurveEditor*.vue
components/dialogs/CompositionSettingsDialog.vue
components/dialogs/ExportDialog.vue
components/dialogs/KeyframeInterpolationDialog.vue
components/dialogs/KeyframeVelocityDialog.vue
components/dialogs/MotionSketchPanel.vue
components/dialogs/TimeStretchDialog.vue
components/export/ComfyUIExportDialog.vue
components/panels/AudioPanel.vue
components/panels/ExportPanel.vue
components/panels/PreviewPanel.vue
components/panels/RenderQueuePanel.vue
components/preview/HDPreviewWindow.vue
components/properties/*Properties.vue
components/timeline/*.vue
config/exportPresets.ts
engine/core/LayerManager.ts
engine/LatticeEngine.ts
engine/layers/*.ts (all layer classes)
engine/MotionEngine.ts
engine/NestedCompRenderer.ts
engine/particles/*.ts
engine/ParticleSimulationController.ts
services/audio*.ts
services/effectProcessor.ts
services/effects/*.ts
services/export/*.ts
services/expressions/*.ts
services/interpolation.ts
services/motionBlur.ts
services/particles/*.ts
services/particleSystem.ts
services/timewarp.ts
services/timelineWaveform.ts
stores/actions/*.ts
stores/audioStore.ts
stores/compositorStore.ts
stores/playbackStore.ts
types/project.ts
workers/audioWorker.ts
```

**Total: 143 files**

---

*Document generated from comprehensive FPS audit. Ready for coordinated fixes.*
