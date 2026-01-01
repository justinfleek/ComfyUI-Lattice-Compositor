# Test Coverage Audit - Complete Analysis

**Date:** 2026-01-01
**Auditor:** Claude Code
**Status:** CRITICAL GAPS - 16% Service Coverage

---

## Executive Summary

| Area | Total Files | Tested | Coverage |
|------|-------------|--------|----------|
| Services | 83 | 13 | **15.7%** |
| Effects | 17 | 2 | **11.8%** |
| Stores | 10 | 3 | **30%** |
| Overall | 110 | 18 | **16.4%** |

**Lines of Code:**
- Total code: 52,836 lines (services) + 15,573 lines (effects) = **68,409 lines**
- Tested code: 8,671 + 1,797 = **10,468 lines (15.3%)**
- Untested code: **57,941 lines (84.7%)**

---

## Test Suite Health

### Current Status

```
Test Files: 7 failed | 18 passed (25 total)
Tests:      46 failed | 1009 passed | 34 skipped (1089 total)
```

### Failed Test Analysis

| Test File | Failures | Root Cause |
|-----------|----------|------------|
| modelExport.adversarial.test.ts | 26 | THREE.js mock issue |
| cameraExportFormats.adversarial.test.ts | 10 | THREE.js mock issue |
| depthRenderer.adversarial.test.ts | 5 | THREE.js mock issue |
| workflowTemplates.adversarial.test.ts | 3 | validateWorkflow crashes |
| allTargets.comprehensive.test.ts | 2 | Missing mocks |

**Common Issue:** THREE.js is mocked as arrow functions instead of classes:
```typescript
// BROKEN
vi.mock('three', () => ({
  Vector3: (x, y, z) => ({ x, y, z }),
}));

// CORRECT
vi.mock('three', () => ({
  Vector3: class {
    constructor(public x = 0, public y = 0, public z = 0) {}
  },
}));
```

---

## Services Coverage Detail

### TESTED (13 files, 8,671 lines)

| Service | Lines | Test File(s) |
|---------|-------|--------------|
| expressionValidator.ts | 600+ | expressionValidator.test.ts |
| frameBlending.ts | 400+ | frameBlending.test.ts |
| alphaToMesh.ts | 500+ | alphaToMesh.test.ts |
| meshWarpDeformation.ts | 800+ | meshWarpDeformation.test.ts |
| motionRecording.ts | 600+ | motionRecording.test.ts |
| speedGraph.ts | 400+ | speedGraph.test.ts |
| comfyui/* | 2000+ | workflowTemplates.adversarial.test.ts |
| export/* | 3000+ | 6 adversarial test files |
| security/* | 500+ | jsonSanitizer.test.ts, urlValidator.test.ts |

### UNTESTED - CRITICAL (>1000 lines)

| Service | Lines | Risk | Description |
|---------|-------|------|-------------|
| particleSystem.ts | 2,009 | **CRITICAL** | GPU particles, physics |
| webgpuRenderer.ts | 1,402 | **CRITICAL** | WebGPU rendering |
| shapeOperations.ts | 1,643 | **CRITICAL** | Boolean ops, path math |
| svgExtrusion.ts | 1,182 | **HIGH** | 3D text extrusion |
| textAnimator.ts | 957 | **HIGH** | Character animation |
| propertyDriver.ts | 823 | **HIGH** | Expression linking |
| preprocessorService.ts | 802 | **HIGH** | Control image generation |
| templateBuilder.ts | 758 | **HIGH** | Template generation |
| pathMorphing.ts | 739 | **HIGH** | Shape interpolation |
| textShaper.ts | 725 | **HIGH** | Text layout |

### UNTESTED - HIGH (500-1000 lines)

| Service | Lines | Description |
|---------|-------|-------------|
| videoDecoder.ts | 650 | Video frame extraction |
| persistenceService.ts | 642 | IndexedDB storage |
| textToVector.ts | 637 | Font → paths |
| spriteSheet.ts | 630 | Sprite generation |
| segmentToMask.ts | 594 | Segmentation masks |
| trackPointService.ts | 556 | Motion tracking |

### UNTESTED - MEDIUM (200-500 lines)

| Service | Lines | Description |
|---------|-------|-------------|
| spriteValidation.ts | 474 | Sprite validation |
| timewarp.ts | 467 | Time remapping |
| textOnPath.ts | 453 | Text along curve |
| timelineWaveform.ts | 449 | Audio waveform |
| vectorLOD.ts | 429 | Level of detail |
| workerPool.ts | 367 | Worker management |
| projectCollection.ts | 358 | Project list |
| rovingKeyframes.ts | 347 | Keyframe interpolation |
| timelineSnap.ts | 317 | Snap to grid |
| textMeasurement.ts | 315 | Font metrics |
| projectMigration.ts | 300 | Schema migration |
| segmentation.ts | 299 | Image segmentation |
| projectStorage.ts | 288 | Project save/load |
| svgExport.ts | 267 | SVG export |

---

## Store Coverage Detail

### TESTED (3 files, 3,235 lines)

| Store | Lines | Coverage Notes |
|-------|-------|----------------|
| compositorStore.ts | 2,542 | Partial - main store |
| selectionStore.ts | 476 | Integration tests |
| playbackStore.ts | 217 | Integration tests |

### UNTESTED (7 files, 2,428 lines)

| Store | Lines | Risk |
|-------|-------|------|
| assetStore.ts | 918 | **HIGH** - asset management |
| audioStore.ts | 711 | **HIGH** - audio sync |
| presetStore.ts | 432 | **MEDIUM** - user presets |
| historyStore.ts | 123 | **HIGH** - undo/redo |
| audioSync.ts | 104 | **MEDIUM** - sync logic |
| toastStore.ts | 88 | **LOW** - notifications |
| themeStore.ts | 52 | **LOW** - UI theme |

---

## Test Organization

### Current Structure

```
src/__tests__/
├── _archived/          # 4 tutorial tests (not running)
│   └── tutorials/
├── integration/        # 2 pipeline tests
├── security/           # 2 security tests
├── services/           # 10 service tests
│   ├── comfyui/        # 1 workflow test
│   ├── export/         # 6 export tests
│   └── security/       # 2 security tests
├── types/              # 2 type tests
└── utils/              # 1 security utility test
```

### Problems with Current Organization

1. **Scattered effect tests** - meshDeformRenderer.test.ts is in services/, freezeFrame.test.ts also in services/
2. **No dedicated effects/ folder** - Despite 17 renderer files
3. **Archived tests not running** - Tutorial tests could be valuable
4. **No store tests folder** - Store tests mixed in integration/

### Recommended Structure

```
src/__tests__/
├── unit/
│   ├── effects/        # All 17 effect renderer tests
│   ├── services/       # Service unit tests
│   ├── stores/         # Store unit tests
│   └── types/          # Type validation tests
├── integration/
│   ├── export/         # Export pipeline tests
│   ├── rendering/      # Render pipeline tests
│   └── workflow/       # ComfyUI workflow tests
├── security/           # Security-focused tests
├── e2e/                # End-to-end browser tests
└── helpers/            # Shared test utilities
```

---

## Critical Untested Paths

### 1. Particle System (2,009 lines)

```
particleSystem.ts → GPU shader compilation
                  → Physics simulation
                  → Collision detection
                  → Memory management
```

**Attack Vectors:**
- particle count = Infinity
- negative particle size
- NaN physics values
- WebGPU context loss

### 2. Shape Operations (1,643 lines)

```
shapeOperations.ts → Boolean operations (union, subtract)
                   → Path offsetting
                   → Curve flattening
                   → Point-in-polygon
```

**Attack Vectors:**
- Self-intersecting paths
- Empty path arrays
- Coincident vertices
- Degenerate curves (length 0)

### 3. WebGPU Renderer (1,402 lines)

```
webgpuRenderer.ts → Device initialization
                  → Pipeline creation
                  → Buffer management
                  → Shader compilation
```

**Attack Vectors:**
- Device loss during render
- Buffer overflow
- Invalid shader code
- Memory exhaustion

### 4. Project Storage (288 + 300 + 358 = 946 lines)

```
projectStorage.ts ←→ IndexedDB
projectMigration.ts ← Schema evolution
projectCollection.ts ← Project listing
```

**Attack Vectors:**
- Corrupted project JSON
- Schema migration failures
- IndexedDB quota exceeded
- Concurrent access

---

## Test Infrastructure Gaps

### Missing Mocks

| Mock Needed | Used By | Current State |
|-------------|---------|---------------|
| THREE.js (proper) | 20+ files | Broken - arrow functions |
| WebGPU | webgpuRenderer | None |
| IndexedDB | persistence, storage | Partial |
| OffscreenCanvas | export pipeline | Partial |
| AudioContext | audioStore, visualizer | None |
| FileReader | asset loading | None |

### Missing Test Utilities

| Utility | Purpose |
|---------|---------|
| createMockProject() | Valid project structure |
| createMockLayer() | Various layer types |
| createMockKeyframes() | Animation data |
| createMockCanvas() | Standard test canvas |
| assertValidJSON() | Export output validation |
| measureMemory() | Memory leak detection |

---

## Recommended Test Priorities

### Week 1: Fix Infrastructure

1. Fix THREE.js mocks (unblocks 46 tests)
2. Create shared test utilities
3. Add IndexedDB mock

### Week 2: Critical Services

4. particleSystem.ts tests
5. shapeOperations.ts tests
6. effectProcessor.ts tests

### Week 3: Stores

7. historyStore.ts (undo/redo)
8. assetStore.ts (asset management)
9. audioStore.ts (audio sync)

### Week 4: Effect Renderers

10. colorRenderer.ts (22 exports, 1,643 lines)
11. blurRenderer.ts (9 exports, 1,295 lines)
12. distortRenderer.ts (6 exports, 1,180 lines)

---

## Coverage Targets

| Week | Service Coverage | Store Coverage | Effect Coverage |
|------|------------------|----------------|-----------------|
| Current | 15.7% | 30% | 11.8% |
| Week 1 | 20% | 30% | 15% |
| Week 2 | 35% | 40% | 30% |
| Week 3 | 45% | 70% | 40% |
| Week 4 | 55% | 80% | 60% |
| Month 2 | 80% | 90% | 80% |

---

*Last Updated: 2026-01-01*
