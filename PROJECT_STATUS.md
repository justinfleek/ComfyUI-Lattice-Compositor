# Project Status Audit

**Last Updated:** December 22, 2025
**Test Status:** 1615 tests passing (9 skipped), 0 TypeScript errors
**Build Status:** Compiles successfully (12.97s)

---

## Quick Summary

| Metric | Count | Status |
|--------|-------|--------|
| Lines of Code | 165,000+ | TypeScript + Vue |
| TypeScript Files | 270+ | All compiling |
| Vue Components | 63+ | All rendering |
| Services | 65+ | All exported |
| Engine Files | 24 | Functional |
| Test Suites | 43 | All passing |
| Total Tests | 1615+ | 99.4% pass rate |
| Layer Types | 17 | All implemented |
| Effects | 22 | 4 categories |
| Easing Functions | 35 | All Penner + custom |
| Camera Presets | 22 | Trajectory presets |
| Particle Presets | 24 | Built-in |
| AI Services | 4 | Camera tracking, Sapiens, Depth, Agent |

## Known Issues (December 2025)

| Issue | Status |
|-------|--------|
| ScrubableNumber drag inputs | **FIXED** |
| Project panel drag to timeline | **FIXED** |
| Upper-left viewport controls | **FIXED** |
| Three.js multi-instance conflict | MITIGATED |

See `HANDOFF.md` for detailed issue descriptions and workarounds.

## Core Infrastructure (December 22, 2025)

Professional-grade infrastructure implemented:

| Phase | Feature | File(s) | Status |
|-------|---------|---------|--------|
| 1 | GPU Effects Pipeline | `gpuEffectDispatcher.ts`, `gpuBenchmark.ts` | **COMPLETE** |
| 2 | Text System (OpenType) | `textShaper.ts` | **COMPLETE** |
| 3 | Shape Booleans (Bezier) | `bezierBoolean.ts` | **COMPLETE** |
| 4 | Video Frame Accuracy | `videoDecoder.ts` + VideoLayer | **COMPLETE** |
| 5 | Render Queue | `renderQueue/RenderQueueManager.ts` | **COMPLETE** |
| 6 | Color Management | `colorManagement/ColorProfileService.ts` | **COMPLETE** |
| 7 | Audio Waveform | `timelineWaveform.ts` | **COMPLETE** |
| 8 | Canvas Selection | `composables/useCanvasSelection.ts` | **COMPLETE** |
| 9 | Plugin API | `plugins/PluginManager.ts` | **COMPLETE** |
| 10 | Project Versioning | `projectMigration.ts` | **COMPLETE** |

## Earlier Features (December 22, 2025)

| Feature | Status |
|---------|--------|
| Camera Tracking Import (COLMAP, Blender, Uni3C) | **COMPLETE** |
| AI Camera Motion Analysis (VLM) | **COMPLETE** |
| Sapiens Integration (human depth/pose) | **COMPLETE** |
| Shadow Catcher Material | **COMPLETE** |
| Track Point Visualization | **COMPLETE** |
| UI Overhaul (dark purple theme) | **COMPLETE** |

## Tutorial Compatibility

| Tutorial | Compatibility |
|----------|---------------|
| Tutorial 1 (AE in 10 Minutes) | 89% |
| Tutorial 10 (3D Camera Tracker) | **55%** (up from 15%) |
| Tutorial 11 (CC Particle World) | **100%** |

---

## 1. Core Architecture

### State Management (`compositorStore.ts`)
| Feature | Status | Notes |
|---------|--------|-------|
| Undo/Redo | YES | `historyStack`, `historyIndex`, 50 entry limit |
| Separated Dimensions | PARTIAL | GraphEditor extracts X/Y for display |
| Clipboard | NO | Copy/paste not implemented |
| Snapping | NO | No snap to keyframe/grid |
| Rulers/Guides | NO | Not implemented |
| Layer Grouping | NO | No pre-compose |
| Expression System | YES | **NEW** - `expressions.ts` service added |

### Timeline Architecture (`TimelinePanel.vue`)
| Feature | Status | Notes |
|---------|--------|-------|
| Split-pane Layout | YES | Sidebar (left) + Track (right) |
| pixelsPerFrame System | YES | **NEW** - Replaced percentage-based |
| Scroll Sync | PARTIAL | Track → Ruler syncs, sidebar independent |
| Playhead | YES | Single playhead spans both areas |

---

## 2. Feature Completion Matrix

### Layer Types (17 Total)

| Type | Store | Render | Properties | Completion |
|------|-------|--------|------------|------------|
| image | YES | YES | YES | 100% |
| solid | YES | YES | YES | 100% |
| null | YES | YES | YES | 100% |
| text | YES | YES | YES | 95% |
| spline | YES | YES | YES | 95% |
| camera | YES | YES | YES | 95% |
| video | YES | YES | YES | 90% |
| particle | YES | YES | YES | 90% |
| precomp | YES | YES | YES | 90% |
| light | YES | YES | YES | 90% |
| model | YES | YES | YES | 90% |
| adjustment | YES | YES | PARTIAL | 85% |
| procedural_matte | YES | YES | PARTIAL | 85% |
| point_cloud | YES | YES | YES | 85% |
| shape | YES | YES | YES | 80% |
| depthflow | YES | PARTIAL | YES | 70% |

### Engine Components

| Component | File | Status | Notes |
|-----------|------|--------|-------|
| WeylEngine | WeylEngine.ts | YES | Main facade |
| MotionEngine | MotionEngine.ts | YES | **AUTHORITATIVE** - Pure frame evaluation |
| LayerManager | LayerManager.ts | YES | Layer CRUD |
| CameraController | CameraController.ts | YES | 3D camera with DOF |
| RenderPipeline | RenderPipeline.ts | YES | Post-processing |
| SceneManager | SceneManager.ts | YES | Three.js scene |
| ResourceManager | ResourceManager.ts | YES | Asset management |
| ParticleSimController | ParticleSimulationController.ts | PARTIAL | Determinism issues |

### Services (32 total)

| Service | Status | Notes |
|---------|--------|-------|
| interpolation.ts | COMPLETE | Pure keyframe interpolation |
| easing.ts | COMPLETE | 30+ Penner easing functions |
| expressions.ts | **NEW** | Expression evaluation system |
| math3d.ts | COMPLETE | Vec3, Mat4, Quaternion |
| arcLength.ts | COMPLETE | LUT-based arc length |
| textOnPath.ts | COMPLETE | Text on bezier paths |
| particleSystem.ts | PARTIAL | **ISSUE**: Math.random() in spawning |
| audioFeatures.ts | COMPLETE | Web Worker FFT analysis |
| audioReactiveMapping.ts | COMPLETE | ATI/Yvann mapping |
| effectProcessor.ts | COMPLETE | Effect stack evaluation |
| motionBlur.ts | COMPLETE | Multi-type motion blur |
| frameCache.ts | COMPLETE | LRU frame caching |
| gpuDetection.ts | COMPLETE | GPU tier detection |
| camera3DVisualization.ts | COMPLETE | Frustum visualization |
| cameraExport.ts | COMPLETE | 6+ export formats |
| depthflow.ts | COMPLETE | Depth parallax |
| fontService.ts | COMPLETE | Google Fonts integration |
| imageTrace.ts | COMPLETE | SVG tracing |
| matteExporter.ts | COMPLETE | Matte sequence export |
| projectStorage.ts | COMPLETE | Save/load projects |
| propertyDriver.ts | **NEW** | Property linking |
| segmentation.ts | PARTIAL | SAM2 integration |
| shapeOperations.ts | COMPLETE | Boolean operations |
| timelineSnap.ts | COMPLETE | Snap calculations |
| workerPool.ts | COMPLETE | Web Worker management |

---

## 3. Recent Fixes (Dec 2025)

### Session: 2025-12-17

1. **services/index.ts** - Complete rewrite
   - Fixed 100+ export mismatches
   - All service exports now verified against actual modules

2. **compositorStore.ts** - API contract fixes
   - `projectId` → `project_id` (snake_case)
   - `loadProjectFromBackend()` fixed
   - `listSavedProjects()` return type fixed

3. **Browser API Mocks** - `__tests__/setup.ts`
   - MockImageData, MockOffscreenCanvas
   - mockCreateImageBitmap, mockRequestAnimationFrame
   - Test utilities: createTestImageData, createTestCanvas

4. **motionBlur.test.ts** - Fixed test API
   - Changed `angle` → `direction`
   - Changed `centerX/Y` → `radialCenterX/Y`

5. **CLAUDE.md** - Updated to reflect actual architecture
   - Removed Fabric.js references (never implemented)
   - Documented Three.js-based engine
   - Added timeline architecture docs
   - Added common issues & solutions

### Previous Sessions (Dec 2025)

- Expression system implementation
- Motion blur processor
- Shape layer operations
- Camera system with store integration
- Audio worker for non-blocking analysis
- Effect processor with StackBlur algorithm

---

## 4. Critical Bugs (Priority Order)

### P0 - Blocking

| Bug | Location | Status | Notes |
|-----|----------|--------|-------|
| Particle Math.random() | particleSystem.ts | **OPEN** | Breaks determinism |
| Scroll sync incomplete | TimelinePanel.vue | **OPEN** | Sidebar independent |
| Input bleed to track | PropertyTrack.vue | **INVESTIGATING** | layoutMode not respected |

### P1 - Major

| Bug | Location | Status | Notes |
|-----|----------|--------|-------|
| Keyframe drag non-functional | PropertyTrack.vue | **OPEN** | Only selects |
| No delete layer UI | TimelinePanel.vue | **OPEN** | Action exists, no button |
| Graph handle drag broken | GraphEditorCanvas.vue | **OPEN** | Direct mutation |
| Playhead desync | TimelinePanel.vue | **INVESTIGATING** | Separate scroll containers |

### P2 - Minor

| Bug | Location | Status | Notes |
|-----|----------|--------|-------|
| Twirl arrow alignment | EnhancedLayerTrack.vue | **OPEN** | CSS issue |
| Font size too small | Various | **OPEN** | Need 14px/16px |
| Missing Mode/TrkMat columns | TimelinePanel.vue | **OPEN** | AE parity |
| Markers not persisted | TimelinePanel.vue | **OPEN** | Local state only |

---

## 5. Missing Features for Full AE Parity

### Timeline

- [ ] Delete layer button/shortcut
- [ ] Keyframe dragging (time axis)
- [ ] Multi-keyframe selection (box select)
- [ ] Copy/paste keyframes
- [ ] Snap to keyframes
- [ ] Layer reorder drag-drop
- [ ] Context menus (right-click)
- [ ] Mode column (blend modes)
- [ ] Track Matte column
- [ ] Timecode display (HH:MM:SS:FF)

### Graph Editor

- [ ] Handle dragging updates store
- [ ] Value typing in graph
- [ ] Ease presets (Easy Ease In/Out)
- [ ] Box selection
- [ ] Copy/paste curves

### Properties Panel

- [ ] Per-effect controls
- [ ] Text animators
- [ ] Shape operation stack
- [ ] Expression editor

### Canvas/Viewport

- [ ] Select tool click handler
- [ ] Text tool click handler
- [ ] Transform handles (move/rotate/scale)
- [ ] Selection highlighting
- [ ] Multi-select

### Export

- [ ] SCAIL-Pose integration
- [ ] Batch export
- [ ] Export history

---

## 6. Architecture Compliance

### MotionEngine (AUTHORITATIVE)

The `MotionEngine.evaluate(frame, project)` function is the **single source of truth** for frame state. All rendering should flow through:

```typescript
const frameState = motionEngine.evaluate(frame, project, audioAnalysis);
engine.applyFrameState(frameState);
```

**DEPRECATED PATH** (still exists, needs removal):
```typescript
engine.setFrame(frame); // Bypasses MotionEngine
```

### Determinism Requirements

Per `docs/15_DETERMINISM_TESTING.md`:
- [ ] `evaluate(50)` === `evaluate(50)` always
- [ ] No Math.random() in render path
- [ ] No Date.now() in render path
- [ ] Seeded PRNG for particles

**Current Violations:**
- `particleSystem.ts:1196,1212,1219-1220` - Math.random() in spawning
- ID generation uses Math.random() (acceptable for IDs only)

---

## 7. Test Coverage

| Category | Suites | Tests | Status |
|----------|--------|-------|--------|
| Stores | 4 | ~60 | All passing |
| Engine | 4 | ~65 | All passing |
| Services | 11 | ~726 | All passing |
| **Total** | **19** | **851** | **100%** |

### Test Gaps

- [ ] MotionEngine determinism tests
- [ ] Particle scrub-order independence
- [ ] Effect application verification
- [ ] Timeline interaction tests
- [ ] Export pipeline integration

---

## 8. File Counts

```
ui/src/
├── components/     45 .vue files
├── engine/         24 .ts files
├── services/       32 .ts files
├── stores/          6 .ts files
├── types/           6 .ts files
├── __tests__/      19 test files
└── Total:         170 source files
```

---

## 9. Estimated Work Remaining

| Phase | Description | Sessions | Priority |
|-------|-------------|----------|----------|
| **P0 Fixes** | Particle determinism, scroll sync | 2-3 | IMMEDIATE |
| **Timeline UX** | Keyframe drag, delete UI, context menus | 3-4 | HIGH |
| **Graph Editor** | Handle drag, value editing | 2 | HIGH |
| **Canvas Tools** | Select/text handlers, transform handles | 3-4 | MEDIUM |
| **AE Parity** | Mode/TrkMat columns, timecode | 2 | MEDIUM |
| **Testing** | Determinism suite, integration tests | 3 | FINAL |
| **Total** | | **15-18** | |

---

## 10. Quality Gates

Before Phase 1 Release:

- [x] TypeScript strict mode compiles (0 errors)
- [x] All tests pass (851/851)
- [x] Build succeeds
- [ ] Particle determinism fixed
- [ ] Timeline scroll sync working
- [ ] Keyframe dragging functional
- [ ] Delete layer UI exists
- [ ] Determinism tests pass

---

**End of Status Document**
