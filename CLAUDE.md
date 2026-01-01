# CLAUDE.md — Project Instructions

## AUTHORITATIVE DOCUMENTATION

| Document | Purpose |
|----------|---------|
| **docs/PROJECT_PROGRESS.md** | Project status, testing checklists, known bugs |
| **AUDIT/BUGS.md** | Active bug registry |
| **AUDIT/PROGRESS.md** | Detailed code audit progress |
| **INVENTORY.md** | Codebase file inventory |
| **README.md** | Public project documentation |

> **Note:** Old docs (AUDIT_PROGRESS.md, PROJECT_STATUS.md, etc.) have been archived to `_archived/`

---

## CURRENT WORKING STATE (2026-01-01)

**Commit:** Pending - Security audit documentation

### What Works
- ✅ Compositor loads in ComfyUI sidebar
- ✅ Sidebar button appears and opens compositor
- ✅ Layers render in viewport
- ✅ SES expression sandbox (worker-only, main thread disabled for Vue/Three.js compatibility)
- ✅ Camera zoom (setLookAt syncs camera-controls internal state)
- ✅ Pan updates viewportTransform[4,5] for 2D overlays
- ✅ NPY header format (Python dict literal syntax)
- ✅ Lineart preprocessor (Sobel edge detection)
- ✅ **TTM workflow uses real Kijai nodes** (WanVideoAddTTMLatents)
- ✅ **Uni3C workflow uses real Kijai nodes** (WanVideoUni3C_ControlnetLoader, WanVideoUni3C_embeds)
- ✅ **SCAIL workflow implemented** (dual reference+pose structure)
- ✅ **WanMove workflow implemented** (WanVideoAddWanMoveTracks)
- ✅ **ATI workflow implemented** (WanVideoATITracks)
- ✅ **Light-X workflow implemented** (LoRA via WanVideoLoraSelect)

### Known Issues (DO NOT fix without careful testing)
| Issue | Component | Description |
|-------|-----------|-------------|
| MotionPathOverlay indices | MotionPathOverlay.vue:304-305 | Uses [0,1] instead of [4,5] for translate - won't track panning |
| UI layout cramped | WorkspaceLayout | Splitpane sizing issues |
| Solid layer anchor | SolidLayer | Wrong anchor point positioning |

---

## 🔴 SECURITY AUDIT STATUS (2026-01-01)

### CRITICAL FINDING: Effect System NOT Production Ready

| System | Lines | Risk Level | Production Ready |
|--------|-------|------------|------------------|
| **Effect System** | 21,367 | **CRITICAL** | ❌ NO |
| **Export Pipeline** | 5,221 | **MEDIUM** | ⚠️ Beta only |

### Effect System Issues (8 Critical)
1. **Memory Leak:** `processEffectStack()` creates canvases outside pool (~500MB/sec GC pressure)
2. **Memory Leak:** `layerStyleRenderer.ts` separate canvas system (7,500 leaked canvases/sec)
3. **Silent Errors:** All errors swallowed - users see broken output with no indication
4. **WebGL:** No context loss recovery in GLSLEngine.ts
5. **Dead Code:** Cleanup functions exist but NEVER called
6. **Division by Zero:** 9 vulnerabilities across renderers
7. **No Limits:** Effects array and canvas size unbounded
8. **Test Coverage:** 4.7% (994 lines tested of 21,367)

### Export Pipeline Status (Acceptable for Beta)
- ✅ Excellent NaN validation (`Number.isFinite()` everywhere)
- ✅ Errors collected and returned (not swallowed)
- ✅ Division by zero protected
- ⚠️ One `URL.createObjectURL()` leak (minor)
- ⚠️ 0% test coverage
- ⚠️ Dimension limits inconsistent (8192 vs 4096)

---

## AUDIT DOCUMENTATION

### Complete Audit Files

| Document | Location | Status |
|----------|----------|--------|
| Effect Security Audit | `AUDIT/EFFECT_SECURITY_AUDIT.md` | ✅ Complete |
| Effect System Complete | `AUDIT/EFFECT_SYSTEM_COMPLETE_AUDIT.md` | ✅ Complete |
| Effect Edge Cases | `AUDIT/EFFECT_EDGE_CASES.md` | ✅ Complete |
| Effect Registration Map | `AUDIT/EFFECT_REGISTRATION_MAP.md` | ✅ Complete |
| Export Security Audit | `AUDIT/EXPORT_SECURITY_AUDIT.md` | ✅ Complete |
| Test Coverage Audit | `AUDIT/TEST_COVERAGE_AUDIT.md` | ✅ Complete |

### Key Files for Continued Analysis

#### Effect System (CRITICAL - Needs Fixes)
| File | Lines | Purpose | Issues |
|------|-------|---------|--------|
| `src/services/effectProcessor.ts` | 816 | Effect orchestrator | Canvas leaks, silent errors |
| `src/services/effects/layerStyleRenderer.ts` | 1,075 | Photoshop styles | Separate canvas system, 22-25 leaks/frame |
| `src/services/glsl/GLSLEngine.ts` | 770 | WebGL shaders | No context loss, canvas leak |
| `src/services/effects/timeRenderer.ts` | 967 | Time effects | Echo leak, good NaN validation |
| `src/services/gpuEffectDispatcher.ts` | 869 | GPU routing | No uniform validation |
| `src/engine/layers/BaseLayer.ts` | 2,001 | Effect execution point | Good NaN validation |

#### Export Pipeline (Acceptable)
| File | Lines | Purpose | Status |
|------|-------|---------|--------|
| `src/services/export/exportPipeline.ts` | 1,584 | Main orchestrator | URL leak |
| `src/services/export/cameraExportFormats.ts` | 795 | Camera formats | ✅ Good validation |
| `src/services/comfyui/workflowTemplates.ts` | 2,101 | ComfyUI workflows | ✅ Good validation |
| `src/services/export/depthRenderer.ts` | 741 | Depth rendering | ✅ Good validation |

---

## SYSTEMS REQUIRING FULL AUDIT

### Priority 1: Layer Rendering System (25 files, ~15,000+ lines)

**Entry Point:** `src/engine/layers/BaseLayer.ts`

| File | Lines | Risk | Description |
|------|-------|------|-------------|
| BaseLayer.ts | 2,001 | HIGH | Base class for all layers |
| ImageLayer.ts | ~400 | MEDIUM | Image rendering |
| VideoLayer.ts | ~500 | HIGH | Video decoding, memory |
| TextLayer.ts | ~600 | MEDIUM | Text rendering |
| ShapeLayer.ts | ~400 | MEDIUM | Vector paths |
| ParticleLayer.ts | ~300 | HIGH | Particle GPU interface |
| ModelLayer.ts | ~500 | HIGH | 3D model loading |
| NestedCompLayer.ts | ~300 | HIGH | Composition nesting (depth limits?) |
| EffectLayer.ts | ~331 | MEDIUM | Adjustment layers |
| DepthLayer.ts | ~300 | MEDIUM | Depth maps |
| CameraLayer.ts | ~200 | LOW | Camera instances |
| LightLayer.ts | ~200 | LOW | Lighting |
| + 13 more | ~5,000 | VARIES | Remaining layer types |

**Audit Focus:**
- Memory management (canvas/texture cleanup)
- NaN validation on transform values
- Error handling for failed loads
- Resource limits (max textures, max layers)

### Priority 2: Expression System (19 files, ~8,000+ lines)

**Entry Point:** `src/services/expressions/expressionEvaluator.ts`

| File | Lines | Risk | Description |
|------|-------|------|-------------|
| expressionEvaluator.ts | ~800 | CRITICAL | Main expression engine |
| sesEvaluator.ts | ~600 | ✅ AUDITED | SES sandbox (86 tests) |
| expressionValidator.ts | ~600 | ✅ TESTED | Syntax validation |
| expressionContext.ts | ~400 | HIGH | Context building |
| expressionCache.ts | ~200 | MEDIUM | Result caching |
| easing.ts | ~300 | LOW | Easing functions |
| motionExpressions.ts | ~400 | MEDIUM | Motion helpers |
| + 12 more | ~5,000 | VARIES | Expression utilities |

**Audit Focus:**
- Sandbox escape vectors
- CPU exhaustion (infinite loops)
- Memory exhaustion (large arrays)
- Context pollution

### Priority 3: Particle System (24 files, ~8,000+ lines)

**Entry Point:** `src/engine/particles/ParticleSystem.ts`

| File | Lines | Risk | Description |
|------|-------|------|-------------|
| ParticleSystem.ts | 2,009 | CRITICAL | GPU particles, physics |
| ParticleEmitter.ts | ~600 | HIGH | Emission logic |
| ParticleRenderer.ts | ~500 | HIGH | GPU rendering |
| ParticlePhysics.ts | ~400 | HIGH | Collision detection |
| GPUParticleSystem.ts | ~800 | CRITICAL | WebGPU compute |
| CPUParticleSystem.ts | ~600 | HIGH | Fallback CPU |
| + 18 more | ~3,000 | VARIES | Particle utilities |

**Audit Focus:**
- Particle count limits (memory exhaustion)
- GPU buffer management
- WebGPU device loss handling
- Physics NaN propagation

### Priority 4: Camera/3D System (8+ files, ~4,000+ lines)

**Entry Point:** `src/engine/core/CameraController.ts`

| File | Lines | Risk | Description |
|------|-------|------|-------------|
| CameraController.ts | ~800 | HIGH | Camera management |
| SceneManager.ts | ~600 | HIGH | THREE.js scene |
| RenderPipeline.ts | ~500 | HIGH | Render orchestration |
| ResourceManager.ts | ~400 | CRITICAL | Resource cleanup |
| LayerManager.ts | ~800 | HIGH | Layer lifecycle |

**Audit Focus:**
- THREE.js resource cleanup (geometries, textures, materials)
- WebGL context loss/recovery
- Camera transform NaN
- Scene graph memory growth

### Priority 5: Audio System (10+ files, ~5,000+ lines)

**Entry Points:** `src/stores/audioStore.ts`, `src/services/audio/`

| File | Lines | Risk | Description |
|------|-------|------|-------------|
| audioStore.ts | 711 | HIGH | Audio state management |
| audioSync.ts | 104 | MEDIUM | Sync logic |
| timelineWaveform.ts | 449 | MEDIUM | Waveform display |
| audioAnalyzer.ts | ~400 | MEDIUM | FFT analysis |
| audioReactivity.ts | ~300 | MEDIUM | Audio-driven values |

**Audit Focus:**
- AudioContext lifecycle
- Buffer memory management
- FFT data validation
- WebAudio node cleanup

### Priority 6: Preview/Playback System

**Entry Points:** `src/stores/playbackStore.ts`, `src/services/preview/`

| File | Lines | Risk | Description |
|------|-------|------|-------------|
| playbackStore.ts | 217 | MEDIUM | Playback state |
| frameScheduler.ts | ~400 | MEDIUM | Frame timing |
| previewRenderer.ts | ~600 | HIGH | Preview generation |

**Audit Focus:**
- Frame buffer memory
- requestAnimationFrame cleanup
- Deterministic frame rendering
- Preview quality vs performance

---

## REQUIRED FIXES BEFORE PRODUCTION

### P0 - CRITICAL (Block Release)

| # | Issue | File | Line | Fix |
|---|-------|------|------|-----|
| 1 | Canvas leaks in processEffectStack | effectProcessor.ts | 471-482 | Use CanvasPool.acquire() |
| 2 | Canvas leaks in layerStyleRenderer | layerStyleRenderer.ts | 80-89 | Integrate with CanvasPool |
| 3 | Cleanup never called | effectProcessor.ts | 323-347 | Add setInterval in main.ts |
| 4 | releaseCanvas never called | All renderers | N/A | Add finally blocks |
| 5 | WebGL context loss | GLSLEngine.ts | N/A | Add event listeners |
| 6 | URL.createObjectURL leak | exportPipeline.ts | 1301 | Add revokeObjectURL |

### P1 - HIGH (Fix Before GA)

| # | Issue | File | Fix |
|---|-------|------|-----|
| 7 | Canvas size validation | effectProcessor.ts | Add MAX_CANVAS_SIZE check |
| 8 | Effects array limit | effectProcessor.ts | Add MAX_EFFECTS constant |
| 9 | NaN validation in renderers | stylizeRenderer, colorGrading | Add Number.isFinite checks |
| 10 | Division by zero | timeRenderer:411,414,421 | Add zero checks |
| 11 | Dimension limit mismatch | workflowTemplates vs exportPipeline | Align to 4096 |

### P2 - MEDIUM (Fix Before Beta)

| # | Issue | File | Fix |
|---|-------|------|-----|
| 12 | Global memory budget | effectProcessor.ts | Add memory tracking |
| 13 | Composition depth limit | NestedCompLayer | Add MAX_DEPTH constant |
| 14 | Error callback option | processEffectStack | Add onError parameter |
| 15 | Test coverage to 80% | All systems | Write tests |

---

## TEST COVERAGE GAPS

| System | Lines | Tests | Coverage | Priority |
|--------|-------|-------|----------|----------|
| effectProcessor.ts | 816 | 0 | **0%** | P0 |
| layerStyleRenderer.ts | 1,075 | 0 | **0%** | P0 |
| GLSLEngine.ts | 770 | 0 | **0%** | P0 |
| gpuEffectDispatcher.ts | 869 | 0 | **0%** | P1 |
| exportPipeline.ts | 1,584 | 0 | **0%** | P1 |
| Effect Renderers (11) | 9,968 | 994 | 10% | P1 |
| BaseLayer.ts | 2,001 | 0 | **0%** | P1 |
| ParticleSystem.ts | 2,009 | 0 | **0%** | P2 |

**Total Untested:** ~57,941 lines (84.7% of codebase)

---

## PROJECT OVERVIEW
Motion graphics compositor as ComfyUI custom node pack.
- **Open Source**: Node pack for creating AI video control signals
- **Pro**: Standalone product with LLM, locked nodes, Weyl API integration

---

## SECURITY AUDIT PROTOCOL v4.0

### PHASE 1 STATUS: ✅ COMPLETE (TypeScript/Frontend)

| Control | File | Tests |
|---------|------|-------|
| Expression Sandbox | services/expressions/sesEvaluator.ts | 86/86 |
| URL Validation | services/security/urlValidator.ts | 37 |
| JSON Sanitization | services/security/jsonSanitizer.ts | 37 |

### PHASE 2 STATUS: 🔴 IN PROGRESS (Python Backend)

#### /nodes/ (Priority - these are the ComfyUI nodes)
| File | Status | Risk |
|------|--------|------|
| controlnet_preprocessors.py | ⬜ PENDING | HIGH |
| lattice_layer_decomposition.py | ⬜ PENDING | HIGH |
| compositor_node.py | ⬜ PENDING | MEDIUM |
| lattice_api_proxy.py | ⬜ PENDING | MEDIUM |
| lattice_frame_interpolation.py | ⬜ PENDING | MEDIUM |
| lattice_stem_separation.py | ⬜ PENDING | MEDIUM |
| lattice_vectorize.py | ⬜ PENDING | MEDIUM |
| __init__.py | ⬜ PENDING | LOW |

---

## DANGEROUS PATTERNS TO FIND

### CRITICAL (must fix immediately)
```python
trust_remote_code=True      # Executes arbitrary Python from model repo
exec(user_input)            # Direct code execution
eval(user_input)            # Direct code execution
```

### HIGH (fix or justify)
```python
pickle.load(f)              # Can execute arbitrary code
torch.load(path)            # Uses pickle internally
subprocess.call(user_input) # Command injection
os.system(user_input)       # Command injection
```

---

## KIJAI ComfyUI-WanVideoWrapper INTEGRATION

### Implemented Workflow Generators

| Target | Kijai Nodes Used | Status |
|--------|------------------|--------|
| **TTM** | `WanVideoAddTTMLatents` | ✅ |
| **Uni3C** | `WanVideoUni3C_ControlnetLoader`, `WanVideoUni3C_embeds` | ✅ |
| **SCAIL** | `WanVideoAddSCAILReferenceEmbeds`, `WanVideoAddSCAILPoseEmbeds` | ✅ |
| **WanMove** | `WanVideoAddWanMoveTracks` | ✅ |
| **ATI** | `WanVideoATITracks` | ✅ |
| **Light-X** | `WanVideoLoraSelect` | ✅ |

### NOT Implemented (Future Work)

| Model | Priority | Purpose |
|-------|----------|---------|
| HuMo | HIGH | Audio-driven human motion |
| MTV | MEDIUM | Motion-to-Video |
| recammaster | MEDIUM | Camera re-rendering |
| fantasytalking | MEDIUM | Talking head animation |

---

## FILES (COMMIT STATUS)

| File | Git Status | Notes |
|------|------------|-------|
| CLAUDE.md | ✅ Commit | Project instructions |
| docs/PROJECT_PROGRESS.md | ✅ Commit | Authoritative project status |
| INVENTORY.md | ✅ Commit | Codebase inventory |
| AUDIT/*.md | ✅ Commit | Audit findings |
| SECURITY_ARCHITECTURE.md | ❌ NEVER COMMIT | Contains vulnerability map |
| _archived/* | ❌ Gitignored | Historical only |

---

## ABSOLUTE RULES

1. **NEVER commit SECURITY_ARCHITECTURE.md** - scrub if accidentally pushed
2. **Document before fixing** - create audit trail
3. **One file at a time** - thorough analysis
4. **Prefer safetensors** - no pickle execution risk
5. **No trust_remote_code=True** - ever
6. **Validate all node inputs** - ComfyUI nodes receive user data

---

## CODEBASE INVENTORY (2026-01-01)

### File Counts

| Category | Count | Location |
|----------|-------|----------|
| Services | 181 | `ui/src/services/` |
| Components | 157 | `ui/src/components/` |
| Engine | 60 | `ui/src/engine/` |
| Types | 23 | `ui/src/types/` |
| Tests | 22 | `ui/src/__tests__/` |

### Engine Directory Structure

| Directory | Files | Status |
|-----------|-------|--------|
| `engine/core/` | 5 | ✅ Active |
| `engine/layers/` | 25 | ✅ Active |
| `engine/particles/` | 18 | ✅ Active |
| `engine/animation/` | 2 | ✅ Active |
| `engine/utils/` | 2 | ✅ Active |
| `engine/effects/` | 0 | ⬜ EMPTY |
| `engine/export/` | 0 | ⬜ EMPTY |

---

## DEPRECATED LAYER TYPES (Technical Debt)

### 'null' → 'control' Migration (13 usages remain)

| File | Line | Action Needed |
|------|------|---------------|
| types/project.ts | 616 | ✅ Marked @deprecated |
| useKeyboardShortcuts.ts | 855 | ⚠️ Creates 'null' layer |
| LayerManager.ts | 367 | ✅ Handles deprecated case |
| layerDecompositionActions.ts | 146 | ⚠️ Creates 'null' group |
| layerActions.ts | 1011 | ⚠️ Creates 'null' group |
| actionExecutor.ts | 245 | ⚠️ Comment lies - returns 'null' not 'control' |
| layerDefaults.ts | 87 | ✅ Handles case |
| audioActions.ts | 521,689,803,913,1053 | ⚠️ 5 usages need migration |

### 'adjustment' → 'effectLayer' Migration (6 usages remain)

| File | Line | Action Needed |
|------|------|---------------|
| types/project.ts | 624 | ✅ Marked @deprecated |
| useKeyboardShortcuts.ts | 847 | ⚠️ Creates 'adjustment' layer |
| LayerManager.ts | 433 | ✅ Handles deprecated case |
| layerDefaults.ts | 399 | ✅ Handles case |
| actionExecutor.ts | 259 | ✅ AI maps adjustment→effectLayer |

---

*Last Updated: 2026-01-01*
*Classification: INTERNAL*
