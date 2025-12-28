# Complete Codebase Inventory

**Generated:** 2024-12-28
**Purpose:** Security audit baseline - map ALL code before building security plan

---

## Summary

| Category | Count |
|----------|-------|
| Python Files | 21 |
| TypeScript Files | 290 |
| Vue Components | 144 |
| JavaScript Files (built/dist) | 22 |
| Total Source Files | ~477 |

---

## 1. Python Files (21 total)

### ComfyUI Nodes (`/nodes/`)
| File | Purpose | Risk Level |
|------|---------|------------|
| `__init__.py` | Node pack registration | LOW |
| `compositor_node.py` | Main compositor node (INPUT_TYPES) | **HIGH** |
| `controlnet_preprocessors.py` | ControlNet preprocessing | MEDIUM |
| `lattice_api_proxy.py` | API proxy to Lattice UI | **HIGH** |
| `lattice_frame_interpolation.py` | Frame interpolation node | MEDIUM |
| `lattice_layer_decomposition.py` | Layer decomposition via AI | **HIGH** |
| `lattice_stem_separation.py` | Audio stem separation | MEDIUM |
| `lattice_vectorize.py` | Image vectorization (INPUT_TYPES) | **HIGH** |

### Scripts (`/scripts/`)
| File | Purpose | Risk Level |
|------|---------|------------|
| `decomp_local.py` | Local decomposition testing | LOW |
| `decomp_run.py` | Decomposition runner | LOW |
| `run_decomp_comfyui.py` | ComfyUI decomp integration | LOW |
| `run_decomp_now.py` | Direct decomp execution | LOW |
| `run_decomposition_gpu.py` | GPU decomposition runner | LOW |
| `test_decomp_fp8.py` | FP8 decomp testing | LOW |
| `test_decomp_gpu.py` | GPU decomp testing | LOW |
| `test_decomp_minimal.py` | Minimal decomp test | LOW |
| `test_load_all.py` | Load all modules test | LOW |
| `test_load.py` | Load testing | LOW |
| `test_manual_load.py` | Manual load testing | LOW |
| `test_transformer.py` | Transformer testing | LOW |

### Root
| File | Purpose | Risk Level |
|------|---------|------------|
| `__init__.py` | Package init | LOW |

---

## 2. TypeScript Files (290 total)

### By Directory

#### `/ui/src/services/` (84 files) - **HIGH PRIORITY**
Core business logic, data processing, external integrations.

| Subdirectory | Files | Priority |
|--------------|-------|----------|
| `expressions/` | 19 | **CRITICAL** - Code execution |
| `effects/` | 17 | HIGH - Canvas/GPU operations |
| `ai/` | 10 | **CRITICAL** - External AI calls |
| `export/` | 10 | HIGH - File generation |
| `audio/` | 4 | MEDIUM |
| `security/` | 2 | **CRITICAL** - Security controls |
| `comfyui/` | 3 | **CRITICAL** - Server communication |
| Root services | 19+ | HIGH |

**Critical Service Files:**
- `services/expressions/expressionValidator.ts` - DoS protection
- `services/expressions/sesEvaluator.ts` - SES sandbox
- `services/expressions/workerEvaluator.ts` - Worker timeout
- `services/security/jsonSanitizer.ts` - JSON bomb protection
- `services/security/urlValidator.ts` - URL protocol blocking
- `services/comfyui/comfyuiClient.ts` - WebSocket + fetch
- `services/ai/AICompositorAgent.ts` - AI integration
- `services/layerDecomposition.ts` - Decomposition API

#### `/ui/src/engine/` (41 files) - **HIGH PRIORITY**
Rendering engine, WebGL, Three.js integration.

| Subdirectory | Files | Priority |
|--------------|-------|----------|
| `layers/` | 25 | HIGH - All layer types |
| `particles/` | 18 | MEDIUM - Particle system |
| `core/` | 5 | HIGH - Core engine |
| `animation/` | 2 | MEDIUM |
| Root engine | 6 | HIGH |

**Critical Engine Files:**
- `engine/LatticeEngine.ts` - Main engine entry point
- `engine/core/ResourceManager.ts` - Asset loading (URL validation)
- `engine/layers/VideoLayer.ts` - Video fetch
- `engine/layers/PointCloudLayer.ts` - Point cloud fetch

#### `/ui/src/stores/` (36 files) - **HIGH PRIORITY**
Pinia state management, action handlers.

| Subdirectory | Files | Priority |
|--------------|-------|----------|
| `actions/` | 20 | HIGH - All mutations |
| `actions/layer/` | 3 | HIGH |
| `actions/layers/` | 1 | HIGH |
| `actions/keyframes/` | 1 | MEDIUM |
| Root stores | 11 | MEDIUM |

**Critical Store Files:**
- `stores/actions/projectActions.ts` - Project load/save (fetch, JSON.parse)
- `stores/actions/layerActions.ts` - Layer mutations
- `stores/compositorStore.ts` - Main state

#### `/ui/src/types/` (23 files) - **LOW PRIORITY**
Type definitions only - no runtime code.

#### `/ui/src/components/` (implicit, see Vue section)
UI components - see Vue Components section.

#### `/ui/src/composables/` (18 files) - MEDIUM
Vue composition functions.

#### `/ui/src/utils/` (7 files) - MEDIUM
Utility functions including security helpers.

#### `/ui/src/workers/` (4 files) - **HIGH PRIORITY**
Web Workers for background processing.
- `audioWorker.ts`
- `computeWorker.ts`
- `expressionWorker.ts` - Expression sandbox worker
- `scopeWorker.ts`

#### `/ui/src/__tests__/` (19 files) - LOW
Test files.

---

## 3. Vue Components (144 total)

### By Directory

| Directory | Count | Priority |
|-----------|-------|----------|
| `components/properties/` | 30 | MEDIUM |
| `components/properties/shape-editors/` | 19 | LOW |
| `components/properties/styles/` | 12 | LOW |
| `components/panels/` | 27 | MEDIUM |
| `components/dialogs/` | 18 | MEDIUM |
| `components/timeline/` | 12 | MEDIUM |
| `components/canvas/` | 9 | HIGH |
| `components/layout/` | 6 | LOW |
| `components/controls/` | 9 | MEDIUM |
| `components/curve-editor/` | 4 | LOW |
| `components/materials/` | 4 | HIGH |
| `components/other/` | ~10 | LOW |

**Critical Vue Components (file upload/external data):**
- `components/materials/AssetUploader.vue` - FileReader
- `components/materials/TextureUpload.vue` - FileReader
- `components/panels/AIChatPanel.vue` - fetch to AI
- `components/panels/LayerDecompositionPanel.vue` - FileReader
- `components/dialogs/DecomposeDialog.vue` - FileReader
- `components/dialogs/VectorizeDialog.vue` - FileReader

---

## 4. JavaScript Files (22 total)

### Distribution (`/dist/`)
Built output for standalone use:
- `weyl-compositor.js`
- `weyl-jszip.min.js`
- `weyl-main.js`

### Web (`/web/js/`)
ComfyUI integration built files:
- `extension.js` - ComfyUI extension entry
- `lattice-compositor.js` - Main compositor
- `lattice-main.js` - Main bundle
- `lattice-*-vendor.js` - Vendor bundles
- `worker-*.js` - Web workers

### Other
- `ui/security-test.js` - Security test suite
- `ui/coverage/*.js` - Coverage reporting

---

## 5. External Dependencies

### NPM Dependencies (Production)

| Package | Version | Risk | Notes |
|---------|---------|------|-------|
| `ses` | ^1.10.0 | **CRITICAL** | Secure sandbox for expressions |
| `three` | ^0.170.0 | HIGH | 3D rendering, potential GPU exploits |
| `vue` | ^3.5.0 | MEDIUM | UI framework |
| `pinia` | ^2.2.0 | LOW | State management |
| `dompurify` | ^3.3.1 | **CRITICAL** | HTML sanitization |
| `jszip` | ^3.10.0 | MEDIUM | ZIP handling for exports |
| `mp4-muxer` | ^5.2.2 | MEDIUM | Video encoding |
| `opentype.js` | ^1.3.4 | MEDIUM | Font parsing |
| `paper` | ^0.12.18 | MEDIUM | Vector graphics |
| `polygon-clipping` | ^0.15.7 | LOW | Geometry operations |
| `primevue` | ^4.2.0 | LOW | UI components |
| `simplex-noise` | ^4.0.3 | LOW | Noise generation |
| `splitpanes` | ^4.0.4 | LOW | UI layout |
| `troika-three-text` | ^0.52.4 | MEDIUM | 3D text rendering |
| `webm-muxer` | ^5.1.4 | MEDIUM | Video encoding |
| `camera-controls` | ^2.10.1 | LOW | Camera utilities |
| `@vueuse/core` | ^14.1.0 | LOW | Vue utilities |
| `@phosphor-icons/vue` | ^2.2.1 | LOW | Icons |

### NPM Dependencies (Dev)
- TypeScript, Vite, Vitest, Playwright - standard build/test tools
- @webgpu/types - WebGPU type definitions

### Python Dependencies

| Package | Purpose | Risk |
|---------|---------|------|
| `numpy` | Array operations | LOW |
| `Pillow` | Image processing | MEDIUM |
| `scipy` | Scientific computing (depth-to-normal) | LOW |

---

## 6. Entry Points (Where User Data Enters)

### TypeScript Entry Points

#### Network (fetch)
| File | Purpose | Risk |
|------|---------|------|
| `services/comfyui/comfyuiClient.ts` | ComfyUI server communication | **CRITICAL** |
| `services/ai/AICompositorAgent.ts` | AI API calls | HIGH |
| `services/ai/depthEstimation.ts` | Depth estimation API | HIGH |
| `services/ai/sapiensIntegration.ts` | Sapiens AI | HIGH |
| `services/ai/cameraTrackingAI.ts` | Camera tracking AI | HIGH |
| `services/layerDecomposition.ts` | Layer decomposition API | HIGH |
| `services/segmentation.ts` | Segmentation API | HIGH |
| `services/preprocessorService.ts` | Preprocessing API | HIGH |
| `services/gaussianSplatting.ts` | Gaussian splatting data | MEDIUM |
| `services/vectorize.ts` | Vectorization API | MEDIUM |
| `services/audio/stemSeparation.ts` | Audio stem separation | MEDIUM |
| `stores/actions/projectActions.ts` | Project file loading | **CRITICAL** |
| `engine/layers/VideoLayer.ts` | Video loading | MEDIUM |
| `engine/layers/PointCloudLayer.ts` | Point cloud data | MEDIUM |

#### WebSocket
| File | Purpose | Risk |
|------|---------|------|
| `services/comfyui/comfyuiClient.ts` | Real-time ComfyUI communication | **CRITICAL** |

#### FileReader (Local File Upload)
| File | Purpose | Risk |
|------|---------|------|
| `services/projectStorage.ts` | Project file reading | **CRITICAL** |
| `components/materials/AssetUploader.vue` | Asset uploads | HIGH |
| `components/materials/TextureUpload.vue` | Texture uploads | HIGH |
| `components/panels/LayerDecompositionPanel.vue` | Decomposition input | HIGH |
| `components/dialogs/DecomposeDialog.vue` | Decomposition input | HIGH |
| `components/dialogs/VectorizeDialog.vue` | Vectorization input | HIGH |
| `services/audio/stemSeparation.ts` | Audio file input | MEDIUM |
| `services/video/frameInterpolation.ts` | Video file input | MEDIUM |

#### JSON.parse (Data Deserialization)
| File | Purpose | Risk |
|------|---------|------|
| `services/security/jsonSanitizer.ts` | Safe JSON parsing | PROTECTED |
| `stores/actions/projectActions.ts` | Project deserialization | **CRITICAL** |
| `services/projectStorage.ts` | Project loading | **CRITICAL** |
| `services/jsonValidation.ts` | Schema validation | PROTECTED |
| `services/cameraTrackingImport.ts` | Camera data import | HIGH |
| `services/templateBuilder.ts` | Template loading | HIGH |

#### addEventListener (DOM Events)
44 files with event listeners - mostly UI interactions, lower risk.

### Python Entry Points (ComfyUI)

| File | Method | Input Type | Risk |
|------|--------|------------|------|
| `nodes/compositor_node.py` | INPUT_TYPES | Images, masks, params | **CRITICAL** |
| `nodes/lattice_vectorize.py` | INPUT_TYPES | Images, settings | HIGH |
| `nodes/lattice_api_proxy.py` | HTTP endpoint | Project JSON | **CRITICAL** |
| `nodes/lattice_layer_decomposition.py` | API call | Images | HIGH |

---

## 7. Security Controls (Current)

| Control | Location | Status |
|---------|----------|--------|
| Expression Sandbox (SES) | `services/expressions/sesEvaluator.ts` | ACTIVE |
| Expression Timeout | `services/expressions/workerEvaluator.ts` | ACTIVE |
| Expression Validation | `services/expressions/expressionValidator.ts` | ACTIVE |
| URL Validation | `services/security/urlValidator.ts` | ACTIVE |
| JSON Sanitization | `services/security/jsonSanitizer.ts` | ACTIVE |
| HTML Sanitization | `dompurify` dependency | ACTIVE |

---

## 8. Unprotected Attack Surface

| Area | Risk | Status |
|------|------|--------|
| ComfyUI Workflows | **CRITICAL** | NO PROTECTION |
| LLM Prompt Injection | HIGH | NO PROTECTION |
| Nested Composition Depth | MEDIUM | NO PROTECTION |
| 3D Model Validation | MEDIUM | NO PROTECTION |
| File Size Limits | LOW | PARTIAL |

---

## Next Steps

1. **Audit Priority Order:**
   - `services/expressions/` - Code execution (DONE)
   - `services/security/` - Verify controls
   - `services/comfyui/` - Server communication
   - `stores/actions/projectActions.ts` - Project loading
   - `services/ai/` - External AI calls
   - `engine/layers/` - Asset loading

2. **Create per-file audit trail in `/AUDIT/FILES_ANALYZED.md`**

3. **Document each bug in `/AUDIT/BUGS.md`**
