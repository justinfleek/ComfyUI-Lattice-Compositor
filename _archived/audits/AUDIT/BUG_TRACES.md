# Bug Traces - Meticulous End-to-End Analysis

This document contains detailed traces of each bug from entry point to impact.

## Summary

| Bug ID | File | Root Cause | Fix Complexity | Status |
|--------|------|------------|----------------|--------|
| ADV-001 | cameraExportFormats.ts | NaN not validated in quaternionToEuler/computeViewMatrix | MEDIUM | ✅ Traced |
| ADV-002 | workflowTemplates.ts | node.inputs/class_type not guarded | LOW | ✅ Traced |
| ADV-003 | cameraExportFormats.ts | lerpAngle returns 360 not 0 | LOW | ✅ Traced |
| ADV-004 | **TEST BUG** | Test missing endFrame | LOW | ✅ Traced |
| ADV-005 | **TEST BUG** | Test missing endFrame | LOW | ✅ Traced |
| ADV-006 | depthRenderer.ts | `|| 100` treats 0 as falsy | LOW | ✅ Traced |
| ADV-007 | cameraExportFormats.ts | Threshold inconsistency between functions | MEDIUM | ✅ Traced |
| ADV-008 | workflowTemplates.ts | validateWorkflow crashes on null workflow | LOW | ✅ Traced |
| ADV-009 | workflowTemplates.ts | validateWorkflow crashes on undefined workflow | LOW | ✅ Traced |
| ADV-010 | workflowTemplates.ts | validateWorkflow iterates string characters | LOW | ✅ Traced |
| ADV-011 | workflowTemplates.ts | class_type check doesn't prevent later crash | LOW | ✅ Traced |
| ADV-012 | workflowTemplates.ts | node.inputs undefined crash | LOW | ✅ Traced |
| ADV-013 | workflowTemplates.ts | node.inputs null crash | LOW | ✅ Traced |
| ADV-014 | workflowTemplates.ts | Old node name in Wan22I2V | LOW | ✅ Traced |
| ADV-015 | workflowTemplates.ts | VHS_LoadVideo requires extension | MEDIUM | ✅ Traced |
| ADV-016 | workflowTemplates.ts | length vs num_frames field name | LOW | ✅ Traced |
| ADV-017 | workflowTemplates.ts | Batch size mismatch with control images | MEDIUM | ✅ Traced |
| ADV-018 | workflowTemplates.ts | No node existence validation | HIGH | ✅ Traced |
| ADV-019 | **TEST BUG** | Test config missing required fields | LOW | ✅ Traced |
| ADV-020 | exportPipeline.ts | New canvas per frame in loops | MEDIUM | ✅ Traced |
| ADV-021 | workflowTemplates.ts | Same as ADV-002 (__proto__ vector) | LOW | ✅ Traced |
| ADV-022 | cameraExportFormats.ts | depthOfField assumed non-null | LOW | ✅ Traced |
| ADV-023 | cameraExportFormats.ts | depthOfField assumed non-null | LOW | ✅ Traced |

### Summary by Category:
- **Production Bugs**: 18 (ADV-001, 002, 003, 006, 007, 008-018, 020-023)
- **Test Bugs**: 3 (ADV-004, 005, 019)
- **Merged/Duplicate**: 2 (ADV-021 same as ADV-002, ADV-023 same as ADV-022)

### Fix Priority:
1. **CRITICAL**: ADV-002/008-013 (validation crashes), ADV-022/023 (null crashes)
2. **HIGH**: ADV-001 (NaN propagation), ADV-020 (memory exhaustion)
3. **MEDIUM**: ADV-003 (angle normalization), ADV-006 (opacity), ADV-007 (thresholds)
4. **LOW**: ADV-014-018 (workflow generation)

## Detailed Traces

---

## ADV-001: NaN Rotation Propagation in cameraExportFormats.ts

### Severity: CRITICAL

### Entry Points Where NaN Can Enter:

1. **External Camera Import** (`cameraTrackingImport.ts:368-374`):
   ```typescript
   const euler = quaternionToEuler(
     pose.rotation.w,  // External solve data - NO VALIDATION
     pose.rotation.x,
     pose.rotation.y,
     pose.rotation.z
   );
   ```
   - External solve data could contain NaN quaternion values
   - `quaternionToEuler()` has NO input validation (lines 519-545)
   - NaN propagates directly to orientation keyframes

2. **Camera3D Direct Assignment** (anywhere `Camera3D` is modified):
   - If orientation set to NaN, persists in state
   - Default factory (`createDefaultCamera`) is safe (zeros)

### Propagation Path:

```
External solve data (pose.rotation = NaN)
  ↓
quaternionToEuler() [cameraTrackingImport.ts:519]
  - NO validation of w, x, y, z inputs
  - Math operations on NaN produce NaN
  ↓
Rotation keyframes stored with NaN values
  ↓
interpolateCameraAtFrame() [cameraExportFormats.ts:65]
  ├── WITH interpolation: lerpAngle() handles NaN → 0 ✅
  └── WITHOUT interpolation (lines 70-78, 93-102):
      Returns camera.orientation DIRECTLY ❌
  ↓
computeViewMatrix() [cameraExportFormats.ts:192]
  - rotation.x * Math.PI / 180 → NaN * anything = NaN
  - Math.cos(NaN) = NaN
  - Math.sin(NaN) = NaN
  - All 16 matrix elements become NaN
  ↓
Exported camera data is CORRUPT
```

### Function-by-Function Validation Status:

| Function | Location | NaN Handling | Status |
|----------|----------|--------------|--------|
| `safeNumber()` | cameraExportFormats.ts:31 | ✅ Returns fallback | EXISTS but unused in critical paths |
| `safeFrame()` | cameraActions.ts:26 | ✅ Returns fallback | Only for frame numbers |
| `lerp()` | cameraExportFormats.ts:150 | ✅ Fallback to 0 | OK |
| `lerpAngle()` | cameraExportFormats.ts:159 | ✅ Fallback to 0 | OK |
| `quaternionToEuler()` | cameraTrackingImport.ts:519 | ❌ NONE | **GAP** |
| `interpolateCameraAtFrame()` | cameraExportFormats.ts:65 | ⚠️ PARTIAL | Direct return has no validation |
| `computeViewMatrix()` | cameraExportFormats.ts:192 | ❌ NONE | **GAP** |
| `computeProjectionMatrix()` | cameraExportFormats.ts:241 | ✅ Uses safeNumber | OK |

### Affected Export Targets:

All camera-based exports are affected:
- `motionctrl` - 4x4 RT matrices corrupt
- `motionctrl-svd` - SVD poses corrupt
- `uni3c-camera` - Trajectories corrupt
- `uni3c-motion` - Motion control corrupt
- `animatediff-cameractrl` - Poses corrupt
- `camera-comfyui` - Generic export corrupt

### Required Fix Locations:

1. **cameraTrackingImport.ts:519** - Add NaN validation to `quaternionToEuler()`
2. **cameraExportFormats.ts:70-78** - Validate orientation before return
3. **cameraExportFormats.ts:93-102** - Validate orientation before return
4. **cameraExportFormats.ts:192** - Validate rotation input to `computeViewMatrix()`

### Test Coverage Required:

- [ ] Import solve data with NaN quaternion
- [ ] Camera with NaN orientation direct assignment
- [ ] interpolateCameraAtFrame with no keyframes + NaN camera
- [ ] computeViewMatrix with NaN rotation
- [ ] Full export with NaN camera → verify error or safe fallback

---

## ADV-002: validateWorkflow Crash on Missing class_type

### Severity: CRITICAL

### Type Definitions:

```typescript
// types/export.ts:308-318
export interface ComfyUINode {
  class_type: string;        // Typed as required, but could be undefined at runtime
  inputs: Record<string, any>; // Typed as required, but could be undefined at runtime
  _meta?: { title: string };
}

export interface ComfyUIWorkflow {
  [nodeId: string]: ComfyUINode;  // Index signature allows ANY string key
}
```

### Entry Point:

```typescript
// exportPipeline.ts:1196-1199
const workflow = generateWorkflowForTarget(this.config.target, params);
const validation = validateWorkflow(workflow);
```

### Crash Points in validateWorkflow:

**Crash 1: Line 2055** - `Object.entries(node.inputs)`
```typescript
for (const [inputName, inputValue] of Object.entries(node.inputs)) {
                                               ^^^^^^^^^^^
// TypeError: Cannot convert undefined or null to object
// Happens when node.inputs is undefined
```

**Crash 2: Line 2067** - `node.class_type.includes(...)`
```typescript
const hasOutput = Object.values(workflow).some(
  node => node.class_type.includes('Save') || ...
               ^^^^^^^^^^^^^^
// TypeError: Cannot read properties of undefined (reading 'includes')
// Happens even though line 2050 checks for missing class_type
// The check adds an error but doesn't prevent later crash
```

### Code Flow Analysis:

```
validateWorkflow(workflow)
  ↓
Line 2050: if (!node.class_type) → Adds error, BUT CONTINUES
  ↓
Line 2055: Object.entries(node.inputs) → CRASH if inputs undefined
  ↓
Line 2067: node.class_type.includes(...) → CRASH if class_type undefined
           This line runs even if the check at 2050 found missing class_type!
```

### How Malformed Workflow Can Enter:

1. **Generator Bug**: `generateWorkflowForTarget()` produces incomplete node
2. **External File**: Untrusted workflow JSON loaded by user
3. **Prototype Pollution**: `__proto__` key in workflow (see ADV-021)
4. **Partial Generation**: Error during workflow generation leaves incomplete state

### Affected Code Paths:

| Caller | Location | Risk |
|--------|----------|------|
| `generateComfyUIWorkflow()` | exportPipeline.ts:1199 | After generation, always called |
| Tests | Multiple test files | Test infrastructure |

### Required Fixes:

1. **Line 2055**: Guard `node.inputs` before iterating:
   ```typescript
   if (node.inputs && typeof node.inputs === 'object') {
     for (const [inputName, inputValue] of Object.entries(node.inputs)) {
   ```

2. **Line 2067**: Short-circuit when class_type missing:
   ```typescript
   const hasOutput = Object.values(workflow).some(
     node => node?.class_type?.includes('Save') || ...
   ```

3. **Type Safety**: Add runtime type guard at function entry:
   ```typescript
   if (!node || typeof node !== 'object') {
     errors.push(`Node ${nodeId}: invalid structure`);
     continue;
   }
   ```

### Test Coverage Required:

- [ ] Workflow with node missing class_type
- [ ] Workflow with node missing inputs property
- [ ] Workflow with node that is null/undefined
- [ ] Workflow with node that is not an object (string, number)
- [ ] Empty workflow `{}`
- [ ] Workflow with __proto__ key

---

## ADV-019: Pipeline State Not Reset After Failed Export

### Severity: **RECLASSIFIED - TEST BUG, NOT PRODUCTION BUG**

### Analysis:

The test failure is caused by **incomplete test configuration**, not production code bug.

### Test Configuration (attackSurface.test.ts:169-180):

```typescript
const pipeline2 = new ExportPipeline({
  layers: [],
  cameraKeyframes: [],
  config: {
    target: 'wan22-i2v',
    width: 512,
    height: 512,
    frameCount: 10,
    fps: 24,
    startFrame: 0,
    // MISSING: endFrame, prompt, outputDirectory
  } as any,
});
```

### Validation Failures:

1. **Line 260-262**: `endFrame` is undefined
   - `Number.isFinite(undefined) === false`
   - Error: "End frame must be a valid number"

2. **Line 278-283**: `prompt` is missing
   - `wan22-i2v` requires prompt (`needsPrompt()` returns true)
   - Error: "Prompt is required for this export target"

### ExportPipeline State Analysis:

| State Variable | Scope | Reset? | Leakage Risk |
|----------------|-------|--------|--------------|
| `this.aborted` | Instance | No (set true on abort) | None - each pipeline has own instance |
| `this.layers` | Instance | N/A | None |
| `this.config` | Instance | N/A | None |

### Module-Level State Analysis:

| Module | Mutable State | Risk |
|--------|---------------|------|
| exportPipeline.ts | NONE | Safe |
| comfyuiClient.ts | `let defaultClient: ComfyUIClient \| null` | POTENTIAL - Singleton pattern |

### Potential Production Issue (separate from test):

The `getComfyUIClient()` singleton (comfyuiClient.ts:619-627) could retain error state:

```typescript
let defaultClient: ComfyUIClient | null = null;

export function getComfyUIClient(serverAddress?: string): ComfyUIClient {
  if (!defaultClient || (serverAddress && serverAddress !== defaultClient.server)) {
    defaultClient = new ComfyUIClient({...});
  }
  return defaultClient;
}
```

If the client enters an error state (e.g., WebSocket closed), subsequent exports might fail.

### Required Fix:

1. **TEST FIX**: Add required fields to test configs:
   ```typescript
   config: {
     target: 'wan22-i2v',
     width: 512,
     height: 512,
     frameCount: 10,
     fps: 24,
     startFrame: 0,
     endFrame: 10,        // ADD
     prompt: 'test',      // ADD
     outputDirectory: '/tmp/test',  // ADD
   }
   ```

2. **POTENTIAL PRODUCTION FIX**: Consider adding client health check or reset capability

### Reclassification:

- ADV-019 is **NOT a production bug**
- ADV-019 is a **test infrastructure bug**
- New bug: Consider tracking singleton client state as separate issue

---

## ADV-020: No Canvas Context Allocation Limit

### Severity: HIGH (DoS / Memory Exhaustion)

### Test vs Production Analysis:

The **test** (attackSurface.test.ts:219-241) fails because:
- jsdom/Node.js environment doesn't enforce browser canvas limits
- All 50 canvases created successfully
- Test expected environmental limit that doesn't exist in test env

The **underlying issue** IS real in production:

### Canvas Creation Locations in exportPipeline.ts:

| Location | Context | In Loop? | Risk |
|----------|---------|----------|------|
| Line 318 | Reference frame | No | Low - single canvas |
| Line 361 | Last frame | No | Low - single canvas |
| Line 583 | Depth sequence (engine) | **YES - frameCount iterations** | **HIGH** |
| Line 689 | Depth sequence (fallback) | **YES - frameCount iterations** | **HIGH** |
| Line 745+ | Control sequence | **YES - frameCount iterations** | **HIGH** |
| Line 928 | Lineart processing | Per-frame | **HIGH** |

### Code Pattern Causing Issue:

```typescript
// exportPipeline.ts:583 - CREATES NEW CANVAS PER FRAME
for (let i = 0; i < frameCount; i++) {
  ...
  const canvas = new OffscreenCanvas(width, height);  // NEW allocation every iteration!
  const ctx = this.get2DContext(canvas, ...);
  ctx.putImageData(imageData, 0, 0);
  const blob = await canvas.convertToBlob(...);
  // canvas goes out of scope but may not be GC'd immediately
}
```

### Memory Impact Calculation:

For 4K export (4096×4096) with 1000 frames:
- Canvas buffer: 4096 × 4096 × 4 bytes = **64 MB per canvas**
- 1000 frames = **64 GB** if not garbage collected

### Browser Limits (Reference):

| Browser | Approx Limit | Behavior |
|---------|--------------|----------|
| Chrome | ~16 active contexts | Silent failure (getContext returns null) |
| Firefox | ~8-12 contexts | Silent failure |
| Safari | Varies | May crash tab |

### Required Fix:

**Option 1: Canvas Reuse (Recommended)**
```typescript
private renderDepthSequence(...) {
  // Create ONCE outside loop
  const canvas = new OffscreenCanvas(width, height);
  const ctx = this.get2DContext(canvas, 'depth sequence');

  for (let i = 0; i < frameCount; i++) {
    ctx.clearRect(0, 0, width, height);  // Clear between frames
    ctx.putImageData(imageData, 0, 0);
    const blob = await canvas.convertToBlob(...);
    // ... save blob
  }
}
```

**Option 2: Explicit Cleanup**
```typescript
for (let i = 0; i < frameCount; i++) {
  const canvas = new OffscreenCanvas(width, height);
  const ctx = canvas.getContext('2d');
  // ... use canvas
  // Explicit cleanup hint to GC
  (canvas as any).width = 0;
  (canvas as any).height = 0;
}
```

### Affected Functions:

- `renderDepthSequence()` - exportPipeline.ts:520-719
- `renderControlSequence()` - exportPipeline.ts:725-765
- `applyLineart()` - exportPipeline.ts:925-980
- Similar patterns in wanMoveExport.ts

### Required Behavior:

**ZERO DEGRADATION** - Either complete 100% or fail upfront with clear error.

### Test Coverage Required:

- [ ] Export 100 frames depth sequence - verify ALL 100 frames exported
- [ ] Export with engine vs fallback path - verify identical frame counts
- [ ] Memory profiling during long export - verify stable memory usage
- [ ] Upfront validation rejects impossible exports BEFORE starting
- [ ] Canvas reuse verified - only 1-2 canvases allocated regardless of frame count

---

## ADV-021: validateWorkflow __proto__ Pollution Crash

### Severity: CRITICAL

### Root Cause: SAME AS ADV-002

This is the same bug as ADV-002, triggered by a specific attack vector.

### Attack Vector:

```json
{
  "__proto__": { "isAdmin": true },
  "constructor": { "prototype": { "isAdmin": true } },
  "1": { "class_type": "LoadImage", "inputs": {} }
}
```

### Crash Mechanism:

1. `Object.entries(workflow)` iterates over ALL keys including `__proto__`
2. When `nodeId = "__proto__"`, `node = { "isAdmin": true }`
3. `node.inputs` is `undefined`
4. `Object.entries(node.inputs)` → `Object.entries(undefined)` → **CRASH**

### Why Object.entries Includes __proto__:

When using `JSON.parse()`, `__proto__` becomes a regular enumerable property, NOT the actual prototype. So `Object.entries()` includes it.

### Fix: Same as ADV-002

Guard all property accesses:
```typescript
for (const [nodeId, node] of Object.entries(workflow)) {
  if (!Object.hasOwn(workflow, nodeId)) continue;  // Skip inherited
  if (!node || typeof node !== 'object') continue; // Skip invalid
  if (node.inputs && typeof node.inputs === 'object') {
    for (const [inputName, inputValue] of Object.entries(node.inputs)) {
      // ...
    }
  }
}
```

### Security Note:

The test also verifies prototype pollution DIDN'T work:
```typescript
expect(({} as any).isAdmin).not.toBe(true);
```

This passes because `JSON.parse` creates a regular property, not actual prototype modification. But the crash is still a vulnerability (DoS via malformed input).

---

## ADV-022/023: depthOfField Undefined Crashes

### Severity: CRITICAL

### Type Definition vs Runtime Reality:

```typescript
// types/camera.ts - depthOfField is REQUIRED
export interface Camera3D {
  // ...
  depthOfField: {           // NOT optional in type!
    enabled: boolean;
    focusDistance: number;
    // ...
  };
}
```

### But Runtime Can Receive:

1. **External imports** - Camera tracking data without depthOfField
2. **Legacy data** - Older saved projects
3. **Tests** - Using `as any` bypass
4. **Partial constructions** - Code that builds Camera3D incrementally

### Crash Locations in cameraExportFormats.ts:

| Line | Code | Context |
|------|------|---------|
| 76 | `camera.depthOfField.focusDistance` | No keyframes, return camera defaults |
| 100 | `camera.depthOfField.focusDistance` | No matching keyframes |
| 113 | `camera.depthOfField.focusDistance` | getFocusDist helper |

### Full Stack Trace:

```
interpolateCameraAtFrame (cameraExportFormats.ts:76)
  ← exportCameraMatrices (cameraExportFormats.ts:707)
  ← attackSurface.test.ts:637

exportToMotionCtrl (cameraExportFormats.ts:?)
  ← exportCameraForTarget (cameraExportFormats.ts:770)
  ← attackSurface.test.ts:718
```

### Test Input That Crashes:

```typescript
// attackSurface.test.ts:629-635
const camera = {
  id: 'test',
  position: { x: 0, y: 0, z: -500 },
  orientation: { x: 0, y: 0, z: 0 },
  focalLength: 50,
  zoom: 1,
  // MISSING: depthOfField!
};

exportCameraMatrices(camera as any, [], {...});  // CRASH
```

### Where Valid Camera3D Objects Are Created:

| Location | depthOfField Present? |
|----------|----------------------|
| `createDefaultCamera()` (camera.ts:173) | ✅ YES |
| `exportPipeline.ts:625` (defaultCamera) | ✅ YES |
| `exportPipeline.ts:1102` (exportCamera) | ✅ YES |
| External import (cameraTrackingImport.ts) | ❌ MAYBE NOT |
| Test mocks | ❌ MAYBE NOT |

### Required Fix:

Add defensive access at EVERY location that reads depthOfField:

```typescript
// Option 1: Safe accessor function
function getFocusDistance(camera: Camera3D): number {
  return camera.depthOfField?.focusDistance ?? 100; // Sensible default
}

// Option 2: Guard in interpolateCameraAtFrame
const getDefaultFocusDistance = () =>
  camera.depthOfField?.focusDistance ?? 100;
```

### Fix Locations:

- `cameraExportFormats.ts:76` - add null-safe access
- `cameraExportFormats.ts:100` - add null-safe access
- `cameraExportFormats.ts:113` - add null-safe access
- `cameraTrackingImport.ts` - ensure imported cameras have depthOfField

### Why This Matters:

This isn't just a test issue. Real users could:
1. Import camera data from 3D tracking software (no depthOfField)
2. Load old project files (missing newer properties)
3. Copy/paste partial camera objects

The code MUST be defensive about optional nested properties, regardless of TypeScript types.

---

## ADV-003: 360° Boundary Interpolation Takes Long Path

### Severity: HIGH

### Location: `cameraExportFormats.ts:159-171`

### The Bug:

```typescript
function lerpAngle(a: number, b: number, t: number): number {
  let diff = b - a;
  if (diff > 180) diff -= 360;
  if (diff < -180) diff += 360;
  return a + diff * t;  // Can return 360 instead of 0
}
```

### Test Case:

```typescript
// Keyframes: 350° → 10° (short path = 20°, midpoint = 0°)
const keyframes = [
  { frame: 0, orientation: { y: 350 } },
  { frame: 10, orientation: { y: 10 } },
];
interpolateCameraAtFrame(camera, keyframes, 5);
// Expected: rotation.y ≈ 0
// Actual: rotation.y = 360
```

### Math Trace:

```
a = 350, b = 10, t = 0.5
diff = 10 - 350 = -340
diff < -180 → diff += 360 → diff = 20
result = 350 + 20 * 0.5 = 360  ← NOT normalized!
```

### Impact:

- 360° and 0° are mathematically equivalent for rotation
- BUT downstream systems may expect normalized range [0, 360) or [-180, 180)
- Comparison checks fail (360 ≠ 0)
- Animation curves show discontinuities at wrap points

### Required Fix:

```typescript
function lerpAngle(a: number, b: number, t: number): number {
  // ... existing code ...
  let result = a + diff * t;

  // Normalize to [0, 360)
  result = ((result % 360) + 360) % 360;
  return result;
}
```

---

## ADV-004: Boundary Validation Off-by-One (64x64 Fails)

### Severity: **RECLASSIFIED - TEST BUG, NOT PRODUCTION BUG**

### Analysis:

The dimension validation is CORRECT:
```typescript
// exportPipeline.ts:230 - This allows 64 (not less than 64)
if (this.config.width < 64 || this.config.width > 4096) {
  errors.push(...);
}
```

### Why Test Fails:

The test helper `createValidConfig()` is missing `endFrame`:

```typescript
// exportPipeline.adversarial.test.ts:49-70
function createValidConfig(overrides) {
  return {
    target: 'wan22-i2v',
    width: 512,
    height: 512,
    frameCount: 24,
    fps: 24,
    startFrame: 0,
    // MISSING: endFrame!
    prompt: 'test',
    ...
  };
}
```

The dimension override works, but validation still fails at line 260:
```typescript
if (!Number.isFinite(this.config.endFrame)) {  // undefined → false → ERROR
  errors.push(`End frame must be a valid number`);
}
```

### Required Fix:

Add `endFrame` to test helper:
```typescript
function createValidConfig(overrides) {
  return {
    ...
    startFrame: 0,
    endFrame: 24,  // ADD THIS
    ...
  };
}
```

### Production Code Status: ✅ CORRECT

The production validation at lines 230-236 properly allows 64 as minimum dimension.

---

## ADV-006: Zero Opacity Layers Not Skipped

### Severity: MEDIUM (Performance + Correctness)

### Location: `depthRenderer.ts:156-166`

### The Bug:

```typescript
function getLayerOpacity(layer: Layer, frame: number): number {
  if (layer.opacity && 'keyframes' in layer.opacity && layer.opacity.keyframes?.length > 0) {
    return (interpolateValue(layer.opacity.keyframes, frame) || 100) / 100;
    //                                                      ^^^^^^
    // BUG: || treats 0 as falsy, returns 100 instead of 0!
  }

  if (layer.opacity && 'value' in layer.opacity) {
    return (layer.opacity.value || 100) / 100;
    //                          ^^^^^^
    // BUG: Same issue - 0 || 100 = 100
  }

  return 1;
}
```

### JavaScript Falsy Bug:

```javascript
0 || 100  // = 100 (0 is falsy, so uses fallback)
0 ?? 100  // = 0   (nullish coalescing only triggers on null/undefined)
```

### Impact:

- Layer with `opacity: { value: 0 }` returns 1.0 (100%) instead of 0.0
- Zero opacity layers are processed and written to depth buffer
- Incorrect depth maps generated
- Performance waste processing invisible layers

### Required Fix:

Use nullish coalescing operator:
```typescript
function getLayerOpacity(layer: Layer, frame: number): number {
  if (layer.opacity && 'keyframes' in layer.opacity && layer.opacity.keyframes?.length > 0) {
    return (interpolateValue(layer.opacity.keyframes, frame) ?? 100) / 100;
  }

  if (layer.opacity && 'value' in layer.opacity) {
    return (layer.opacity.value ?? 100) / 100;
  }

  return 1;
}
```

### Similar Patterns to Check:

This `|| 100` pattern for opacity may exist elsewhere:
- Search: `opacity.value || 100` or `|| 100` near opacity
- Also check: `|| 0` for values where 0 is valid

---

## ADV-007: Zoom/Motion Detection Threshold Inconsistency

### Severity: MEDIUM (Inconsistent behavior across export targets)

### Location: `cameraExportFormats.ts` - Two functions with different thresholds

### The Bug:

Two functions analyze the same camera keyframes but use DIFFERENT thresholds:

**Function 1: `detectMotionCtrlSVDPreset` (lines 311-352)**
```typescript
const threshold = 50; // Single threshold for all movement

// Zoom check
if (Math.abs(deltaZ) > threshold) { ... }  // 50

// Rotation check
if (Math.abs(deltaRy) > 15) { ... }        // 15

// Pan check
if (Math.abs(deltaX) > threshold) { ... }  // 50
```

**Function 2: `analyzeCameraMotion` (lines 399-470)**
```typescript
const panThreshold = 30;     // Different from 50!
const zoomThreshold = 50;    // Same
const orbitThreshold = 20;   // Different from 15!

// Pan check
if (panX > panThreshold || panY > panThreshold) { ... }  // 30

// Zoom check
if (Math.abs(deltaZ) > zoomThreshold) { ... }            // 50

// Orbit check
if (Math.abs(deltaRy) > orbitThreshold && ...) { ... }   // 20
```

### Threshold Comparison:

| Motion Type | detectMotionCtrlSVDPreset | analyzeCameraMotion | Difference |
|-------------|--------------------------|---------------------|------------|
| Zoom (Z)    | 50                       | 50                  | ✅ Same |
| Pan (X/Y)   | 50                       | 30                  | ❌ 20 units |
| Rotation (Y)| 15                       | 20 (orbit)          | ❌ 5 degrees |

### Impact:

Camera movement in the "gap" between thresholds produces INCONSISTENT results:

**Example 1: Pan with deltaX=35**
- `analyzeCameraMotion`: Detects pan (35 > 30) → returns `hasPan: true`
- `detectMotionCtrlSVDPreset`: No pan (35 < 50) → might return `'static'`

**Result**: `mapToWan22FunCamera` says "Pan Right", but `detectMotionCtrlSVDPreset` says "static"

**Example 2: Rotation with deltaRy=18**
- `detectMotionCtrlSVDPreset`: Detects rotation (18 > 15) → returns `'rotate_cw'`
- `analyzeCameraMotion`: No orbit (18 < 20) → returns `hasOrbit: false`

**Result**: MotionCtrl-SVD gets rotation, but Wan22FunCamera doesn't detect it

### Call Sites:

| Function | Called By | Export Target |
|----------|-----------|---------------|
| `detectMotionCtrlSVDPreset` | `exportToMotionCtrlSVD` | motionctrl-svd |
| `analyzeCameraMotion` | `mapToWan22FunCamera` | wan22-fun-camera |
| `analyzeCameraMotion` | `detectUni3CTrajectoryType` | uni3c-camera, uni3c-motion |
| `analyzeCameraMotion` | `detectCameraCtrlMotionType` | animatediff-cameractrl |

### Required Fix:

**Option 1: Unify Thresholds (Recommended)**
```typescript
// Define once at module level
const MOTION_THRESHOLDS = {
  pan: 30,      // Sensitivity for pan detection (units)
  zoom: 50,     // Sensitivity for zoom detection (units)
  rotation: 15, // Sensitivity for rotation detection (degrees)
} as const;

// Use in both functions
if (Math.abs(deltaX) > MOTION_THRESHOLDS.pan) { ... }
```

**Option 2: Document Intentional Difference**
If thresholds differ intentionally (different targets have different sensitivity needs), document WHY:
```typescript
// MotionCtrl-SVD uses higher pan threshold (50) because
// the model is less sensitive to small movements
const threshold = 50;
```

### Test Coverage Required:

- [ ] Test camera with deltaX=35 → verify same detection across functions
- [ ] Test camera with deltaRy=18 → verify same detection across functions
- [ ] Test edge cases at exact threshold boundaries
- [ ] Integration test: Same keyframes export to multiple targets → verify consistent motion type

---

## ADV-008 through ADV-013: Workflow Input Validation Gaps

### Severity: HIGH (Crashes on malformed input)

### Location: `workflowTemplates.ts:2038-2079` - `validateWorkflow` function

### The Bug:

The `validateWorkflow` function has multiple paths where invalid input crashes instead of returning validation errors.

### Complete Code Analysis:

```typescript
export function validateWorkflow(workflow: ComfyUIWorkflow): {
  valid: boolean;
  errors: string[];
  warnings: string[];
} {
  const errors: string[] = [];
  const warnings: string[] = [];

  const nodeIds = Object.keys(workflow);   // ← BUG: Crashes if workflow is null/undefined

  for (const [nodeId, node] of Object.entries(workflow)) {
    // Check class_type exists
    if (!node.class_type) {                // ← Line 2050: Adds error BUT CONTINUES
      errors.push(`Node ${nodeId}: missing class_type`);
    }

    // Check connections reference valid nodes
    for (const [inputName, inputValue] of Object.entries(node.inputs)) {
      //                                               ^^^^^^^^^^^^^^^^
      //                                               ← Line 2055: CRASH if node.inputs undefined
      if (Array.isArray(inputValue) && inputValue.length === 2) {
        const [refNodeId] = inputValue;
        if (typeof refNodeId === 'string' && !nodeIds.includes(refNodeId)) {
          errors.push(`Node ${nodeId}.${inputName}: references non-existent node ${refNodeId}`);
        }
      }
    }
  }

  // Check for output nodes
  const hasOutput = Object.values(workflow).some(
    node => node.class_type.includes('Save') || ...
    //      ^^^^^^^^^^^^^^^^^^^^^^^
    //      ← Line 2067: CRASH if ANY node has undefined class_type
    //      Even though we detected it at line 2050!
  );
  ...
}
```

### Gap Analysis:

| Line | Bug ID | Input | Expected | Actual |
|------|--------|-------|----------|--------|
| 2046 | ADV-008 | `workflow = null` | Return `{ valid: false, errors: ['...'] }` | `TypeError: Cannot convert null to object` |
| 2046 | ADV-009 | `workflow = undefined` | Return validation error | `TypeError` |
| 2046 | ADV-010 | `workflow = "string"` | Return validation error | Iterates characters |
| 2050 | ADV-011 | `node.class_type = undefined` | Continue safely | Crashes at line 2067 |
| 2055 | ADV-012 | `node.inputs = undefined` | Skip iteration | `TypeError: Cannot convert undefined to object` |
| 2055 | ADV-013 | `node.inputs = null` | Skip iteration | `TypeError` |

### Data Flow Proving Crash:

```
validateWorkflow({ "1": { class_type: "LoadImage" } })  // inputs missing
  ↓
Line 2046: nodeIds = ["1"]
  ↓
Line 2048: Iterates, nodeId = "1", node = { class_type: "LoadImage" }
  ↓
Line 2050: !node.class_type → false (has class_type)
  ↓
Line 2055: Object.entries(node.inputs)
  ↓
node.inputs is undefined!
  ↓
Object.entries(undefined) → TypeError: Cannot convert undefined or null to object
```

### Where Invalid Workflows Come From:

1. **User imports** - JSON pasted from web tutorials might be incomplete
2. **Generator bugs** - Our own generators could produce partial nodes on error
3. **ComfyUI updates** - Node schemas change, old saved workflows become invalid
4. **Copy/paste errors** - Users copy partial workflow JSON
5. **Prototype pollution** - `__proto__` key in parsed JSON (see ADV-021)

### Required Fix:

```typescript
export function validateWorkflow(workflow: ComfyUIWorkflow): {
  valid: boolean;
  errors: string[];
  warnings: string[];
} {
  const errors: string[] = [];
  const warnings: string[] = [];

  // ADV-008/009/010: Guard workflow itself
  if (!workflow || typeof workflow !== 'object' || Array.isArray(workflow)) {
    return {
      valid: false,
      errors: ['Workflow must be a non-null object'],
      warnings: [],
    };
  }

  const nodeIds = Object.keys(workflow);

  for (const [nodeId, node] of Object.entries(workflow)) {
    // ADV-010: Skip inherited properties and invalid nodes
    if (!Object.hasOwn(workflow, nodeId)) continue;
    if (!node || typeof node !== 'object') {
      errors.push(`Node ${nodeId}: must be an object`);
      continue;
    }

    // ADV-011: Check class_type with early continue
    if (!node.class_type || typeof node.class_type !== 'string') {
      errors.push(`Node ${nodeId}: missing or invalid class_type`);
      continue; // ← CRITICAL: Don't process further if class_type missing
    }

    // ADV-012/013: Guard node.inputs before iterating
    if (node.inputs && typeof node.inputs === 'object') {
      for (const [inputName, inputValue] of Object.entries(node.inputs)) {
        // ... existing validation
      }
    }
  }

  // ADV-011: Safe access with optional chaining
  const hasOutput = Object.values(workflow).some(
    node => node?.class_type?.includes?.('Save') ||
            node?.class_type?.includes?.('Output') ||
            node?.class_type?.includes?.('Preview')
  );
  // ...
}
```

### Test Coverage Required:

- [ ] `validateWorkflow(null)` → `{ valid: false, errors: [...] }`
- [ ] `validateWorkflow(undefined)` → `{ valid: false, errors: [...] }`
- [ ] `validateWorkflow("string")` → `{ valid: false, errors: [...] }`
- [ ] `validateWorkflow({})` → `{ valid: true, warnings: ['no output nodes'] }`
- [ ] `validateWorkflow({ "1": null })` → validation error
- [ ] `validateWorkflow({ "1": { class_type: "X" } })` → valid (inputs optional)
- [ ] `validateWorkflow({ "1": { inputs: {} } })` → error (class_type required)
- [ ] `validateWorkflow({ "__proto__": {...} })` → no crash, skip inherited

---

## ADV-014 through ADV-018: Workflow Generator Missing Required Inputs

### Severity: MEDIUM (Generated workflows fail in ComfyUI)

### Analysis Method:

Cross-reference each workflow generator against ComfyUI node schemas to identify missing required inputs.

### ADV-014: `generateWan22I2VWorkflow` - Missing Required Fields

**File:** `workflowTemplates.ts:288-368`

**Issue:** WanVideoModelLoader may require additional fields depending on ComfyUI version.

**Current:**
```typescript
workflow[wanLoaderId] = createNode('DownloadAndLoadWan2_1Model', {
  model: `wan2.1_${wanModel}_bf16.safetensors`,
  base_precision: 'bf16',
  quantization: 'disabled',
}, 'Load Wan Model');
```

**Potential Missing:** The node name `DownloadAndLoadWan2_1Model` is from an older version. Current Kijai wrapper uses `WanVideoModelLoader`.

**Status:** UNCERTAIN - Need to verify against actual ComfyUI installation.

### ADV-015: `generateUni3CWorkflow` - VHS_LoadVideo May Not Exist

**File:** `workflowTemplates.ts:588-596`

**Issue:** Uses `VHS_LoadVideo` which requires VideoHelperSuite extension.

```typescript
workflow[renderVideoId] = createNode('VHS_LoadVideo', {
  video: params.uni3cRenderVideo || 'camera_render.mp4',
  ...
}, 'Load Camera Render Video');
```

**Impact:** If user doesn't have VideoHelperSuite installed, workflow fails with "Node type not found".

**Fix:** Add validation or provide fallback using native `LoadImage` batch.

### ADV-016: `generateTTMWorkflow` - Missing num_frames Field

**File:** `workflowTemplates.ts:1119-1132`

**Issue:** `WanVideoImageToVideoEncode` uses `length` but Kijai's node expects `num_frames`:

```typescript
workflow[imageEncoderId] = createNode('WanVideoImageToVideoEncode', {
  ...
  length: params.frameCount,  // ← Is this right? Or should it be num_frames?
  ...
});
```

**Verification needed:** Check Kijai's actual node definition.

### ADV-017: `generateControlNetWorkflow` - Batch Size Mismatch

**File:** `workflowTemplates.ts:1239-1245`

**Issue:** Empty latent batch size set to frameCount, but control images loaded separately.

```typescript
workflow[latentId] = createNode('EmptyLatentImage', {
  width: params.width,
  height: params.height,
  batch_size: params.frameCount,  // ← Must match loaded control image count
}, 'Empty Latent');
```

If control sequence has different frame count than `params.frameCount`, dimensions mismatch crashes.

### ADV-018: All Workflows - No Validation of Node Existence

**Issue:** No runtime check that referenced node classes actually exist in user's ComfyUI.

**Impact:** Workflow generation succeeds, but ComfyUI rejects with cryptic "Unknown node type" error.

**Proposed Fix:**
```typescript
// Add to workflow generation
const REQUIRED_EXTENSIONS: Record<ExportTarget, string[]> = {
  'wan22-i2v': ['ComfyUI-WanVideoWrapper'],
  'uni3c-camera': ['ComfyUI-WanVideoWrapper', 'VideoHelperSuite'],
  'ttm': ['ComfyUI-WanVideoWrapper'],
  'controlnet-depth': ['ControlNet'],
  // ...
};

export function checkRequiredExtensions(target: ExportTarget): {
  missing: string[];
  available: string[];
} {
  // Would need to query ComfyUI's /object_info endpoint
  // to check which nodes are available
}
```

### Summary Table:

| Bug ID | Generator | Issue | Fix Complexity |
|--------|-----------|-------|----------------|
| ADV-014 | generateWan22I2VWorkflow | Old node name | LOW - rename |
| ADV-015 | generateUni3CWorkflow | VHS extension required | MEDIUM - add fallback |
| ADV-016 | generateTTMWorkflow | length vs num_frames | LOW - verify and fix |
| ADV-017 | generateControlNetWorkflow | Batch size mismatch | MEDIUM - validate |
| ADV-018 | All workflows | No node existence check | HIGH - add API check |

### Test Coverage Required:

- [ ] Generate each workflow type and validate against ComfyUI /object_info
- [ ] Test workflow with mismatched frame counts
- [ ] Test with missing VideoHelperSuite extension
- [ ] Integration test: Execute generated workflow in actual ComfyUI

---

## TEST-001: THREE.js Mock Constructor Bug

### Severity: CRITICAL (Blocks 46 tests)

### Location: Multiple test files using `vi.mock('three', ...)`

### The Bug:

THREE.js classes are mocked as arrow functions instead of proper constructors:

**Current (Broken):**
```typescript
vi.mock('three', () => ({
  Vector3: (x, y, z) => ({ x, y, z }),       // Arrow function!
  Matrix4: () => ({ elements: new Array(16).fill(0) }),
  Quaternion: () => ({ x: 0, y: 0, z: 0, w: 1 }),
}));
```

**Why it fails:**
```typescript
// Production code does:
const position = new THREE.Vector3(x, y, z);  // "new" requires constructor

// Arrow functions can't be called with "new":
// TypeError: (x, y, z) => ({ x, y, z }) is not a constructor
```

**Fix:**
```typescript
vi.mock('three', () => ({
  Vector3: class {
    constructor(public x = 0, public y = 0, public z = 0) {}
    set(x: number, y: number, z: number) { this.x = x; this.y = y; this.z = z; return this; }
    clone() { return new (this.constructor as any)(this.x, this.y, this.z); }
  },
  Matrix4: class {
    elements = new Float32Array(16);
    constructor() { this.identity(); }
    identity() { /* ... */ return this; }
    multiply(m: any) { return this; }
  },
  Quaternion: class {
    constructor(public x = 0, public y = 0, public z = 0, public w = 1) {}
    setFromEuler(e: any) { return this; }
  },
}));
```

### Affected Files:

| Test File | Failures |
|-----------|----------|
| modelExport.adversarial.test.ts | 26 |
| cameraExportFormats.adversarial.test.ts | 10 |
| depthRenderer.adversarial.test.ts | 5 |
| allTargets.comprehensive.test.ts | 5 |

### Test Coverage Required:

- [ ] Fix all THREE.js mocks in affected test files
- [ ] Create shared THREE.js mock in `__tests__/helpers/threeMock.ts`
- [ ] Verify all 46 blocked tests pass after fix

---

## TEST-002: Test Helper Missing Required Fields

### Severity: HIGH (Caused false positives)

### Status: ✅ FIXED

### Location: `exportPipeline.adversarial.test.ts:49-70`

### The Bug:

`createValidConfig()` helper was missing `endFrame` field, causing tests to fail at validation before testing actual functionality.

### Fix Applied:

```typescript
function createValidConfig(overrides) {
  return {
    // ... other fields ...
    startFrame: 0,
    endFrame: 24,  // ADDED - was missing
    // ...
  };
}
```

---

## TEST-003: Test Uses Wrong Export Target

### Severity: MEDIUM (Tests didn't test what they claimed)

### Status: ✅ FIXED

### Location: `exportPipeline.adversarial.test.ts` - multiple tests

### The Bug:

Tests for "minimum dimensions", "maximum dimensions", "single frame" used `wan22-i2v` target which requires reference image, but had `exportReferenceFrame: false`.

Tests were failing on "missing reference image" instead of testing dimensions/frames.

### Fix Applied:

Changed tests to use `controlnet-depth` target which doesn't require reference image:

```typescript
it('should handle minimum valid dimensions (64x64)', async () => {
  const options = createValidOptions({
    width: 64,
    height: 64,
    target: 'controlnet-depth' as ExportTarget,  // FIXED
  });
  // ...
});
```

---

## TEST-004 through TEST-006: Coverage Gaps (Documentation Only)

See separate audit documents for comprehensive analysis:

- **`/AUDIT/EFFECT_SYSTEM_AUDIT.md`** - Effect renderer coverage (11.8%)
- **`/AUDIT/TEST_COVERAGE_AUDIT.md`** - Overall service/store coverage (16.4%)

### Summary:

| Gap ID | Area | Files Untested | Lines Untested |
|--------|------|----------------|----------------|
| TEST-004 | Effect renderers | 14/17 | 10,613 |
| TEST-005 | Services | 70/83 | 44,165 |
| TEST-006 | Stores | 7/10 | 2,428 |

---

*Last Updated: 2026-01-01*
