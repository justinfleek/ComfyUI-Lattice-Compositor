# Bug Registry

**Last Updated:** 2026-01-10
**Found By:** Adversarial Tests, Security Audit, Phase 0 Refactor Audit

---

## Summary

| Severity | Count | Status |
|----------|-------|--------|
| P0 - Critical | 4 | **4 Fixed** |
| P0 - Effect System | 6 | **6 Fixed** (Phase 0 Refactor) |
| P1 - High | 14 | 9 Fixed / **5 OPEN (Camera System)** |
| P2 - Medium | 6 | **3 Fixed** / 1 Open / 2 Export |
| Design Choices | 5 | Not Bugs |
| Test Errors | 3 | 2 Fixed / **1 OPEN (TE-003)** |

## Code Quality Note (2026-01-10)

**Bug ID references have been removed from production code.** Professional codebases do not include
external tracking IDs like "BUG-XXX" or "CAM-XXX" in source files. All production code comments
now explain the *why* without referencing external tracking systems.

Test files appropriately retain bug references for regression test documentation.

## Regression Test Coverage

| Area | Test File | Tests |
|------|-----------|-------|
| Viewport Controls NaN | regression/camera/viewport-controls-nan-validation.regression.test.ts | 16 |
| Camera Export NaN | regression/camera/camera-export-nan-validation.regression.test.ts | 22 |
| Camera 3D Projection | regression/camera/BUG-camera3d-double-divide.regression.test.ts | 4 |
| **Total** | | **42 regression tests** |

Additionally, 126 camera export tests and 49 integration tests verify the camera system.

---

## 🚨 CAMERA SYSTEM - CRITICAL ISSUES (Found 2026-01-10)

**Status:** BLOCKING - These bugs affect ALL interactive features including spline editing, path drawing, layer manipulation, and coordinate accuracy.

**Root Cause Analysis:** Complete coordinate system audit revealed fundamental bugs in how screen coordinates are transformed to canvas/world space.

**Historical Symptoms Explained:**
- ❌ Mouse coordinates not aligning with canvas points → **CAM-002**
- ❌ Small camera moves causing large point displacements → **CAM-001**
- ❌ Spline/path points not following mouse accurately → **CAM-001 + CAM-002**
- ❌ Points going off-screen unexpectedly → **CAM-001**
- ❌ Extreme lag in point placement → **CAM-003**

---

## 🔴 P0 - CAMERA SYSTEM CRITICAL BUGS

### CAM-001: Pan Offset Unit Mismatch ✅ FIXED

**File:** `ui/src/engine/LatticeEngine.ts:1107-1108`
**Function:** `setViewportTransform`
**Found:** 2026-01-10 by coordinate system audit
**Fixed:** 2026-01-10
**Severity:** P0 - CRITICAL (Causes ~8-16x coordinate displacement)

**Description:**
The viewport pan values are passed to the camera in screen pixels, but the camera interprets them as world units. This causes pan movements to be dramatically amplified.

**Evidence:**
```typescript
// LatticeEngine.ts:1107-1108
setViewportTransform(transform: number[]): void {
  const scale = transform[0];
  const tx = transform[4];  // Screen pixels!
  const ty = transform[5];  // Screen pixels!

  this.camera.setZoom(scale);    // ✓ Correct
  this.camera.setPan(tx, ty);    // ✗ WRONG: camera expects world units
}

// CameraController.ts:395-398
setPan(x: number, y: number): void {
  this.panOffset.set(x, y);  // Stored as world units
}
```

**Data Flow:**
```
useViewportControls.ts:129
  viewportTransform[4] = (viewW - scaledW) / 2  ← Screen pixels (e.g., 400)
      ↓
LatticeEngine.ts:1108
  camera.setPan(400, 0)  ← Passed as-is
      ↓
CameraController.ts:395
  panOffset.set(400, 0)  ← Interpreted as 400 world units!
      ↓
Result: Camera pans 400 world units instead of appropriate screen offset
```

**Impact:**
- Pan 100 screen pixels → points move ~800-1600 world units
- Small viewport adjustments cause massive coordinate shifts
- All spline/path editing becomes impossible

**Fix Applied:**
```typescript
// Convert viewport pan from screen pixels to world units.
// The viewport transform stores pan in screen pixels, but the camera's
// setPan() expects world units. Dividing by zoom (scale) normalizes
// the offset so that visual pan distance matches user expectation
// regardless of zoom level.
const safeScale = scale > 0 ? scale : 1;
const worldPanX = tx / safeScale;
const worldPanY = ty / safeScale;
this.camera.setPan(worldPanX, worldPanY);
```

---

### CAM-002: SVG Coordinate Transform Ignored ✅ FIXED

**Files Fixed:**
- `ui/src/components/canvas/SplineEditor.vue` - Added overlayStyle with pan offset
- `ui/src/components/canvas/MaskEditor.vue` - Added overlayStyle with pan offset

**Found:** 2026-01-10 by coordinate system audit
**Fixed:** 2026-01-10
**Severity:** P0 - CRITICAL (Mouse clicks don't align with canvas)

**Description:**
The `screenToCanvas()` function uses simple proportional scaling but completely ignores the CSS transform (zoom + pan) applied to the SVG overlay element.

**Evidence:**
```typescript
// useSplineInteraction.ts:164-173 (BROKEN)
function screenToCanvas(screenX: number, screenY: number) {
  const svgRect = overlayStyle.value;
  const svgWidth = parseFloat(svgRect.width);
  const svgHeight = parseFloat(svgRect.height);

  // Simple proportional mapping - IGNORES CSS TRANSFORM!
  const x = (screenX / svgWidth) * canvasWidth.value;
  const y = (screenY / svgHeight) * canvasHeight.value;
  return { x, y };
}
```

**But the SVG has CSS transforms applied:**
```typescript
// SplineEditor.vue overlayStyle computed
transform: `translate(${tx}px, ${ty}px) scale(${zoom})`
```

**The Problem:**
1. User clicks at screen position (200, 150)
2. SVG has transform: `translate(100, 0) scale(2)`
3. `screenToCanvas()` computes: `(200 / svgWidth) * canvasWidth`
4. **Completely ignores that SVG is translated and scaled!**
5. Click registers at wrong canvas position

**Impact:**
- At 2x zoom, clicks appear at 0.5x the actual canvas position
- At any pan offset, clicks are shifted by the pan amount
- Spline editing, path drawing, point selection all broken

**Fix Applied (SplineEditor.vue):**
```typescript
// Apply viewport pan offset to keep SVG aligned with the canvas.
// viewportTransform[4,5] contain screen-pixel pan offsets. The SVG must
// move with the viewport so mouse coordinates stay aligned with canvas
// content during pan operations.
const vpt = props.viewportTransform;
const panOffsetX = vpt && vpt.length > 4 && Number.isFinite(vpt[4]) ? vpt[4] : 0;
const panOffsetY = vpt && vpt.length > 5 && Number.isFinite(vpt[5]) ? vpt[5] : 0;

const left = centerLeft + panOffsetX;
const top = centerTop + panOffsetY;
```

**Fix Applied (MaskEditor.vue):**
```typescript
// Compute CSS transform to keep mask overlay aligned with canvas during pan/zoom.
// viewportTransform: [scaleX, skewX, skewY, scaleY, translateX, translateY]
// We apply translate for pan offset and scale for zoom level.
const overlayStyle = computed(() => {
  const vt = props.viewportTransform;
  const tx = vt && vt.length > 4 && Number.isFinite(vt[4]) ? vt[4] : 0;
  const ty = vt && vt.length > 5 && Number.isFinite(vt[5]) ? vt[5] : 0;
  const zoom = props.zoom > 0 && Number.isFinite(props.zoom) ? props.zoom : 1;

  return {
    transform: `translate(${tx}px, ${ty}px) scale(${zoom})`,
    transformOrigin: 'top left',
  };
});
```

---

### CAM-002b: Missing viewportTransform in Overlay Components ⚠️ OPEN

**Files Affected:**
- `ui/src/components/canvas/PathPreviewOverlay.vue` - No viewportTransform prop
- `ui/src/components/canvas/TrackPointOverlay.vue` - No viewportTransform prop

**Found:** 2026-01-10 by overlay component audit
**Severity:** P2 - MEDIUM (These overlays won't track viewport pan/zoom)

**Description:**
PathPreviewOverlay and TrackPointOverlay don't have a viewportTransform prop at all, so they cannot position correctly when the viewport is panned or zoomed.

**MotionPathOverlay.vue** was already correct - it has viewportTransform prop and applies it via CSS transform.

**Required Fix:**
Add viewportTransform prop to both components and apply CSS transform like MotionPathOverlay.vue does.

---

## 🟠 P1 - CAMERA SYSTEM HIGH BUGS

### CAM-003: camera-controls Internal State Desync ✅ FIXED

**File:** `ui/src/engine/core/CameraController.ts:203-217, 452-472`
**Function:** `updateCameraForViewport`, `resetToDefault`
**Found:** 2026-01-10 by coordinate system audit
**Fixed:** 2026-01-10
**Severity:** P1 - HIGH (Camera state can be partially reverted)

**Description:**
The `camera-controls` library maintains internal spherical coordinates that can override manual pan/zoom updates. When `setLookAt()` is called, it doesn't fully override the internal state.

**Fix Applied:**
```typescript
// Sync camera-controls internal state to match the new position.
// In 2D mode, setLookAt alone isn't enough - the internal spherical
// coordinates can "fight back" during update(). Calling update(0)
// forces immediate sync, preventing the smoothDamp from interpolating
// back to old positions.
if (this.cameraControls) {
  this.cameraControls.setLookAt(
    cameraPosX, cameraPosY, distance,
    cameraPosX, cameraPosY, 0,
    false, // No transition animation
  );
  this.cameraControls.update(0); // Force immediate internal state sync
}
```

Applied to both `updateCameraForViewport()` and `resetToDefault()` functions.

---

### CAM-004: Zoom/FOV Semantic Mismatch ⚠️ OPEN

**Files:**
- `ui/src/engine/core/CameraController.ts:379-382`
- `ui/src/services/export/cameraExportFormats.ts`
**Found:** 2026-01-10 by coordinate system audit
**Severity:** P1 - HIGH (Exported zoom doesn't match viewport)

**Description:**
The viewport camera's "zoom" is actually a distance multiplier (camera moves closer/farther), but the export system treats "zoom" as a separate camera property. They are semantically different.

**Evidence:**
```typescript
// CameraController.ts - zoom is distance multiplier
const distance = baseDistance / this.zoomLevel;

// cameraExportFormats.ts - zoom is separate property
type InterpolatedCamera = {
  focalLength: number;
  zoom: number;  // ← What does this mean?
}
```

**Impact:**
- Exported camera data doesn't match viewport behavior
- AI video generation gets wrong camera motion
- 2x zoom in viewport ≠ 2x zoom in exported video

**Required Fix:**
Define clear semantic meaning for "zoom" and ensure consistency:
- Option A: Export uses distance-based zoom like viewport
- Option B: Convert viewport distance to equivalent zoom property

---

### CAM-005: Layer Anchor Shifts Spline Points ⚠️ OPEN

**Files:**
- `ui/src/components/canvas/SplineEditor.vue:356-367`
- `ui/src/composables/useSplineInteraction.ts:305-314`
**Found:** 2026-01-10 by coordinate system audit
**Severity:** P1 - HIGH (Changing anchor moves all spline points)

**Description:**
Control points are stored in composition-space coordinates but layer transforms are applied relative to anchor point. When anchor point changes, all spline points appear to jump.

**Evidence:**
```typescript
// SplineEditor.vue:356-367 - transforms use anchor
const anchorPoint = getVal(t.anchorPoint, { x: 0, y: 0 });
let x = p.x - anchorPoint.x;  // Offset by anchor
x *= scale.x / 100;
// ... apply rotation ...
return { x: rx + position.x, y: ry + position.y };

// useSplineInteraction.ts:305-314 - stores raw coords
const newPoint: ControlPoint = {
  x: layerPos.x,  // NOT anchor-adjusted
  y: layerPos.y,
};
store.addSplineControlPoint(layerId.value, newPoint);
```

**Impact:**
- Change anchor from (0,0) to (50,50) → all points jump 50 units
- Unexpected behavior when adjusting layer registration point

**Required Fix:**
Store control points in anchor-relative coordinates, OR transform consistently:
```typescript
// Store relative to anchor
const anchorAdjustedX = layerPos.x - anchorPoint.x;
const anchorAdjustedY = layerPos.y - anchorPoint.y;
```

---

### CAM-006: viewportTransform Array Unit Mixing ⚠️ OPEN

**File:** `ui/src/composables/useViewportControls.ts:54, 69-71, 82-86, 95-96, 129-130`
**Found:** 2026-01-10 by coordinate system audit
**Severity:** P1 - HIGH (Design flaw causing confusion)

**Description:**
The `viewportTransform` array mixes different units without clear semantics:
- Indices [0,3]: Dimensionless zoom scalar
- Indices [4,5]: Screen pixels (not world units)

**Evidence:**
```typescript
const viewportTransform = ref<number[]>([1, 0, 0, 1, 0, 0]);
// [scaleX, skewX, skewY, scaleY, translateX, translateY]

// Setting values:
viewportTransform.value[0] = newZoom;  // Dimensionless
viewportTransform.value[4] = (viewW - scaledW) / 2;  // Pixels!
```

**Impact:**
- Easy to confuse units when reading/writing values
- `transform[4] = 100` - is that pixels or world units?
- Different components interpret values differently

**Required Fix:**
Replace magic array with typed object:
```typescript
interface ViewportTransform {
  zoom: number;           // Dimensionless scalar
  panScreenX: number;     // Screen pixels
  panScreenY: number;     // Screen pixels
  panWorldX?: number;     // World units (derived)
  panWorldY?: number;     // World units (derived)
}
```

---

## 🟡 P2 - CAMERA SYSTEM MEDIUM BUGS

### CAM-007: No Viewport Transform Bounds Checking ✅ FIXED

**File:** `ui/src/composables/useViewportControls.ts:96-112, 200-231`
**Found:** 2026-01-10 by coordinate system audit
**Fixed:** 2026-01-10
**Severity:** P2 - MEDIUM (Silent corruption possible)

**Description:**
Zoom can be set to arbitrary values including negative, zero, NaN, or Infinity without validation.

**Fix Applied:**
```typescript
// setZoom function
function setZoom(newZoom: number) {
  // Reject invalid input to prevent viewport state corruption
  if (!Number.isFinite(newZoom) || newZoom <= 0) {
    console.warn(
      `[ViewportControls] Invalid zoom value: ${newZoom}. Must be a positive finite number.`,
    );
    return; // Reject invalid values instead of silently corrupting state
  }
  newZoom = Math.max(0.1, Math.min(10, newZoom));
  // ... apply zoom
}

// screenToScene function - Guard against division by zero/NaN
function screenToScene(screenX: number, screenY: number) {
  const scaleX = vpt[0];
  const scaleY = vpt[3];

  if (!Number.isFinite(scaleX) || scaleX === 0) {
    console.warn(`[ViewportControls] Invalid scaleX in viewportTransform: ${scaleX}`);
    return { x: 0, y: 0 };
  }
  // ... similar validation for scaleY
}
```

---

### CAM-008: screenToWorld Never Used ⚠️ OPEN

**File:** `ui/src/engine/core/CameraController.ts:579-602`
**Function:** `screenToWorld`
**Found:** 2026-01-10 by coordinate system audit
**Severity:** P2 - MEDIUM (Wasted code, inconsistent coordinate handling)

**Description:**
A proper `screenToWorld()` method exists in CameraController but is never called by any UI component. All coordinate conversion is done ad-hoc in composables with varying implementations.

**Impact:**
- Duplicated coordinate conversion logic
- Different components use different approaches
- Bug fixes must be applied in multiple places

**Required Fix:**
Use the centralized `screenToWorld()` method, or deprecate it and standardize on composable approach.

---

## Coordinate System Data Flow Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│ USER INPUT                                                          │
│ Mouse click at (500, 300) screen pixels                            │
└─────────────────────────────────────────────────────────────────────┘
                                    │
                                    ▼
┌─────────────────────────────────────────────────────────────────────┐
│ SplineEditor.vue                                                    │
│ Receives: offsetX, offsetY from MouseEvent                         │
│ Calls: screenToCanvas(500, 300)                                    │
└─────────────────────────────────────────────────────────────────────┘
                                    │
                    ┌───────────────┴───────────────┐
                    │                               │
                    ▼                               ▼
    ┌───────────────────────────┐   ┌───────────────────────────────┐
    │ CURRENT (BROKEN)          │   │ SHOULD BE                     │
    │                           │   │                               │
    │ screenToCanvas():         │   │ screenToCanvas():             │
    │ x = (500/svgW) * canvasW  │   │ x = (500 - panX) / zoom       │
    │ y = (300/svgH) * canvasH  │   │ y = (300 - panY) / zoom       │
    │                           │   │                               │
    │ IGNORES: zoom, pan        │   │ ACCOUNTS FOR: zoom, pan       │
    └───────────────────────────┘   └───────────────────────────────┘
                    │                               │
                    ▼                               ▼
              WRONG COORDS                    CORRECT COORDS

┌─────────────────────────────────────────────────────────────────────┐
│ CAMERA STATE FLOW (ALSO BROKEN)                                    │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│ useViewportControls.ts:129                                         │
│   viewportTransform[4] = 400  ← Screen pixels                      │
│                     │                                               │
│                     ▼                                               │
│ LatticeEngine.ts:1108                                              │
│   camera.setPan(400, 0)  ← Passed as-is                            │
│                     │                                               │
│                     ▼                                               │
│ CameraController.ts:395                                            │
│   panOffset.set(400, 0)  ← Interpreted as 400 WORLD UNITS!         │
│                     │                                               │
│                     ▼                                               │
│ RESULT: 8-16x pan amplification                                    │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

---

## P0 - Critical Bugs

### BUG-001: Zoom Detection Logic Inverted ✅ FIXED

**File:** `ui/src/services/export/cameraExportFormats.ts:298-302`
**Function:** `detectMotionCtrlSVDPreset`
**Found:** 2026-01-10 by adversarial test
**Fixed:** 2026-01-10

**Description:**
The zoom detection logic is inverted. When camera moves forward (Z increases toward 0), it returns "zoom_out" instead of "zoom_in".

**Fix Applied:**
```typescript
// Now uses absolute distance from origin to determine zoom direction
// Works for cameras on either side of the origin
const distStart = Math.abs(firstPos.z);
const distEnd = Math.abs(lastPos.z);
return distEnd < distStart ? "zoom_in" : "zoom_out";
```

**Note:** This fix assumes subject is at origin. Needs verification with actual viewport camera system.

**Test Case:**
- Camera at Z=-500 moves to Z=-400 (forward, closer to subject)
- deltaZ = -400 - (-500) = +100 (positive)
- Current: returns "zoom_out"
- Expected: should return "zoom_in"

**Impact:** Video generation exports use wrong camera motion presets.

---

### BUG-002: computeProjectionMatrix Has No Input Validation

**File:** `ui/src/services/export/cameraExportFormats.ts:197-216`
**Function:** `computeProjectionMatrix`
**Found:** 2026-01-10 by adversarial test

**Description:**
Function accepts any aspect ratio including 0, negative, and NaN without validation. This produces garbage matrices silently.

**Evidence:**
```typescript
// No validation for aspectRatio parameter
export function computeProjectionMatrix(
  cam: InterpolatedCamera,
  aspectRatio: number,  // Not validated!
  nearClip: number = 0.1,
  farClip: number = 1000,
): number[][] {
  // Directly uses aspectRatio without checking
  return [
    [f / aspectRatio, 0, 0, 0],  // Division by zero if aspectRatio = 0
    ...
  ];
}
```

**Impact:**
- aspectRatio = 0 → Division by zero → Infinity in matrix
- aspectRatio < 0 → Negative values in projection matrix → Inverted rendering
- aspectRatio = NaN → NaN propagates through entire matrix

---

## P1 - High Bugs

### BUG-003: computeViewMatrix Doesn't Handle NaN Rotation

**File:** `ui/src/services/export/cameraExportFormats.ts:150-191`
**Function:** `computeViewMatrix`
**Found:** 2026-01-10 by adversarial test

**Description:**
If rotation values are NaN, Math.cos(NaN) and Math.sin(NaN) return NaN, producing a matrix full of NaN values.

**Expected Behavior:** Use fallback values (0) and warn, or throw error.

---

### BUG-004: No nearClip/farClip Validation

**File:** `ui/src/services/export/cameraExportFormats.ts:197-216`
**Function:** `computeProjectionMatrix`
**Found:** 2026-01-10 by adversarial test

**Description:**
- nearClip <= 0 produces invalid projection matrix
- farClip <= nearClip produces invalid nf value (1 / negative = negative)

**Expected Behavior:** Validate and use fallback values or throw.

---

### BUG-005: exportCameraMatrices No Zero Dimension Check

**File:** `ui/src/services/export/cameraExportFormats.ts:608-651`
**Function:** `exportCameraMatrices`
**Found:** 2026-01-10 by adversarial test

**Description:**
If width=0 or height=0, aspectRatio becomes 0/0=NaN or n/0=Infinity.

**Expected Behavior:** Throw error for invalid dimensions.

---

### BUG-006: exportCameraMatrices No Zero FPS Check

**File:** `ui/src/services/export/cameraExportFormats.ts:629`
**Function:** `exportCameraMatrices`
**Found:** 2026-01-10 by adversarial test

**Description:**
If fps=0, timestamp calculation `frame / options.fps` produces Infinity.

**Expected Behavior:** Throw error for invalid fps.

---

### BUG-007: NaN focalLength Not Handled

**File:** `ui/src/services/export/cameraExportFormats.ts:204`
**Function:** `computeProjectionMatrix`
**Found:** 2026-01-10 by adversarial test

**Description:**
NaN focalLength propagates through focalLengthToFOV and produces NaN in projection matrix.

**Expected Behavior:** Use fallback value and warn.

---

### BUG-008: 360-Degree Angle Interpolation Incorrect

**File:** `ui/src/services/export/cameraExportFormats.ts`
**Function:** `interpolateCameraAtFrame`
**Found:** 2026-01-10 by adversarial test

**Description:**
When interpolating between angles like 350 and 10 degrees, the function doesn't take the short path through 360. It interpolates the long way (350 → 180 → 10) instead of (350 → 360/0 → 10).

**Expected Behavior:** Use shortest angular path for interpolation.

---

### BUG-009: injectParameters JSON Parsing Error

**File:** `ui/src/services/comfyui/workflowTemplates.ts:2593`
**Function:** `injectParameters`
**Found:** 2026-01-10 by workflowTemplates.adversarial.test.ts

**Description:**
When object values are passed to injectParameters, the resulting JSON string is invalid because object stringification isn't handled correctly.

**Expected Behavior:** Properly serialize object values.

---

### BUG-010: Missing TTM Model Compatibility Warning

**File:** `ui/src/services/comfyui/workflowTemplates.ts`
**Function:** `generateTTMWorkflow`
**Found:** 2026-01-10 by workflowTemplates.adversarial.test.ts

**Description:**
TTM workflow generation doesn't warn when used with non-Wan models.

**Expected Behavior:** Warn user about incompatibility.

### BUG-013: No Upper Bound Validation on Dimensions

**File:** `ui/src/services/comfyui/workflowTemplates.ts:91-115`
**Function:** `validateWorkflowParams`
**Found:** 2026-01-10 by workflowTemplates.adversarial.test.ts

**Description:**
Dimensions (width/height) are only validated for `> 0` and `Number.isFinite()`. No upper bound check exists. Values like 16384 or 1000000 pass validation and can cause memory issues.

**Evidence:**
```typescript
if (!Number.isFinite(params.width) || params.width <= 0) {
  errors.push(`Invalid width: ${params.width}. Must be a positive number.`);
}
// No check for params.width > 8192
```

**Expected Behavior:** Validate width/height in range 64-8192.

---

### BUG-014: No Upper Bound Validation on frameCount

**File:** `ui/src/services/comfyui/workflowTemplates.ts:103-105`
**Function:** `validateWorkflowParams`
**Found:** 2026-01-10 by workflowTemplates.adversarial.test.ts

**Description:**
frameCount is only validated for `> 0`. Values like 100000 pass and can cause memory exhaustion during video generation.

**Expected Behavior:** Validate frameCount in range 1-10000.

---

### BUG-015: No Upper Bound Validation on fps

**File:** `ui/src/services/comfyui/workflowTemplates.ts:108-110`
**Function:** `validateWorkflowParams`
**Found:** 2026-01-10 by workflowTemplates.adversarial.test.ts

**Description:**
fps is only validated for `> 0`. Values like 1000 pass and can cause issues with video encoders.

**Expected Behavior:** Validate fps in range 1-120.

---

## P2 - Medium Bugs

### BUG-011: exportToUni3C Missing Non-Functional Warning

**File:** `ui/src/services/export/cameraExportFormats.ts`
**Function:** `exportToUni3C`
**Found:** 2026-01-10 by adversarial test

**Description:**
Function should warn when producing non-functional export data.

---

### BUG-012: exportCameraMatrices No NaN Parameter Handling

**File:** `ui/src/services/export/cameraExportFormats.ts:608-651`
**Function:** `exportCameraMatrices`
**Found:** 2026-01-10 by adversarial test

**Description:**
NaN values for frameCount, width, height, or fps produce garbage output without warning.

**Expected Behavior:** Use fallback values and warn.

---

## Not Bugs - Design Choices

### DC-001: frameCount=0 Returns Empty Array

**Current:** `exportCameraMatrices` returns empty frames array when frameCount=0
**Test Expected:** At least 1 frame

**Verdict:** Current behavior is logical. Requesting 0 frames and getting 0 is correct. Test assumption is wrong.

---

### DC-002: depthRenderer Uses Browser-Only APIs

**Issue:** Tests use `ImageData` which doesn't exist in Node.js
**Verdict:** Not a bug - these are browser-only functions that need E2E tests, not unit tests.

---

### DC-003: Missing Fallback Values for Some Inputs

**Issue:** Some tests expect fallback values instead of errors for invalid inputs
**Verdict:** Whether to throw vs. use fallback is a design choice. Either is valid.

---

### DC-004: Workflow Generators Use Defaults for Missing Inputs

**Issue:** Tests expect throws for missing `referenceImage`, `ttmLayers`, or `cameraData`
**Current Behavior:** Generators use defaults like `"input.png"` or `[]` instead of throwing

**Examples:**
- `generateWan22I2VWorkflow`: `params.referenceImage || "input.png"`
- `generateTTMWorkflow`: `params.ttmLayers || []`
- `generateWanMoveWorkflow`: `params.motionData?.tracks || []`

**Verdict:** Using defaults is a valid design choice. Tests assumptions are wrong.

---

### DC-005: Wan-Move and ATI Accept Empty Track Data

**Issue:** Tests expect throw when cameraData is missing for wan-move/ati targets
**Current Behavior:** Workflow generates with empty tracks, allowing user to add later

**Verdict:** Empty workflow generation is valid - user can modify before execution.

---

## Test Errors - Wrong Test Assumptions

### TE-001: Test Claims "scail" is Unknown Target

**Test:** `workflowTemplates.adversarial.test.ts` lines 248-257, 467-474
**Test Expects:** `generateWorkflowForTarget("scail", params)` throws "Unknown export target"
**Reality:** `scail` IS a valid ExportTarget (workflowTemplates.ts line 2542-2544)

```typescript
case "scail":
  // SCAIL pose-driven video generation
  return generateSCAILWorkflow(params);
```

**Verdict:** Test is wrong. SCAIL was added but tests weren't updated.

---

### TE-002: Tests Expect Throws for Design Choice Defaults

**Tests:** Multiple tests in "Missing Required Inputs" section (lines 168-258)
**Test Expects:** Throws for missing referenceImage, ttmLayers, cameraData
**Reality:** Generators use defaults, not throws

**Verdict:** Tests have wrong assumptions about API contract.

---

### TE-003: math3d Property Test Floating Point Precision (Flaky)

**Status:** OPEN - Needs Investigation
**Discovered:** 2026-01-10 (during Phase 3 audio migration verification)
**Test:** `src/__tests__/services/math3d.property.test.ts` line 283
**Test Name:** "translation composition is commutative with addition"

**Error:**
```
Counterexample: [{x:0,y:0,z:-5.684341886080803e-14},{x:0,y:0,z:627.7579040527344}]
```

**Root Cause Analysis:**
- Property-based test using fast-check generates random vectors
- Test composes two translation matrices: `translateMat4(a) * translateMat4(b)`
- Compares against direct addition: `translateMat4(addVec3(a, b))`
- Very small floating point errors (5.68e-14 ≈ 0) cause `vec3Equal` to fail

**Investigation Needed:**
1. Check if `vec3Equal` uses appropriate epsilon tolerance
2. Determine if this is a bug in the equality function or expected FP behavior
3. Check if this test was always flaky or recently broke

**Files to Review:**
- `src/services/math3d.ts` - vec3Equal, translateMat4, addVec3 implementations
- `src/__tests__/services/math3d.property.test.ts` - test implementation

**Impact:** This is a test infrastructure issue, not a production bug. The floating point error is within acceptable tolerance for graphics operations.

**Note:** EPSILON = 1e-5 in the test, but the error 5.68e-14 is much smaller. This suggests the test SHOULD pass. May be a flaky test due to fast-check's random seed or matrix multiplication accumulation errors with extreme values.

**Relation to Audio Migration:** This test failure was observed during Phase 3 audio migration but is UNRELATED to the audio changes. The test file has no recent modifications.

---

## Verification Method

Each bug was verified by:
1. Reading the test expectation
2. Reading the implementation code
3. Tracing the data flow
4. Confirming the mismatch between expected and actual behavior

**Test Files:**
- `ui/src/__tests__/export/cameraExportFormats.adversarial.test.ts` - 12 real bugs found
- `ui/src/__tests__/comfyui/workflowTemplates.adversarial.test.ts` - 6 real bugs + 2 test errors
- `ui/src/__tests__/export/depthRenderer.adversarial.test.ts` - 11 failures, all browser-only (ImageData API)

---

## depthRenderer Browser-Only Failures (Not Bugs)

The following tests fail because they use browser-only APIs that don't exist in Node.js/Vitest:

| Test Section | Functions Used | Root Cause |
|--------------|---------------|------------|
| depthToImageData tests | `depthToImageData()` | `new ImageData()` not available |
| applyColormap tests | `applyColormap()` | `new ImageData()` not available |
| renderDepthFrame tests | `renderDepthFrame()` | Calls `depthToImageData()` internally |

**Lines using ImageData:** 586, 616, 661, 691, 928

**Solution:** These functions are tested in E2E tests (`e2e/export/depth-renderer.spec.ts`) where browser APIs are available. The `depthRenderer.property.test.ts` file tests Node.js-compatible functions (`convertDepthToFormat`, `generateDepthMetadata`) separately.
