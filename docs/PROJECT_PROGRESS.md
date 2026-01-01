# Lattice Compositor - Project Progress & Testing Checklist

> Last updated: 2026-01-01

## Overview

This document tracks the overall project status, feature testing checklists, and known issues for the Lattice Compositor.

---

## PHASE 1: FOUNDATION

### Security Hardening
- [x] Expression sandbox (SES/Compartment) - 86 tests passing
- [x] URL validation service - 37 tests passing
- [x] JSON sanitization service - 37 tests passing
- [x] Template signature verification - 16 tests passing
- [x] Prompt injection defense (boundary tags)
- [x] Rate limiting service (implemented, no tests)
- [x] Audit logging service (implemented, no tests)

### CI/CD Pipeline
- [x] GitHub Actions workflow created
- [x] Lint and typecheck job
- [x] Unit test job (Vitest)
- [x] Build job
- [x] Security audit job (PRs only)

### Error Tracking
- [ ] Sentry/error tracking integration
- [ ] Error boundary components
- [ ] Crash reporting

### E2E Test Infrastructure
- [x] Playwright installed
- [x] Playwright config created
- [x] Basic smoke tests written
- [ ] ComfyUI integration tests
- [ ] Full user workflow tests

---

## P0 SHIP-STOPPER FIXES (CTO Review Remediation)

> See `GroundTruthMasterAudit.md` for full details

### P0.1 - Backend Routes Not Registered ✅ COMPLETE (2026-01-01)

**Problem:** Package root only imported `compositor_node.py`, so route modules never loaded.

**Fix:**
- `__init__.py` now imports from `.nodes` and calls `register_all_routes()`
- `nodes/__init__.py` contains explicit `register_all_routes()` function
- All 7 route modules imported and 47 routes registered

**Verification:**
- 10 integration tests in `tests/test_route_registration.py`
- All tests verify routes appear in MockRouteTable
- UI test baseline maintained (252 failed | 803 passed)

### P0.2 - Vectorize Routes Never Called ✅ COMPLETE (2026-01-01)

**Problem:** `lattice_vectorize.py` used `setup_routes(app)` pattern but nothing called it.

**Fix:**
- Converted to `@routes.get/post` decorator pattern
- Deleted `setup_routes()` function
- Routes now register at import time like other modules

**Verification:**
- 5 vectorize routes verified in integration tests
- No `setup_routes()` function remains

### P0.3 - Opacity Range Mismatch ☐ NOT STARTED

**Problem:** Backend validates opacity as 0-1, frontend uses 0-100.

### P0.4 - Node Output Shape Wrong ☐ NOT STARTED

**Problem:** CompositorEditorNode likely returns wrong IMAGE tensor shape.

### P0.5 - Duplicate AI APIs ☐ NOT STARTED

**Problem:** Two separate AI service implementations need unification.

---

## PHASE 2: CORE FUNCTIONALITY AUDIT

### Layer Types (26 total)

Each layer type needs these tests verified:

| Layer Type | Create | Select | Delete | Properties | Timeline | Renders |
|------------|--------|--------|--------|------------|----------|---------|
| `image` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `video` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `audio` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `text` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `solid` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `shape` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `spline` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `path` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `control` (null) | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `camera` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `light` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `particle` (legacy) | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `particles` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `group` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `nestedComp` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `depth` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `normal` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `depthflow` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `generated` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `matte` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `effect` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `adjustment` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `model` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `pointcloud` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `pose` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |
| `mask` | [ ] | [ ] | [ ] | [ ] | [ ] | [ ] |

### Toolbar Tools

| Tool | Activates | Canvas Interaction | Keyboard Shortcut |
|------|-----------|-------------------|-------------------|
| Select (V) | [ ] | [ ] | [ ] |
| Pen (G) | [ ] | [ ] | [ ] |
| Text (T) | [ ] | [ ] | [ ] |
| Hand/Pan (H) | [ ] | [ ] | [ ] |
| Zoom (Z) | [ ] | [ ] | [ ] |
| Segment | [ ] | [ ] | [ ] |
| Rectangle | [ ] | [ ] | [ ] |
| Ellipse | [ ] | [ ] | [ ] |
| Polygon | [ ] | [ ] | [ ] |
| Star | [ ] | [ ] | [ ] |

### Timeline Features

| Feature | Works | Notes |
|---------|-------|-------|
| Play/Pause | [ ] | |
| Stop | [ ] | |
| Frame scrubbing | [ ] | |
| Go to start | [ ] | |
| Go to end | [ ] | |
| Set work area | [ ] | |
| Loop playback | [ ] | |
| Layer visibility toggle | [ ] | |
| Layer lock toggle | [ ] | |
| Layer solo | [ ] | |
| Layer reorder (drag) | [ ] | |
| Layer trim (drag ends) | [ ] | |
| Layer slip (drag middle) | [ ] | |

### Keyframe Operations

| Operation | Works | Notes |
|-----------|-------|-------|
| Add keyframe | [ ] | |
| Delete keyframe | [ ] | |
| Move keyframe | [ ] | |
| Copy/paste keyframes | [ ] | |
| Select multiple keyframes | [ ] | |
| Keyframe interpolation types | [ ] | |
| Graph editor display | [ ] | |
| Bezier handle editing | [ ] | |
| Easy ease | [ ] | |

### Export Features

| Feature | Works | Notes |
|---------|-------|-------|
| Export button accessible | [ ] | |
| MP4 export | [ ] | |
| WebM export | [ ] | |
| GIF export | [ ] | |
| Image sequence export | [ ] | |
| Frame range selection | [ ] | |
| Resolution options | [ ] | |
| Quality settings | [ ] | |

---

## PHASE 3: KNOWN BUGS

### Active Bugs

| ID | Description | Severity | Component | Status | Notes |
|----|-------------|----------|-----------|--------|-------|
| UI-001 | Viewport not centered in composition panel | Minor | CenterViewport.vue | Open | CSS flexbox added, may need camera centering fix |
| UI-002 | Responsive layout issues on small screens | Minor | WorkspaceLayout.vue | Open | Splitpane minimum sizes |
| UI-003 | Sidebar tab not appearing in some ComfyUI versions | Major | extension.js | Fixed | Added extensionManager guard |
| CAM-001 | MotionPathOverlay wrong transform indices | Minor | MotionPathOverlay.vue:304-305 | Open | Uses [0,1] not [4,5] for translate |
| CAM-002 | Solid layer wrong anchor point | Minor | SolidLayer | Open | Positioning incorrect |

### Fixed Bugs (Recent)

| ID | Description | Severity | Fixed Date | Notes |
|----|-------------|----------|------------|-------|
| CAM-003 | Zoom not working (camera-controls reverts) | Major | 2025-12-29 | Added setLookAt() sync in CameraController.ts:431 |
| CAM-004 | Pan not updating screenToScene coordinates | Major | 2025-12-29 | Added viewportTransform[4,5] update in ThreeCanvas.vue:1163 |
| SEC-001 | SES lockdown breaks Vue/Three.js | Critical | 2025-12-29 | Disabled main thread lockdown, worker-only sandbox |
| BUG-176 | Division by zero in periodic() | Medium | 2025-12-28 | expressionEvaluator.ts |
| BUG-177 | NaN propagation in wave functions | Medium | 2025-12-28 | sawtooth, triangle, square |
| BUG-178 | NaN bypasses clamp in smoothstep() | Medium | 2025-12-28 | |
| BUG-179 | NaN bypasses clamp in smootherstep() | Medium | 2025-12-28 | |
| BUG-180 | Division by zero in mod() | Medium | 2025-12-28 | |
| BUG-181 | Math.max NaN bypass in gaussRandom() | Medium | 2025-12-28 | |
| BUG-182 | NaN bypass in expressionEase() | Medium | 2025-12-28 | |
| BUG-183 | NaN bypass in expressionEaseIn() | Medium | 2025-12-28 | |
| BUG-184 | NaN bypass in expressionEaseOut() | Medium | 2025-12-28 | |
| BUG-185 | Division by fps in createThisCompObject() | Medium | 2025-12-28 | |
| BUG-186 | No input validation in easing functions | Medium | 2025-12-28 | All 30+ easing functions |

### Code Quality Issues Found

| Type | Count | Notes |
|------|-------|-------|
| TODO comments | ~5 | Mostly in test files |
| FIXME comments | 0 | |
| BUG comments | ~50 | Mostly fixed bugs with tracking IDs |
| NaN guards added | ~30 | Number.isFinite validation throughout |

---

## PHASE 4: BETA READY CHECKLIST

### Performance

- [ ] Baseline render performance measured
- [ ] Memory usage profiled
- [ ] 60fps playback verified for standard compositions
- [ ] Large composition stress test (100+ layers)
- [ ] Long video handling (10+ minutes)

### Stability

- [ ] No crashes in 1-hour continuous use
- [ ] Undo/redo works for all operations
- [ ] Auto-save implemented
- [ ] Project recovery from crash

### Error Handling

- [ ] All user-facing errors have clear messages
- [ ] Network failures handled gracefully
- [ ] Invalid file imports show helpful errors
- [ ] Expression errors don't crash compositor

### Documentation

- [ ] User guide complete
- [ ] Keyboard shortcuts documented
- [ ] Tutorial workflows verified (20 workflows)
- [ ] API documentation for effects

### Tutorial Workflows Verification

| # | Tutorial | Status | Notes |
|---|----------|--------|-------|
| 1 | Basic layer creation | [ ] | |
| 2 | Text animation | [ ] | |
| 3 | Keyframe basics | [ ] | |
| 4 | Shape animation | [ ] | |
| 5 | Motion paths | [ ] | |
| 6 | Text animators | [ ] | |
| 7 | Particle effects | [ ] | |
| 8 | Camera animation | [ ] | |
| 9 | Masking | [ ] | |
| 10 | Expressions basics | [ ] | |
| 11 | Audio reactive | [ ] | |
| 12 | Depth effects | [ ] | |
| 13 | 3D layers | [ ] | |
| 14 | Nested compositions | [ ] | |
| 15 | Export workflow | [ ] | |
| 16 | ControlNet export | [ ] | |
| 17 | Pose detection | [ ] | |
| 18 | Color correction | [ ] | |
| 19 | Blend modes | [ ] | |
| 20 | Project organization | [ ] | |

---

## Test Coverage Summary

### Unit Tests (Vitest)

| Category | Files | Tests | Passing |
|----------|-------|-------|---------|
| Security | 4 | 176 | 176 |
| Services | 10 | ~150 | ~150 |
| Integration | 2 | ~50 | ~50 |
| Types | 2 | ~8 | ~8 |
| **Total** | **21** | **~384** | **~384** |

### E2E Tests (Playwright)

| Test Suite | Tests | Status |
|------------|-------|--------|
| Smoke tests | 3 | Written |
| ComfyUI integration | 0 | Not started |
| Full workflows | 0 | Not started |

---

## Files Needing Attention

Based on code analysis, these areas need review:

### High Priority
- `ui/src/services/expressions/` - Security critical, 1/17 files audited
- `ui/src/services/effects/` - Canvas/WebGL corruption risk
- `ui/src/stores/actions/` - State mutation logic

### Medium Priority
- `ui/src/engine/` - Render pipeline, 60 files
- `ui/src/components/` - Memory leaks, 160 files

### Low Priority
- `ui/src/types/` - Type definitions, usually clean
- `ui/src/composables/` - Vue reactive state

---

## Session Notes

### 2026-01-01 - P0.1 & P0.2 Complete

**CTO Review Remediation - Route Registration System**

Completed fixes for P0.1 (Backend Routes Not Registered) and P0.2 (Vectorize Routes Never Called).

**Files Modified:**
| File | Change |
|------|--------|
| `__init__.py` | Import from `.nodes`, call `register_all_routes()` |
| `nodes/__init__.py` | Created `register_all_routes()` function |
| `nodes/lattice_vectorize.py` | Converted `setup_routes()` to decorator pattern |
| `tests/test_route_registration.py` | Created 10 integration tests |

**Test Results:**
- Route registration tests: 10/10 pass
- UI test baseline: 252 failed | 803 passed (no regression)
- 47 routes verified across 7 modules

**Documentation Updated:**
- `GroundTruthMasterAudit.md` - Added completion evidence (sections 4.1.11, 4.2.8)
- `CLAUDE.md` - Added CURRENT STATUS section
- `docs/PROJECT_PROGRESS.md` - Added P0 fixes section

---

### 2025-12-29 (Late Session) - Current: ae6e6904

**SES Lockdown Investigation & Resolution:**
- SES lockdown with `overrideTaming: 'severe'` broke Vue/Three.js
- Error: "Cannot assign to read only property 'next' of object '[object Array Iterator]'"
- Tried `overrideTaming: 'moderate'` - still broke
- **FINAL FIX:** Disabled main thread lockdown entirely, expressions run in isolated worker only
- Worker has its own SES sandbox with 100ms timeout
- Main thread never executes expressions, so this is secure

**Camera System Deep Dive:**
- Diagnosed why zoom/pan weren't working
- **Root cause 1:** `camera-controls` library maintains internal state
- When we set `camera.position` directly, `cameraControls.update()` in render loop reverts it
- **Fix:** Added `setLookAt()` sync after direct camera updates (CameraController.ts:431)

- **Root cause 2:** `viewportTransform[4,5]` (pan offsets) never updated during pan
- `screenToScene()` uses viewportTransform for 2D coordinate conversion
- **Fix:** Added `viewportTransform.value[4] += dx` during pan (ThreeCanvas.vue:1163)

**Coordinate System Architecture Documented:**
- Two systems: 2D affine `viewportTransform` for overlays, 3D camera for WebGL
- viewportTransform format: `[scaleX, skewX, skewY, scaleY, translateX, translateY]`
- `screenToScene()` - 2D affine inverse (for layer placement)
- `screenToWorld()` - 3D ray unprojection (currently unused)

**Bug Found (not yet fixed):**
- MotionPathOverlay.vue:304-305 uses wrong indices `[0,1]` instead of `[4,5]`
- This means motion path overlay won't track panning correctly

**Many Reverts:**
- Multiple commit/revert cycles during SES debugging
- Final stable state: ae6e6904

### 2025-12-29 (Earlier)
- Created PROJECT_PROGRESS.md
- Security hardening complete (Phase 1)
- CI pipeline operational
- E2E infrastructure in place
- Viewport centering fix attempted (CSS)
- Extension.js guarded for ComfyUI compatibility

### Previous Sessions
- See AUDIT/PROGRESS.md for detailed bug fix history
- See AUDIT/BUGS.md for full bug registry
