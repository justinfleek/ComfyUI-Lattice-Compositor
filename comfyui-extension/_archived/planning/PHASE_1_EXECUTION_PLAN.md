# PHASE 1 EXECUTION PLAN: Export System Stabilization

> **Created:** 2026-01-11
> **Status:** IN PROGRESS
> **Blocking:** All subsequent phases depend on this completing successfully

---

## EXECUTIVE SUMMARY

**Goal:** Wire new Kijai-compatible export functions to all call sites, deprecate old functions, achieve 100% test pass rate.

**Current State:**
- Tests: 5010 passed, 1 failed (GPU particle bug - REAL BUG, see analysis), 14 skipped
- New export functions created but NOT wired to unified export system
- Old broken functions still in use internally
- Dual export paths coexist (confusion risk)
- **No external Python consumers** (verified via grep)

**Definition of Done:**
- [ ] All tests pass (100%)
- [ ] New functions used in all export paths
- [ ] Old functions marked @deprecated with migration notes
- [ ] No breaking changes to existing call sites
- [ ] CI can verify completion

---

## PART 1: CURRENT ARCHITECTURE

### 1.1 Export System Structure

```
services/
├── modelExport.ts           # Unified export orchestrator (OLD functions)
│   ├── exportForModel()     # Main entry point
│   ├── exportCameraTrajectory()      # ❌ OLD - wrong format
│   ├── exportWanMoveTrajectories()   # ❌ OLD - wrong format
│   └── exportATITrajectory()         # ❌ OLD - wrong format
│
└── export/
    ├── index.ts             # Re-exports everything
    ├── wanMoveExport.ts     # ✅ NEW - exportAsKijaiWanMoveJSON()
    ├── atiExport.ts         # ✅ NEW - exportAsKijaiATI()
    ├── cameraExportFormats.ts # ✅ NEW - exportAsCameraCtrlPoses()
    └── ...
```

### 1.2 Function Mapping

| Target | Old Function (BROKEN) | New Function (CORRECT) | Status |
|--------|----------------------|------------------------|--------|
| wan-move | `exportWanMoveTrajectories()` | `exportAsKijaiWanMoveJSON()` | 🔴 Not wired |
| ati | `exportATITrajectory()` | `exportAsKijaiATI()` | 🔴 Not wired |
| camera-comfyui | `exportCameraTrajectory()` | `exportAsCameraCtrlPoses()` | 🔴 Not wired |
| motionctrl | `exportToMotionCtrl()` | (same - already correct) | ✅ OK |
| uni3c | `exportToUni3C()` | N/A (deprecated) | ✅ Deprecated |

### 1.3 Call Sites to Update

**modelExport.ts:**
- Line 842: `exportCameraTrajectory()` → Need CameraCtrl format option
- Line 878: `exportWanMoveTrajectories()` → Use `exportAsKijaiWanMoveJSON()`
- Line 923: `exportATITrajectory()` → Use `exportAsKijaiATI()`
- Line 930: `exportCameraTrajectory()` → (internal use, keep)
- Line 1061: `exportCameraTrajectory()` → (light-x, may keep)
- Line 1118: `exportWanMoveTrajectories()` → Use `exportAsKijaiWanMoveJSON()`

### 1.4 External Consumer Check

```bash
# Verified: No Python consumers of old export functions
grep -r "exportWanMoveTrajectories\|exportATITrajectory\|exportCameraTrajectory" \
  --include="*.py" ../ 2>/dev/null
# Result: No matches - safe to deprecate
```

---

## PART 2: BUG ANALYSIS - GPU Particle Spawn Rate (BUG-099)

### 2.1 Test Failure Details

**File:** `src/__tests__/engine/particles/GPUParticleSystem.property.test.ts:586-610`
**Counterexample:** `dt=7.83s, emissionRate=20911`
**Expected:** Complete in <2000ms, spawn ≤10000 particles
**Actual:** Took 19118ms (19 seconds)

### 2.2 Root Cause Analysis

**THIS IS A REAL BUG, NOT A WRONG TEST EXPECTATION.**

The spawn rate cap (10000 per frame) is correctly implemented:

```typescript
// emitParticles() at line 1215-1221 - CORRECT
const MAX_SPAWN_PER_FRAME = 10000;
let spawned = 0;
while (emitter.accumulator >= 1 && spawned < MAX_SPAWN_PER_FRAME) {
  this.spawnParticle(emitter);
  emitter.accumulator -= 1;
  spawned++;
}
```

**But `spawnParticle()` has an O(N) recycling scan when the pool is full:**

```typescript
// spawnParticle() at line 1233-1250 - BUG: O(N) per call
if (this.freeIndices.length === 0) {
  // Find oldest particle to recycle - scans ALL particles!
  for (let i = 0; i < this.config.maxParticles; i++) {  // <-- O(N)
    const age = buffer[i * PARTICLE_STRIDE + 6];
    if (age > oldestAge) { ... }
  }
}
```

### 2.3 Complexity Analysis

With test parameters:
- `maxParticles = 15000`
- `emissionRate = 20911`
- `dt = 7.83s`

Timeline:
1. `accumulator = 20911 × 7.83 = 163,729` particles requested
2. First ~15000 spawns fill the pool (O(1) each)
3. Remaining spawns (capped at 10000) each trigger O(15000) scan
4. **Total: ~10000 × 15000 = 150 MILLION loop iterations**

This explains the 19-second runtime.

### 2.4 Fix: Option A - Cap Recycle Attempts Per Frame

**Decision:** Cap recycle scans at 100 per frame. This preserves recycling behavior for normal use while preventing O(N²) collapse during browser pause scenarios.

**Rationale:**
- Recycling oldest particles is intentional for visual continuity
- 100 recycles per frame is plenty for normal 60fps operation
- Prevents pathological case when dt is large (browser pause)

---

## PART 3: EXECUTION STEPS

### Step 1: Fix GPU Particle Spawn Bug (BUG-099) ✅ COMPLETE

**File:** `src/engine/particles/GPUParticleSystem.ts`
**Fix:** Cap recycle scan attempts at 100 per frame

**Checkpoint:** `npm test -- --run src/__tests__/engine/particles/GPUParticleSystem.property.test.ts` passes

---

### Step 2: Add Deprecation Warnings to Old Functions

**File:** `src/services/modelExport.ts`

**Functions to deprecate:**

```typescript
/**
 * @deprecated Use exportAsKijaiWanMoveJSON() from '@/services/export/wanMoveExport' instead.
 * This function produces incorrect output format for Kijai's WanVideoWrapper.
 *
 * Migration:
 * 1. Import { exportAsKijaiWanMoveJSON, type WanMoveTrajectory } from '@/services/export'
 * 2. Convert PointTrajectory[] to WanMoveTrajectory using createWanMoveTrajectory()
 * 3. Call exportAsKijaiWanMoveJSON(trajectory)
 *
 * @see https://github.com/kijai/ComfyUI-WanVideoWrapper/blob/main/WanMove/nodes.py
 */
export function exportWanMoveTrajectories(...) { ... }

/**
 * @deprecated Use exportAsKijaiATI() from '@/services/export/atiExport' instead.
 * This function produces incorrect ATI format. Kijai expects exactly 121 frames
 * with pixel coordinates (normalization done by process_tracks internally).
 *
 * Migration:
 * 1. Import { exportAsKijaiATI, createATITrajectory } from '@/services/export'
 * 2. Convert your trajectory to WanMoveTrajectory format
 * 3. Call exportAsKijaiATI(trajectory)
 *
 * @see https://github.com/kijai/ComfyUI-WanVideoWrapper/blob/main/ATI/nodes.py
 */
export function exportATITrajectory(...) { ... }

/**
 * @deprecated For Kijai CameraCtrl format, use exportAsCameraCtrlPoses() from
 * '@/services/export/cameraExportFormats' instead.
 *
 * This function outputs generic 4x4 matrices. For ComfyUI integration, use the
 * specific format functions in cameraExportFormats.ts.
 *
 * Migration:
 * 1. Import { exportAsCameraCtrlPoses } from '@/services/export'
 * 2. Call exportAsCameraCtrlPoses(cameras, width, height, fps)
 */
export function exportCameraTrajectory(...) { ... }
```

**Checkpoint:** `npx tsc --noEmit` compiles; deprecation warnings appear in IDE

---

### Step 3: Create Adapter Layer

**File:** `src/services/export/legacyAdapters.ts` (NEW)

**Purpose:** Bridge old signatures to new implementations for gradual migration.

```typescript
/**
 * Legacy Export Adapters
 *
 * These functions wrap new Kijai-compatible implementations with old signatures.
 * Use during migration only - will be deprecated after all call sites updated.
 *
 * @deprecated This entire module will be removed after migration complete.
 */

import {
  exportAsKijaiWanMoveJSON,
  type WanMoveTrajectory
} from './wanMoveExport';
import {
  exportAsKijaiATI,
  ATI_FIXED_FRAMES
} from './atiExport';
import type { PointTrajectory } from '../modelExport';

/**
 * Convert old PointTrajectory[] format to new WanMoveTrajectory format
 *
 * NOTE: Output uses {x, y} objects per Kijai spec, NOT [x, y] arrays
 */
export function convertPointTrajectoriesToWanMove(
  trajectories: PointTrajectory[],
  width: number,
  height: number,
  fps: number = 16
): WanMoveTrajectory {
  const numFrames = trajectories[0]?.points.length ?? 0;

  return {
    // Internal format uses [x, y] arrays; exportAsKijaiWanMoveJSON converts to {x, y}
    tracks: trajectories.map(t =>
      t.points.map(p => [p.x, p.y])
    ),
    visibility: trajectories.map(t => t.points.map(() => true)),
    metadata: {
      numPoints: trajectories.length,
      numFrames,
      width,
      height,
      fps,
    },
  };
}

/**
 * Adapter: Old WanMove signature → New Kijai format
 *
 * Returns JSON string with [[{x, y}, ...], ...] format per Kijai spec
 */
export function legacyWanMoveExport(
  trajectories: PointTrajectory[],
  width: number,
  height: number,
  fps: number = 16
): string {
  const converted = convertPointTrajectoriesToWanMove(trajectories, width, height, fps);
  return exportAsKijaiWanMoveJSON(converted);
}

/**
 * Adapter: Old ATI signature → New Kijai format
 *
 * Returns JSON string with [[{x, y}, ...], ...] format, padded to 121 frames
 */
export function legacyATIExport(
  trajectory: PointTrajectory,
  width: number,
  height: number
): string {
  const wanMove = convertPointTrajectoriesToWanMove([trajectory], width, height);
  return exportAsKijaiATI(wanMove);
}
```

**CRITICAL:** The `exportAsKijaiWanMoveJSON()` function in `wanMoveExport.ts` must output `{x, y}` objects:
```typescript
// In wanMoveExport.ts - verify this format:
return JSON.stringify(
  tracks.map(track =>
    track.map(([x, y]) => ({ x, y }))  // Convert to {x, y} objects
  )
);
```

**Checkpoint:** Adapters compile and type-check

---

### Step 4: Wire Unified Export to New Functions

**File:** `src/services/modelExport.ts`

**Add imports at TOP of file:**
```typescript
// At top of modelExport.ts, with other imports
import {
  legacyWanMoveExport,
  legacyATIExport,
  convertPointTrajectoriesToWanMove,
} from './export/legacyAdapters';
import { exportAsCameraCtrlPosesText } from './export/cameraExportFormats';
```

**Changes to `exportForModel()` switch cases:**

**4a. wan-move case (line 862-907):**
```typescript
case "wan-move": {
  const trajectories: PointTrajectory[] = [];
  for (const layer of layers) {
    if (layer.transform.position.animated) {
      trajectories.push(extractLayerTrajectory(...));
    }
  }

  // Use new Kijai-compatible format
  const jsonString = legacyWanMoveExport(trajectories, compWidth, compHeight, fps);

  return {
    success: true,
    target,
    data: { tracks: jsonString },
    files: [{
      name: "track_coords.json",  // Kijai expects this name
      content: jsonString,
      type: "json",
    }],
  };
}
```

**4b. ati case (line 910-953):**
```typescript
case "ati": {
  const atiTracks: string[] = [];
  for (const layer of layers) {
    if (layer.transform.position.animated) {
      const trajectory = extractLayerTrajectory(...);
      atiTracks.push(legacyATIExport(trajectory, compWidth, compHeight));
    }
  }

  // Combine all tracks into single JSON array
  const combinedTracks = atiTracks.map(t => JSON.parse(t)).flat();

  return {
    success: true,
    target,
    data: combinedTracks,
    files: [{
      name: "ati_track_coords.json",
      content: JSON.stringify(combinedTracks),
      type: "json",
    }],
  };
}
```

**4c. Add camera-ctrl target (new case):**
```typescript
case "camera-ctrl": {
  const posesText = exportAsCameraCtrlPosesText(cameras, compWidth, compHeight, fps);

  return {
    success: true,
    target,
    data: { poses: posesText },
    files: [{
      name: "camera_poses.txt",
      content: posesText,
      type: "txt",
    }],
  };
}
```

**Checkpoint:** All export targets produce Kijai-compatible output

---

### Step 5: Update Tests

**Files to update:**
- `src/__tests__/export/modelExport.test.ts` - Update old function tests

**New tests to add:**
```typescript
describe('Kijai WanVideoWrapper Compatibility', () => {
  it('wan-move exportForModel produces Kijai-compatible JSON', async () => {
    const result = await exportForModel({ target: 'wan-move', ... });
    const parsed = JSON.parse(result.files[0].content);

    // Verify format: [[{x, y}, ...], ...]
    expect(Array.isArray(parsed)).toBe(true);
    expect(parsed[0][0]).toHaveProperty('x');
    expect(parsed[0][0]).toHaveProperty('y');
    // NOT arrays:
    expect(Array.isArray(parsed[0][0])).toBe(false);
  });

  it('ati exportForModel produces exactly 121 frames', async () => {
    const result = await exportForModel({ target: 'ati', ... });
    const parsed = JSON.parse(result.files[0].content);

    expect(parsed[0].length).toBe(121);
  });

  it('camera-ctrl exportForModel produces CameraCtrl format', async () => {
    const result = await exportForModel({ target: 'camera-ctrl', ... });
    const lines = result.files[0].content.split('\n');

    // Each line: time fx fy cx cy aspect flag1 flag2 w2c[12]
    const parts = lines[0].split(' ');
    expect(parts.length).toBe(20); // 8 params + 12 matrix elements
  });
});
```

**Checkpoint:** All new format tests pass

---

### Step 6: Clean Up Dual Exports

**Goal:** Single export path per target, remove confusion.

**Tasks:**
1. Update `services/export/index.ts` - Remove old function re-exports
2. Update `services/index.ts` - Only export new functions
3. Keep deprecated functions in `modelExport.ts` for backwards compat

**Checkpoint:**
```bash
# Only deprecated usages remain
grep -r "exportWanMoveTrajectories" src/services/ | grep -v "@deprecated" | wc -l
# Expected: 0 (only deprecated definitions)
```

---

## PART 4: ADAPTER DEPRECATION TIMELINE

| Phase | Status | Adapters | Internal Code | Timeline |
|-------|--------|----------|---------------|----------|
| **Phase 1** | NOW | ✅ Create adapters | Uses adapters | This sprint |
| **Phase 2** | NEXT | Keep for compat | Uses new functions directly | +2 weeks |
| **Phase 3** | LATER | @deprecated | All migrated | +1 month |
| **Phase X** | FUTURE | REMOVED | N/A | After API stable |

### Phase 1 (Current): Create Adapters
- `legacyAdapters.ts` created
- `exportForModel()` uses adapters
- Old functions marked @deprecated
- Tests pass

### Phase 2: Direct Migration
- Internal code imports new functions directly
- Adapters still available for any external consumers
- Performance improvement (no adapter overhead)

### Phase 3: Adapter Deprecation
- Adapters marked @deprecated
- Console warnings on adapter usage
- Migration guide in docs

### Phase X: Adapter Removal
- Verify no external consumers
- Remove `legacyAdapters.ts`
- Remove deprecated functions from `modelExport.ts`
- Final cleanup

---

## PART 5: VERIFICATION CHECKLIST

### Machine-Verifiable Checkpoints

```bash
# 1. All tests pass
npm test -- --run
# Expected: 0 failed

# 2. TypeScript compiles
npx tsc --noEmit
# Expected: No errors

# 3. New functions are used in exportForModel
grep -A5 "case \"wan-move\"" src/services/modelExport.ts | grep -c "legacyWanMoveExport\|exportAsKijaiWanMoveJSON"
# Expected: 1

# 4. Old functions not directly called (except in adapters)
grep -r "exportWanMoveTrajectories\|exportATITrajectory" src/services/ \
  | grep -v "@deprecated" \
  | grep -v "legacyAdapters" \
  | grep -v "export function" \
  | wc -l
# Expected: 0

# 5. No Python consumers
grep -r "exportWanMoveTrajectories\|exportATITrajectory\|exportCameraTrajectory" \
  --include="*.py" ../ 2>/dev/null | wc -l
# Expected: 0 (VERIFIED)
```

### Manual Verification

1. [ ] Export wan-move from compositor UI, verify Kijai node accepts it
2. [ ] Export ATI from compositor UI, verify 121 frames
3. [ ] Export CameraCtrl, verify format matches `fun_camera/nodes.py`

---

## PART 6: ROLLBACK STRATEGY

### Git Tags

```bash
# Before any changes
git tag phase1/before-changes

# After bug fix
git tag phase1/after-bug-fix

# After deprecation markers
git tag phase1/after-deprecation

# After adapter layer
git tag phase1/after-adapters

# After wiring complete
git tag phase1/after-wiring

# Phase 1 complete
git tag phase1/complete
```

### Rollback Commands

```bash
# If bug fix breaks things
git checkout phase1/before-changes

# If adapters break things
git checkout phase1/after-bug-fix

# If wiring breaks things
git checkout phase1/after-adapters

# Complete rollback
git checkout phase1/before-changes
```

### Feature Flag (Emergency)

```typescript
// In case of emergency rollback need
const USE_LEGACY_EXPORTS = import.meta.env.VITE_USE_LEGACY_EXPORTS === 'true';

// In exportForModel():
if (USE_LEGACY_EXPORTS) {
  return legacyExportPath(...);
} else {
  return newExportPath(...);
}
```

---

## PART 7: SESSION HANDOFF

### For Next Session

1. Read this document first
2. Check current step status below
3. Run `npm test -- --run` to verify baseline
4. Continue from current step

### Current Progress

| Step | Status | Notes |
|------|--------|-------|
| Step 1: Fix GPU particle bug | ✅ COMPLETE | BUG-099 fixed with recycle cap |
| Step 2: Deprecation warnings | ⏸️ PENDING | |
| Step 3: Adapter layer | ⏸️ PENDING | |
| Step 4: Wire unified export | ⏸️ PENDING | |
| Step 5: Update tests | ⏸️ PENDING | |
| Step 6: Clean up | ⏸️ PENDING | |

---

## APPENDIX A: File References

### New Export Files (CORRECT)
- `ui/src/services/export/wanMoveExport.ts` - WanMove Kijai format
- `ui/src/services/export/atiExport.ts` - ATI Kijai format (121 frames)
- `ui/src/services/export/cameraExportFormats.ts` - CameraCtrl poses

### Old Export Functions (TO DEPRECATE)
- `ui/src/services/modelExport.ts:322` - `exportWanMoveTrajectories`
- `ui/src/services/modelExport.ts:454` - `exportATITrajectory`
- `ui/src/services/modelExport.ts:84` - `exportCameraTrajectory`

### Bug Fix Location
- `ui/src/engine/particles/GPUParticleSystem.ts:1217` - spawn loop recycle cap

### Tests
- `ui/src/__tests__/export/wanMoveExport.test.ts` - 76 tests
- `ui/src/__tests__/export/atiExport.test.ts` - 32 tests
- `ui/src/__tests__/export/cameraExportFormats.test.ts` - 86 tests
- `ui/src/__tests__/export/modelExport.test.ts` - Old function tests
- `ui/src/__tests__/engine/particles/GPUParticleSystem.property.test.ts` - BUG-099 test

---

## APPENDIX B: External Consumer Verification

```bash
# Python consumers check (2026-01-11)
$ grep -r "exportWanMoveTrajectories\|exportATITrajectory\|exportCameraTrajectory" \
    --include="*.py" /mnt/c/Users/justi/Desktop/ComfyUI-Lattice-Compositor/
# Result: No matches

# JavaScript/TypeScript consumers outside services/
$ grep -r "exportWanMoveTrajectories" --include="*.ts" --include="*.vue" \
    src/components/ src/stores/ src/views/ 2>/dev/null
# Result: (run before making changes)
```

---

*Document Version: 1.0*
*Last Updated: 2026-01-11*
*Author: Claude Code*
