# LATTICE COMPOSITOR - BUGS FOUND
Master bug tracking document

**NOTICE: Audit reset on 2025-12-25. Starting fresh with complete file reads.**

---

## SUMMARY

| Severity | Count | Fixed | Open |
|----------|-------|-------|------|
| CRITICAL | 0 | 0 | 0 |
| HIGH | 2 | 2 | 0 |
| MEDIUM | 0 | 0 | 0 |
| LOW | 0 | 0 | 0 |
| **TOTAL** | **2** | **2** | **0** |

---

## BUGS BY FEATURE

### Feature 1.1: Layer Creation/Deletion

---

## BUG-001: Hardcoded fps=30 in splitLayerAtPlayhead

**Feature:** Layer Creation/Deletion (1.1)
**Severity:** HIGH
**Found:** 2025-12-25
**Status:** FIXED

**Location:**
- File: ui/src/stores/actions/layerActions.ts
- Line: 1539

**Issue:**
When splitting a video layer at the playhead, the source time offset calculation uses a hardcoded `fps = 30` instead of the composition's actual fps. This causes incorrect frame-to-time conversion when splitting video layers in compositions with non-30fps frame rates.

**Evidence:**
```typescript
// Adjust source time for video layers (VideoData has startTime and speed properties)
if (isLayerOfType(newLayer, 'video') && newLayer.data) {
  const fps = 30; // Default FPS <-- BUG: hardcoded
  const originalStartTime = newLayer.data.startTime ?? 0;
  const speed = newLayer.data.speed ?? 1;

  // Calculate new source start time based on split point
  const frameOffset = currentFrame - startFrame;
  const timeOffset = (frameOffset / fps) * speed;  // <-- Uses wrong fps
  newLayer.data.startTime = originalStartTime + timeOffset;
}
```

**Impact:**
- Video layer split at wrong time offset in 24fps, 60fps, or other non-30fps compositions
- For 60fps composition: video starts at wrong point (off by 2x)
- For 24fps composition: video starts at wrong point (off by ~0.8x)

**Fix Applied:**
1. Changed `const fps = 30;` to `const fps = store.fps ?? 30;`
2. Updated function signature to include `fps: number` in store type

**Files Changed:**
- ui/src/stores/actions/layerActions.ts (lines 1501, 1539)

**Related:**
- Lines 1448, 1590 already used correct pattern

---

## BUG-002: Hardcoded fps=30 in keyframe velocity functions

**Feature:** Layer Transform / Keyframe System (1.2)
**Severity:** HIGH
**Found:** 2025-12-25
**Status:** FIXED

**Location:**
- File: ui/src/stores/actions/keyframeActions.ts
- Lines: 1325-1326, 1388-1389

**Issue:**
The `applyKeyframeVelocity` and `getKeyframeVelocity` functions use hardcoded `fps = 30` for converting between velocity units and frame units. The code even has a TODO comment acknowledging this should be from the composition. This causes incorrect velocity calculations for non-30fps compositions.

**Evidence:**
```typescript
// Line 1325-1326 in applyKeyframeVelocity:
// Convert velocity to value offset
// Velocity is in units per second, convert to units per frame segment
const fps = 30; // TODO: Get from composition
const inVelocityPerFrame = settings.incomingVelocity / fps;
const outVelocityPerFrame = settings.outgoingVelocity / fps;

// Line 1388-1389 in getKeyframeVelocity:
// Convert value offset back to velocity
const fps = 30;
const inVelocity = keyframe.inHandle?.enabled && keyframe.inHandle.frame !== 0
  ? -keyframe.inHandle.value / Math.abs(keyframe.inHandle.frame) * fps
  : 0;
```

**Impact:**
- Keyframe velocity dialog shows incorrect velocity values for non-30fps compositions
- Applied velocity settings create wrong bezier handles
- 60fps compositions: velocities off by 2x
- 24fps compositions: velocities off by ~0.8x

**Fix Applied:**
1. Added `VelocityStore` interface extending `KeyframeStore` with `fps: number`
2. Updated function signatures to use `VelocityStore`
3. Changed `const fps = 30` to `const fps = store.fps ?? 30`

**Files Changed:**
- ui/src/stores/actions/keyframeActions.ts (lines 1279-1281, 1301, 1329, 1360, 1392)

**Related:**
- BUG-001 (same hardcoded fps pattern)

---

## TEMPLATE FOR NEW BUGS

Copy this template when adding new bugs:
```markdown
## BUG-XXX: [Short Title]

**Feature:** [Feature name] ([Tier ID])
**Severity:** CRITICAL / HIGH / MEDIUM / LOW
**Found:** [Date]
**Status:** OPEN / FIXED / WONT_FIX

**Location:**
- File: [exact file path]
- Line: [line number or range]

**Issue:**
[Precise description of what's wrong]

**Evidence:**
```[language]
[Code snippet showing the bug]
```

**Impact:**
[What breaks because of this bug]

**Fix:**
[Exact change needed - be specific]

**Related:**
[Other bugs or features affected]
```
