# Bug Tracking Reconciliation

## CRITICAL: DUPLICATE BUG IDs IN BUGS.md

After detailed analysis, discovered that BUGS.md itself contains **DUPLICATE bug IDs**:

**Original entries (lines 1-500):**
- BUG-029: hdrRenderer.ts - gamma correction div/0
- BUG-030: layerStyleRenderer.ts - infinite loop
- BUG-035: frameCache.ts - cache key collision
- BUG-036: cameraActions.ts - NaN keyframe
- BUG-037: frameCache.ts - infinite loop
- BUG-038: frameCache.ts - NaN memory counter
- BUG-047: layerActions.ts - newIndex NaN
- BUG-048: layerActions.ts - samplePathPoints div/0
- BUG-049: layerActions.ts - applyExponentialScale div/0

**Later entries (lines 1755+) with SAME bug IDs:**
- BUG-029: audioActions.ts - extractChannelAmplitudes div/0
- BUG-030: audioActions.ts - getAudioAmplitudeAtFrame div/0
- BUG-035: (not redefined)
- BUG-047: audioActions.ts - clearAudio resource leak
- BUG-048: audioActions.ts - createPathAnimator resource leak
- BUG-049: audioActions.ts - removePathAnimator resource leak

This means FIX_TRACKER.md was tracking the LATER entries (audioActions bugs), not the ORIGINAL entries (frameCache/layerActions bugs).

## Result: BUGS FIXED THIS SESSION

The following bugs from ORIGINAL BUGS.md were shadowed by duplicates and are now FIXED:

| Bug ID | File | Description | Status |
|--------|------|-------------|--------|
| BUG-035 | frameCache.ts:246-253 | getCacheKey NaN collision | **FIXED** (added Number.isFinite check) |
| BUG-036 | cameraActions.ts:18-19 | NaN keyframe accumulation | FIXED (framesEqual helper exists) |
| BUG-037 | frameCache.ts:478-480 | preCacheWindow infinite loop | **FIXED** (added validation + cap) |
| BUG-038 | frameCache.ts:336-342 | NaN ImageData memory corruption | **FIXED** (dimension validation) |
| BUG-047 | layerActions.ts:591 | newIndex NaN in moveLayer | FIXED (Number.isInteger check exists) |
| BUG-048 | layerActions.ts:1349-1355 | samplePathPoints div/0 | FIXED (count<2 guard exists) |
| BUG-049 | layerActions.ts:1606-1612 | applyExponentialScale div/0 | FIXED (Number.isFinite check exists) |

## Original Bug Mappings (from BUGS.md lines 1-500)

| Bug ID | Correct File | Correct Description | FIX_TRACKER said | Status |
|--------|--------------|---------------------|------------------|--------|
| BUG-035 | frameCache.ts | Cache key collision with NaN frame | layerActions.ts SYSTEMIC-004 | **UNFIXED** |
| BUG-036 | cameraActions.ts | NaN keyframe accumulation | layerActions.ts SYSTEMIC-002 | FIXED (framesEqual) |
| BUG-037 | frameCache.ts | Infinite loop preCacheWindow=Infinity | layerActions.ts SYSTEMIC-003 | **UNFIXED** |
| BUG-038 | frameCache.ts | NaN ImageData corrupts memory counter | breadcrumbActions.ts | **UNFIXED** |
| BUG-039 | compositionActions.ts | fps validation | compositionActions.ts | FIXED (validateFps) |
| BUG-040 | compositionActions.ts | NaN index breadcrumb | compositionActions.ts | FIXED (Number.isInteger) |
| BUG-041 | depthflowActions.ts | NaN config values | depthflowActions.ts | FIXED (sanitizeNumber) |
| BUG-042 | effectActions.ts | NaN index reorderEffects | effectActions.ts | FIXED (Number.isInteger) |
| BUG-043 | effectActions.ts | NaN parameter values | effectActions.ts | **NEEDS VERIFICATION** |
| BUG-044 | keyframeActions.ts | NaN frame bypass | keyframeActions.ts | FIXED (safeFrame) |
| BUG-045 | keyframeActions.ts | div/0 insertKeyframeOnPath | keyframeActions.ts | **NEEDS VERIFICATION** |
| BUG-046 | keyframeActions.ts | fps=0 velocity | keyframeActions.ts | FIXED (fps validation) |
| BUG-047 | layerActions.ts | NaN newIndex in moveLayer | audioActions.ts (WRONG) | FIXED (Number.isInteger) |
| BUG-048 | layerActions.ts | div/0 samplePathPoints | audioActions.ts (WRONG) | **NEEDS VERIFICATION** |
| BUG-049 | layerActions.ts | div/0 applyExponentialScale | audioActions.ts (WRONG) | FIXED (Number.isFinite) |

## Bugs Confirmed UNFIXED

### BUG-035: frameCache.ts line 246-248
```typescript
private getCacheKey(frame: number, compositionId: string): string {
  return `${compositionId}:${frame}`;
}
```
**Issue:** NaN frame creates key "comp:NaN" - all NaN frames collide to same cache entry

### BUG-037: frameCache.ts line 475
```typescript
for (let i = 1; i <= window; i++) {
```
**Issue:** preCacheWindow=Infinity causes infinite loop, browser freeze

### BUG-038: frameCache.ts lines 334, 364
```typescript
let size = imageData.width * imageData.height * 4;
// ...
this.currentMemory += size;
```
**Issue:** NaN dimensions → size=NaN → currentMemory=NaN permanently → cache grows unbounded

## Root Cause of Discrepancy

FIX_TRACKER.md appears to have been manually edited with incorrect bug-to-file mappings, likely during a context compaction where the original BUGS.md wasn't re-read.

## Action Required

1. Fix BUG-035, BUG-037, BUG-038 in frameCache.ts
2. Verify BUG-043, BUG-045, BUG-048
3. Update FIX_TRACKER.md with correct mappings
4. Cross-reference ALL bugs against source BUGS.md

---
Created: 2025-12-28
