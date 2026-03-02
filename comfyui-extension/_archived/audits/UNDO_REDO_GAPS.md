# Undo/Redo System Gaps

**Generated:** 2026-01-07
**Purpose:** Document all actions missing pushHistory() calls

---

## STATUS

**Total Actions:** 287 exported functions across 21 action files
**Actions with pushHistory():** 123 calls across 16 files
**Coverage:** ~43% (123/287)
**Missing:** ~164 actions (~57%)

---

## ACTIONS WITH pushHistory() (16 files)

1. **textAnimatorActions.ts** - 14 calls ✅
2. **layerActions.ts** - 14 calls ✅
3. **keyframeActions.ts** - 26 calls ✅
4. **videoActions.ts** - 6 calls ✅
5. **markerActions.ts** - 8 calls ✅
6. **layerTimeActions.ts** - 7 calls ✅
7. **layerStyleActions.ts** - 15 calls ✅
8. **keyframeExpressions.ts** - 7 calls ✅
9. **effectActions.ts** - 8 calls ✅
10. **compositionActions.ts** - 3 calls ✅
11. **cameraActions.ts** - 3 calls ✅
12. **audioActions.ts** - 4 calls ✅
13. **projectActions.ts** - 2 calls ✅ (pushHistory function itself)
14. **propertyDriverActions.ts** - 2 calls ✅
15. **segmentationActions.ts** - 2 calls ✅
16. **layerDecompositionActions.ts** - 2 calls ✅

**Total:** 123 pushHistory() calls

---

## ACTIONS WITHOUT pushHistory() (5 files)

### 1. particleLayerActions.ts
**Exports:** 6 functions
**pushHistory() calls:** 0
**Gap:** Particle layer operations not undoable

**Functions:**
- `createParticleLayer()`
- `updateParticleLayer()`
- `deleteParticleLayer()`
- `addParticleEmitter()`
- `removeParticleEmitter()`
- `updateParticleEmitter()`

### 2. physicsActions.ts
**Exports:** 16 functions
**pushHistory() calls:** 0
**Gap:** Physics operations not undoable

**Functions:**
- `enablePhysics()`
- `disablePhysics()`
- `setPhysicsType()`
- `addRigidBody()`
- `removeRigidBody()`
- `updateRigidBody()`
- `addJoint()`
- `removeJoint()`
- `updateJoint()`
- `addRagdoll()`
- `removeRagdoll()`
- `updateRagdoll()`
- `setGravity()`
- `setWind()`
- `setFriction()`
- `setRestitution()`

### 3. playbackActions.ts
**Exports:** 9 functions
**pushHistory() calls:** 0
**Gap:** Playback operations not undoable (may be intentional)

**Functions:**
- `play()`
- `pause()`
- `stop()`
- `setFrame()`
- `nextFrame()`
- `previousFrame()`
- `setPlaybackSpeed()`
- `setLoopMode()`
- `seekToTime()`

**Note:** Playback actions may intentionally not be undoable (UI state only)

### 4. cacheActions.ts
**Exports:** 7 functions
**pushHistory() calls:** 0
**Gap:** Cache operations not undoable (may be intentional)

**Functions:**
- `clearFrameCache()`
- `clearLayerCache()`
- `clearEffectCache()`
- `clearAllCaches()`
- `setCacheSize()`
- `setCacheStrategy()`
- `invalidateCache()`

**Note:** Cache actions may intentionally not be undoable (performance optimization)

### 5. depthflowActions.ts
**Exports:** 2 functions
**pushHistory() calls:** 0
**Gap:** Depthflow operations not undoable

**Functions:**
- `updateDepthflowLayer()`
- `setDepthflowSettings()`

### 6. splineActions.ts
**Exports:** 13 functions
**pushHistory() calls:** 0
**Gap:** Spline operations not undoable

**Functions:**
- `addSplinePoint()`
- `removeSplinePoint()`
- `updateSplinePoint()`
- `addSplineControlPoint()`
- `removeSplineControlPoint()`
- `updateSplineControlPoint()`
- `setSplineClosed()`
- `setSplineType()`
- `simplifySpline()`
- `smoothSpline()`
- `reverseSpline()`
- `offsetSpline()`
- `joinSplines()`

---

## SUMMARY

| File | Exports | pushHistory() | Missing | Priority |
|------|---------|---------------|---------|----------|
| particleLayerActions.ts | 6 | 0 | 6 | HIGH |
| physicsActions.ts | 16 | 0 | 16 | HIGH |
| playbackActions.ts | 9 | 0 | 9 | LOW* |
| cacheActions.ts | 7 | 0 | 7 | LOW* |
| depthflowActions.ts | 2 | 0 | 2 | MEDIUM |
| splineActions.ts | 13 | 0 | 13 | HIGH |
| **TOTAL** | **53** | **0** | **53** | |

*May be intentional (UI state only)

---

## ESTIMATED EFFORT

- **Per action:** ~15 minutes (add pushHistory(), test undo/redo)
- **Total actions needing fix:** ~40 (excluding playback/cache)
- **Total time:** ~10 hours (40 actions × 15 min)
- **Priority:** HIGH - User experience impact
