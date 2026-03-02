# Phase 2 Getter/Method Decisions - CRITICAL ARCHITECTURAL DECISIONS

> **Date:** 2026-01-18  
> **Status:** ⚠️ **PENDING DECISIONS** - Must complete BEFORE KeyframeStoreAccess refactoring  
> **Priority:** 🔴 **CRITICAL** - Blocks all keyframeStore refactoring work  
> **Why Critical:** Working backwards from consumer expectations - wrong decisions break everything

---

## Executive Summary

**Problem:** Before we can eliminate `KeyframeStoreAccess` and refactor `keyframeStore` methods to use domain stores directly, we must decide where these critical getters/methods live:

1. `currentFrame` - Where should this getter live?
2. `fps` - Where should this getter live?
3. `frameCount` - Where should this getter live?
4. `currentTime` - Where should this getter live?
5. `getFrameState()` - Where should this method live?
6. `getInterpolatedValue()` - Where should this method live?

**Impact:** These decisions affect:
- `KeyframeStoreAccess` interface requirements
- All `keyframeStore` method refactoring
- 100+ consumer files that use these getters
- All domain stores that need to access these values

**Risk:** Making wrong decisions now will require massive refactoring later. We must analyze consumer usage patterns first.

---

## Current State Analysis

### What KeyframeStoreAccess Requires

From `ui/src/stores/keyframeStore/types.ts:21-36`:

```typescript
export interface KeyframeStoreAccess {
  project: {
    composition: { width: number; height: number };
    meta: { modified: string };
  };
  getActiveComp(): {
    currentFrame: number;        // ⚠️ NEEDS DECISION
    layers: Layer[];
    settings: { 
      fps: number;               // ⚠️ NEEDS DECISION
      frameCount: number;        // ⚠️ NEEDS DECISION
      duration: number; 
      width: number; 
      height: number 
    };
  } | null;
  getActiveCompLayers(): Layer[];
  getLayerById(id: string): Layer | null;
  pushHistory(): void;
  readonly fps: number;          // ⚠️ NEEDS DECISION (duplicate of settings.fps?)
}
```

### Current Implementation

**compositorStore.ts getters (lines 144-182):**
- `frameCount()` → `this.activeComposition?.settings.frameCount || 81`
- `fps()` → `this.activeComposition?.settings.fps || 16`
- `duration()` → `this.activeComposition?.settings.duration || 5`
- `currentFrame()` → `comp?.currentFrame || 0`
- `currentTime()` → `comp.currentFrame / comp.settings.fps`

**projectStore.ts methods:**
- `getActiveComp()` → Returns `Composition | null` (has `currentFrame` property)
- `getActiveCompLayers()` → Returns layers array
- `pushHistory()` → History management

**animationStore.ts:**
- `getFrameState()` → Currently delegates to `animationStore.getFrameState()`
- `isPlaying()` → Playback state

**keyframeStore:**
- `getInterpolatedValue()` → Currently delegates to `keyframeStore.getInterpolatedValue()`

---

## Decision Matrix

### Decision 1: `currentFrame` Getter

**Current:** `compositorStore.currentFrame()` → reads from `activeComposition.currentFrame`

**Analysis Results:**
- **Storage:** `composition.currentFrame` (composition property - data)
- **Control:** `animationStore.setFrame()` sets it (playback control - UI state)
- **Usage Patterns:**
  - Components: `store.currentFrame` (WorkspaceLayout.vue:116, 620)
  - Composables: `activeComp?.currentFrame` (useKeyboardShortcuts, useMenuActions)
  - Stores: `comp.currentFrame` (physicsStore, layerStore/time.ts)
  - animationStore methods: Read via `AnimationStoreAccess.currentFrame` (helper reads from composition)

**Options:**

| Option | Store | Rationale | Pros | Cons |
|--------|-------|-----------|------|------|
| **A** | `animationStore` | Playback/timeline control domain | Logical grouping with playback control | Requires accessing projectStore for composition |
| **B** | `projectStore` | Composition property (data) | Direct access to composition | Mixes UI state (currentFrame) with data (composition) |
| **C** | **Read directly** | No getter, use `getActiveComp()?.currentFrame` | Simplest, no abstraction | Every consumer needs to know about composition structure |

**✅ DECISION: Option A - `animationStore` getter**
- **Rationale:** 
  - `animationStore.setFrame()` controls it (playback domain)
  - `AnimationStoreAccess` already requires `currentFrame` as readonly property
  - Consumers already create helpers that read from composition
  - Getter provides convenient access while keeping domain clear
- **Implementation:** Add `currentFrame()` getter to `animationStore` that reads from `projectStore.getActiveComp()?.currentFrame`
- **Migration:** Update consumers to use `animationStore.currentFrame` instead of `compositorStore.currentFrame`

---

### Decision 2: `fps` Getter

**Current:** `compositorStore.fps()` → reads from `activeComposition.settings.fps`

**Analysis Results:**
- **Storage:** `composition.settings.fps` (composition setting - data)
- **Existing:** `projectStore.getFps()` method already exists (line 126)
- **Usage Patterns:**
  - Components: `store.fps` (WorkspaceLayout.vue, DepthflowProperties.vue)
  - Composables: `animationAccess.fps` (useKeyboardShortcuts) - helper uses `projectStore.getFps()`
  - Stores: `comp.settings.fps` (compositorStore, audioStore)
  - projectStore: Already has `getFps()` method and getter

**Options:**

| Option | Store | Rationale | Pros | Cons |
|--------|-------|-----------|------|------|
| **A** | `projectStore` | Composition setting (data) | Already exists as method/getter | None |
| **B** | **Read directly** | No getter, use `getActiveComp()?.settings.fps` | Simplest | Every consumer needs to know structure |

**✅ DECISION: Option A - `projectStore.getFps()` (already exists)**
- **Rationale:**
  - `projectStore.getFps()` already exists and is used
  - Composition setting (data domain)
  - Some consumers already use it (WorkspaceLayout.vue:621, 636)
- **Implementation:** No change needed - already exists
- **Migration:** Update remaining consumers to use `projectStore.getFps()` instead of `compositorStore.fps()`

---

### Decision 3: `frameCount` Getter

**Current:** `compositorStore.frameCount()` → reads from `activeComposition.settings.frameCount`

**Analysis Results:**
- **Storage:** `composition.settings.frameCount` (composition setting - data)
- **Existing:** `projectStore.getFrameCount()` method already exists (line 121)
- **Usage Patterns:**
  - Components: `store.frameCount` (WorkspaceLayout.vue:117)
  - Composables: `animationAccess.frameCount` (useKeyboardShortcuts) - helper reads from composition
  - Stores: `comp.settings.frameCount` (physicsStore, layerStore)
  - projectStore: Already has `getFrameCount()` method and getter

**Options:**

| Option | Store | Rationale | Pros | Cons |
|--------|-------|-----------|------|------|
| **A** | `projectStore` | Composition setting (data) | Already exists as method/getter | None |
| **B** | **Read directly** | No getter, use `getActiveComp()?.settings.frameCount` | Simplest | Every consumer needs to know structure |

**✅ DECISION: Option A - `projectStore.getFrameCount()` (already exists)**
- **Rationale:**
  - `projectStore.getFrameCount()` already exists
  - Composition setting (data domain)
  - Consistent with `getFps()` pattern
- **Implementation:** No change needed - already exists
- **Migration:** Update remaining consumers to use `projectStore.getFrameCount()` instead of `compositorStore.frameCount()`

---

### Decision 4: `currentTime` Getter

**Current:** `compositorStore.currentTime()` → computed: `comp.currentFrame / comp.settings.fps`

**Analysis Results:**
- **Computation:** `currentFrame / fps` (computed value)
- **Existing:** `projectStore.getCurrentTime()` method already exists (line 141)
- **Usage Patterns:**
  - Very rarely used (only in tutorial tests)
  - Most consumers don't use it
  - projectStore already has `getCurrentTime()` method

**Options:**

| Option | Store | Rationale | Pros | Cons |
|--------|-------|-----------|------|------|
| **A** | `animationStore` | Computed from playback state | Logical grouping | Requires accessing both currentFrame and fps |
| **B** | `projectStore` | Composition-level computed property | Already exists | Mixes UI state with data |
| **C** | **Read directly** | No getter, compute inline | Simplest | Duplication if used frequently |

**✅ DECISION: Option B - `projectStore.getCurrentTime()` (already exists)**
- **Rationale:**
  - `projectStore.getCurrentTime()` already exists
  - Rarely used, so keeping it simple is fine
  - Consistent with other composition-level getters
- **Implementation:** No change needed - already exists
- **Migration:** Update any consumers to use `projectStore.getCurrentTime()` instead of `compositorStore.currentTime()`

---

### Decision 5: `getFrameState()` Method

**Current:** `compositorStore.getFrameState()` → delegates to `animationStore.getFrameState()`

**Analysis Results:**
- **Location:** `animationStore.getFrameState()` (line 311)
- **Domain:** Frame evaluation (animation/playback domain)
- **Signature:** `getFrameState(store: FrameEvaluationAccess, frame?: number): FrameState`
- **Usage:** Delegates correctly from compositorStore

**Options:**

| Option | Store | Rationale | Pros | Cons |
|--------|-------|-----------|------|------|
| **A** | **Keep in `animationStore`** | Frame evaluation is animation domain | Already correct | None |
| **B** | Move to `projectStore` | Project-level operation | Centralized | Wrong domain |

**✅ DECISION: Option A - Keep in `animationStore`** ✅ **VERIFIED CORRECT**

**Action:** 
- ✅ Already correctly placed
- ⏳ Update consumers to use `animationStore.getFrameState()` directly instead of `compositorStore.getFrameState()`
- ⏳ Remove delegation from compositorStore after consumer migration

---

### Decision 6: `getInterpolatedValue()` Method

**Current:** `compositorStore.getInterpolatedValue()` → delegates to `keyframeStore.getInterpolatedValue()`

**Analysis Results:**
- **Location:** `keyframeStore.getInterpolatedValue()` 
- **Domain:** Keyframe interpolation (keyframe domain)
- **Usage:** Delegates correctly from compositorStore

**Options:**

| Option | Store | Rationale | Pros | Cons |
|--------|-------|-----------|------|------|
| **A** | **Keep in `keyframeStore`** | Interpolation is keyframe domain | Already correct | None |
| **B** | Move elsewhere | ? | Wrong domain | N/A |

**✅ DECISION: Option A - Keep in `keyframeStore`** ✅ **VERIFIED CORRECT**

**Action:**
- ✅ Already correctly placed
- ⏳ Update consumers to use `keyframeStore.getInterpolatedValue()` directly instead of `compositorStore.getInterpolatedValue()`
- ⏳ Remove delegation from compositorStore after consumer migration

---

## Analysis Required

### Step 1: Consumer Usage Analysis

**Files to grep:**
```bash
# Find all usages of these getters/methods
grep -r "\.currentFrame" ui/src/
grep -r "\.fps" ui/src/
grep -r "\.frameCount" ui/src/
grep -r "\.currentTime" ui/src/
grep -r "getFrameState" ui/src/
grep -r "getInterpolatedValue" ui/src/
```

**Questions to Answer:**
1. How many files use each getter/method?
2. Are they used for UI state (timeline scrubbing) or data access?
3. Are they used frequently enough to warrant getters vs direct access?
4. Do consumers expect these from `compositorStore` or would domain stores be acceptable?

### Step 2: Domain Store Analysis

**Check what each store currently provides:**
- `projectStore`: Has `getActiveComp()` which returns composition with all these properties
- `animationStore`: Has playback state, but not composition access
- `keyframeStore`: Needs these values but shouldn't own them

### Step 3: Architectural Consistency

**Principles:**
- UI state (currentFrame for scrubbing) → `animationStore`
- Data (composition settings) → `projectStore`
- Computed values → Where they're computed from
- Methods → Domain that owns the operation

---

## Decision Process

1. ✅ **Document current state** (this document)
2. ✅ **Analyze consumer usage** (grep + manual review) - COMPLETE 2026-01-18
3. ✅ **Propose decisions** (with rationale) - COMPLETE 2026-01-18
4. ✅ **Review decisions** (verify against consumer expectations) - COMPLETE 2026-01-18
5. ⏳ **Implement decisions** (update stores, update consumers) - IN PROGRESS
   - ✅ Added `currentFrame()` getter to `animationStore`
   - ⏳ Update consumers to use new getter locations
6. ⏳ **Refactor KeyframeStoreAccess** (now that getters are decided) - READY TO START

---

## Impact Assessment

### If We Get This Wrong:

- **Wrong store placement** → Consumers break, need massive refactoring
- **Missing getters** → Consumers can't access values, need to update 100+ files
- **Inconsistent decisions** → Confusion, technical debt, harder to maintain

### If We Get This Right:

- **Clear architecture** → Easy to understand where things live
- **Smooth refactoring** → KeyframeStoreAccess elimination becomes straightforward
- **Consumer migration** → Clear path for updating 100+ files

---

## Next Steps

1. ✅ **Run consumer usage analysis** (grep + categorize) - COMPLETE
2. ✅ **Document usage patterns** (how each getter is used) - COMPLETE
3. ✅ **Propose decisions** (with evidence from analysis) - COMPLETE
4. ✅ **Review decisions** (verify decisions make sense) - COMPLETE
5. ⏳ **Implement decisions** (update stores) - IN PROGRESS
   - ✅ Added `currentFrame()` getter to `animationStore`
   - ⏳ Verify `projectStore.getFps()`, `getFrameCount()`, `getCurrentTime()` exist (already verified)
6. ⏳ **Update consumers** (migrate to new getter locations) - PENDING
   - Update `store.currentFrame` → `animationStore.currentFrame`
   - Update `store.fps` → `projectStore.getFps()`
   - Update `store.frameCount` → `projectStore.getFrameCount()`
   - Update `store.currentTime` → `projectStore.getCurrentTime()`
7. ⏳ **Refactor KeyframeStoreAccess** (now that getters are decided) - READY TO START

---

## Related Documents

- `docs/MASTER_REFACTOR_STATUS.md` - Overall refactor status
- `docs/MASTER_REFACTOR_PLAN.md` - Original plan
- `ui/src/stores/keyframeStore/types.ts` - KeyframeStoreAccess interface
- `ui/src/stores/compositorStore.ts` - Current getter implementations

---

*Document created: 2026-01-18*  
*Purpose: Prevent loss of architectural decisions during compactions*  
*Status: PENDING DECISIONS - Analysis required*
