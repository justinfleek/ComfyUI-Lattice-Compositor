# WEYL COMPOSITOR MASTER PLAN

> **Document Purpose:** Single source of truth for project state, decisions, and progress. Read this FIRST at the start of every session.
> 
> **Last Updated:** 2026-01-22
> **Session Count:** 5+ (across multiple context windows)
> **Latest:** Keyframe System ✅ COMPLETE (2026-01-22) - All 35 gaps fixed/verified, KeyframeStoreAccess elimination verified complete

---

## FOUNDATIONAL PRINCIPLES

These axioms from the CTO govern ALL development decisions. Memorize them.

### The Hypermodern Coding Axioms

| Axiom | Implication |
|-------|-------------|
| **Precision is a BUDGET not a theology** | Be precise where it matters. Don't over-engineer low-risk areas. Spend precision budget on boundaries, exports, and validation. |
| **Choices dominate resources** | Architecture decisions matter more than compute. A bad design can't be fixed by throwing hardware at it. |
| **Choices generate outcomes** | Every shortcut, every `any` type, every skipped validation has downstream consequences. Own them. |
| **High integrity behavior is lucrative and efficient** | Doing it right is cheaper than fixing it later. Technical debt compounds like financial debt. |
| **Logic is hygiene** | Clean, logical code is basic hygiene, not optional polish. You don't ship dirty code. |
| **The constraints you accept determine the solution you discover** | Embrace constraints (TypeScript strict, validation boundaries, canonical formats). They force better solutions. |
| **Build it right the first time** | No "we'll fix it later." Later never comes. The 14% completion problem exists because of this. |
| **Accuracy > Speed. Correctness > Completion** | A correct partial solution beats a complete broken one. Ship less, ship right. |
| **Slow and meticulous wins the AI race against slop** | The market is flooded with fast, broken AI tools. Meticulous quality is the competitive advantage. |

### How These Apply to This Project

```
PRECISION BUDGET ALLOCATION:
├── HIGH PRECISION (spend the budget here)
│   ├── Export formats (AI model compatibility)
│   ├── Input validation (security boundaries)
│   ├── Type definitions (runtime contracts)
│   └── Test coverage (regression prevention)
│
└── LOWER PRECISION (acceptable trade-offs)
    ├── Internal utility functions
    ├── UI polish details
    └── Performance micro-optimizations
```

### The Anti-Patterns We're Eliminating

| Anti-Pattern | Axiom Violated | Fix |
|--------------|----------------|-----|
| `any` types everywhere | Logic is hygiene | Strict TypeScript |
| Nullable required fields | Build it right first time | Validation at boundaries |
| 4 color formats | Choices generate outcomes | Canonical format |
| Old + new export functions | High integrity is efficient | Deprecate old, wire new |
| 3,000 line files | Precision is a budget | Modularize strategically |
| 14% completion across codebase | Accuracy > Speed | Finish one thing completely |

---

## EXECUTIVE SUMMARY

**What is this project?**
Lattice Compositor (formerly Weyl) is a professional motion graphics compositor built as a ComfyUI custom node with a Vue frontend. It enables AI-driven video generation with 26 layer types, camera systems, and exports to 24+ AI model formats.

**Current State:** BROKEN - In the middle of a major refactor with:
- 14% completion across multiple subsystems (started but not finished)
- 3,000+ line files being modularized
- Type system chaos (types don't match runtime)
- 90+ unvalidated input boundaries
- 24 export formats, 3 confirmed broken

**Critical Principle:** CODE IS TRUTH. Types describe code behavior, never prescribe it. Never delete properties to satisfy TypeScript. *(This is "Logic is hygiene" + "High integrity behavior" in action.)*

---

## PART 1: CURRENT STATE AUDIT

### 1.1 Codebase Health Summary

| Area | Status | Details |
|------|--------|---------|
| TypeScript Strict Mode | ❌ Not enforced | `any` types, `as` casts, `!` assertions everywhere |
| Layer Data Types | ❌ 17/26 broken | Type definitions don't match runtime behavior |
| Color Formats | ❌ 4 different formats | hex, RGB object, array, HSL - no canonical format |
| Alpha Values | ❌ Mixed ranges | 0-1, 0-255, 0-100 all in use |
| Input Validation | ❌ 90+ unvalidated | Zod schemas exist but not wired up |
| Export Formats | ⚠️ 3 patched | WanMove, ATI, CameraCtrl fixed but OLD functions still exist |
| File Sizes | ❌ 3,000+ line files | Modularization started, not finished |
| Test Coverage | ⚠️ Partial | Some unit tests, no integration tests |
| Documentation | ❌ None | No architecture docs, no API docs |

### 1.2 Layer Type Audit Results

From session 2026-01-11-13-14-31:

| Layer Type | Type/Runtime Match | Nullable Fields | Notes |
|------------|-------------------|-----------------|-------|
| solid | ❌ | color can be null | Should never be null |
| gradient | ❌ | stops, type, angle nullable | All required |
| image | ❌ | src nullable | Required field |
| video | ❌ | src, currentTime nullable | Required |
| text | ❌ | text, font nullable | Required |
| shape | ❌ | shapeType nullable | Required |
| audio | ❌ | src nullable | Required |
| composition | ❌ | compositionId nullable | Required |
| null | ✅ | N/A | Placeholder type |
| adjustment | ⚠️ | adjustments array | Partial match |
| camera3d | ⚠️ | Complex nested | Partial match |
| light3d | ⚠️ | Complex nested | Partial match |
| mesh3d | ⚠️ | Complex nested | Partial match |
| particles | ❌ | Multiple nullable | Heavy issues |
| spline | ❌ | points nullable | Required |
| mask | ❌ | maskData nullable | Required |
| depth | ⚠️ | depthData optional | Acceptable |
| normal | ⚠️ | normalData optional | Acceptable |
| flow | ❌ | flowData nullable | Required |
| pose | ❌ | poseData nullable | Required |
| trajectory | ❌ | trajectoryData nullable | Required |
| control | ⚠️ | controlType checked | Partial |
| wanmove | ❌ | Complex nested | Heavy issues |
| effect | ❌ | effectType nullable | Required |
| group | ✅ | children array | Works |
| reference | ❌ | referenceId nullable | Required |

**Summary:** 17 BROKEN, 6 PARTIAL, 3 OK

### 1.3 Export Format Audit Results

From session 2026-01-11-15-13-17:

**Camera Exports (6):**
| Format | Status | Notes |
|--------|--------|-------|
| MotionCtrl 4x4 | ✅ Compatible | View matrix format matches |
| MotionCtrl-SVD | ⚠️ Untested | Needs verification |
| Wan 2.2 Fun Camera | ✅ Preset only | No matrices exported |
| Uni3C | ⚠️ Deprecated | Non-functional with current models |
| AnimateDiff CameraCtrl | ✅ FIXED | Added `exportAsCameraCtrlPoses()` |
| Full Camera JSON | ✅ Internal | Not for AI models |

**Trajectory Exports (3):**
| Format | Status | Notes |
|--------|--------|-------|
| WanMove JSON | ✅ FIXED | Added `exportAsKijaiWanMoveJSON()` - uses {x,y} objects |
| ATI | ✅ FIXED | Created `atiExport.ts` - 121 frame padding |
| NPY Binary | ⚠️ Untested | Needs verification |

**Pose Exports (3):**
| Format | Status | Notes |
|--------|--------|-------|
| OpenPose JSON | ✅ Compatible | Standard format |
| Pose Sequence | ⚠️ Untested | Needs verification |
| Pose Image | ⚠️ Untested | Needs verification |

**Other Exports:**
| Format | Status | Notes |
|--------|--------|-------|
| VACE Control | ⚠️ Untested | Video control format |
| Mesh Deform | ⚠️ Untested | 3D deformation |
| Frame Sequences | ⚠️ Untested | Image sequences |
| Matte Export | ⚠️ Untested | Alpha channels |
| ComfyUI Workflow | ⚠️ Untested | Node graph export |

**CRITICAL:** Old broken export functions still exist alongside new fixed ones. Need to:
1. Update all call sites to use new functions
2. Deprecate old functions
3. Add tests for integration

### 1.4 Input Boundary Audit

From session 2026-01-11-14-31-39:

**90+ Unvalidated Boundaries Identified:**

```
EXTERNAL INPUTS (highest risk):
├── ComfyUI node inputs (Python → JavaScript)
├── File uploads (images, videos, audio, projects)
├── URL inputs (external resources)
├── LLM-generated content (embedded AI outputs)
└── Cross-machine communication

INTERNAL BOUNDARIES (medium risk):
├── Layer data mutations
├── Store updates
├── Property changes
├── Timeline operations
└── Camera transforms

EXPORT BOUNDARIES (data integrity):
├── 24 export formats
├── JSON serialization
├── Binary formats (NPY)
└── Image/video encoding
```

**Existing but unused validation:**
- Zod schemas defined in multiple files
- Validation utilities exist
- Never wired to actual input paths

---

## PART 2: ARCHITECTURAL DECISIONS

### 2.1 Canonical Internal Format (DECIDED)

**Decision:** Use Game Engine Pattern - Single canonical internal format with adapters at boundaries.

```
EXTERNAL INPUT → [Import Adapter] → CANONICAL FORMAT → [Export Adapter] → EXTERNAL OUTPUT
                                          ↓
                                    [Internal Processing]
```

**Canonical Color Format:**
```typescript
interface CanonicalColor {
  r: number;  // 0-1 (NOT 0-255)
  g: number;  // 0-1
  b: number;  // 0-1
  a: number;  // 0-1
}
```

**Canonical Coordinate Format:**
```typescript
interface CanonicalPoint {
  x: number;  // pixels (for screen space)
  y: number;  // pixels
}

interface NormalizedPoint {
  x: number;  // -1 to 1 (for AI models)
  y: number;  // -1 to 1
}
```

**Adapters needed:**
- `hexToCanonical()`, `canonicalToHex()`
- `rgb255ToCanonical()`, `canonicalToRgb255()`
- `hslToCanonical()`, `canonicalToHsl()`
- `pixelToNormalized()`, `normalizedToPixel()`

### 2.2 Type System Strategy (DECIDED)

**Decision:** Types DESCRIBE code, never PRESCRIBE it.

**Rules:**
1. If code handles null → type includes null
2. If code can't handle null → type excludes null AND validation enforces it
3. Never delete code to satisfy types
4. Never add `as` casts to make types pass
5. Update types to match runtime, then add validation to prevent invalid states

**Implementation:**
```typescript
// Step 1: Types reflect CURRENT reality (including bugs)
interface LayerData {
  color: string | null;  // Currently nullable at runtime
}

// Step 2: Add runtime validation at boundaries
const validateLayerData = z.object({
  color: z.string().regex(/^#[0-9a-f]{6}$/i),  // Validate on input
});

// Step 3: After all inputs validated, tighten types
interface LayerData {
  color: string;  // Now guaranteed non-null
}
```

### 2.3 Validation Strategy (DECIDED)

**Decision:** Validate at boundaries only, trust internal code.

```
┌─────────────────────────────────────────────────────────────┐
│                    TRUSTED ZONE                              │
│                                                              │
│   [Store] ←→ [Components] ←→ [Services] ←→ [Utils]          │
│                                                              │
├──────────────────────────────────────────────────────────────┤
│                    VALIDATION BOUNDARY                       │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│   [ComfyUI] [Files] [URLs] [LLM] [Network] [User Input]     │
│                                                              │
│                    UNTRUSTED ZONE                            │
└─────────────────────────────────────────────────────────────┘
```

**Validation libraries:**
- Zod for schema validation
- fast-check for property testing
- Custom sanitizers for specific formats

---

## PART 3: EXECUTION PLAN

### Phase 0: Project Infrastructure [CURRENT]
**Goal:** Enable persistent context across sessions

| Task | Status | Checkpoint |
|------|--------|------------|
| Create master plan document | ✅ DONE | This file exists |
| Create session handoff protocol | 🔄 IN PROGRESS | Documented below |
| Set up task tracking | ⏸️ PENDING | Need GitHub issues or similar |
| Define machine-verifiable checkpoints | ⏸️ PENDING | CI/CD checks |

### Phase 1: Stabilize Current State
**Goal:** Stop the bleeding, make tests pass

| Task | Status | Checkpoint |
|------|--------|------------|
| Wire new export functions to call sites | ⏸️ PENDING | All exports use new functions |
| Deprecate old broken exports | ⏸️ PENDING | TypeScript warnings on old functions |
| Run full test suite | ⏸️ PENDING | `npm test` passes |
| Fix any broken tests | ⏸️ PENDING | 0 failing tests |
| Document current test coverage | ⏸️ PENDING | Coverage report generated |

### Phase 2: Type System Foundation
**Goal:** Types match runtime, strict mode enabled

| Task | Status | Checkpoint |
|------|--------|------------|
| Audit all 26 layer types | ✅ DONE | See 1.2 above |
| Update type definitions to match runtime | ⏸️ PENDING | No `as` casts needed |
| Enable TypeScript strict mode | ⏸️ PENDING | `tsc --strict` passes |
| Remove all `any` types | ⏸️ PENDING | grep finds 0 `any` |
| Remove all `!` assertions | ⏸️ PENDING | grep finds 0 `!` on properties |

### Phase 3: Validation Infrastructure
**Goal:** All inputs validated at boundaries

| Task | Status | Checkpoint |
|------|--------|------------|
| Define Zod schemas for all layer types | ⏸️ PENDING | 26 schemas defined |
| Wire validation to ComfyUI inputs | ⏸️ PENDING | All node inputs validated |
| Wire validation to file uploads | ⏸️ PENDING | All uploads validated |
| Wire validation to URL inputs | ⏸️ PENDING | All URLs validated |
| Add validation error reporting | ⏸️ PENDING | Errors surface to user |

### Phase 4: Canonical Formats
**Goal:** Single internal representation for each data type

| Task | Status | Checkpoint |
|------|--------|------------|
| Implement canonical color format | ⏸️ PENDING | All colors use 0-1 RGBA |
| Create color adapters | ⏸️ PENDING | hex/rgb/hsl converters work |
| Implement canonical coordinate format | ⏸️ PENDING | Pixel + normalized variants |
| Update all code to use canonical formats | ⏸️ PENDING | grep finds no old formats |
| Add property tests for round-trips | ⏸️ PENDING | fast-check tests pass |

### Phase 5: Testing Infrastructure
**Goal:** Comprehensive test coverage

| Task | Status | Checkpoint |
|------|--------|------------|
| Unit tests for all services | ⏸️ PENDING | 80%+ coverage |
| Property tests for all exports | ⏸️ PENDING | fast-check for each format |
| Contract tests vs Kijai reference | ⏸️ PENDING | Output matches expected |
| Integration tests | ⏸️ PENDING | Cross-module tests pass |
| E2E tests | ⏸️ PENDING | Playwright tests pass |

### Phase 6: Security Hardening
**Goal:** All 90+ boundaries protected

| Task | Status | Checkpoint |
|------|--------|------------|
| Input sanitization | ⏸️ PENDING | XSS tests pass |
| Path traversal prevention | ⏸️ PENDING | Security tests pass |
| URL validation | ⏸️ PENDING | Only allowed domains |
| File type validation | ⏸️ PENDING | Magic bytes checked |
| Rate limiting | ⏸️ PENDING | Abuse prevention active |

### Phase 7: Performance & Monitoring
**Goal:** Production-ready observability

| Task | Status | Checkpoint |
|------|--------|------------|
| Error tracking (Sentry) | ⏸️ PENDING | Errors reported |
| Performance metrics | ⏸️ PENDING | Render time tracked |
| Memory leak detection | ⏸️ PENDING | No leaks in long sessions |
| Bundle size budgets | ⏸️ PENDING | CI fails on bloat |

### Phase 8: Documentation
**Goal:** Self-documenting codebase

| Task | Status | Checkpoint |
|------|--------|------------|
| API documentation | ⏸️ PENDING | All exports documented |
| Architecture diagrams | ⏸️ PENDING | Mermaid diagrams in repo |
| Integration guides | ⏸️ PENDING | ComfyUI setup docs |
| Contributing guide | ⏸️ PENDING | New dev onboarding |

---

## PART 4: SESSION HANDOFF PROTOCOL

### Starting a New Session

1. **Read this document FIRST** - It contains current state and decisions
2. **Check the transcript journal** - `/mnt/transcripts/journal.txt`
3. **Ask:** "What phase are we in? What's the next uncompleted task?"
4. **Verify state:** Run `npm test` to confirm baseline

### During a Session

1. **Update this document** when:
   - A task status changes
   - A decision is made
   - A new issue is discovered
2. **Create transcript summaries** for complex work
3. **Mark checkpoints** when verifiable milestones are reached
4. **Apply the axioms** - When facing a choice, ask:
   - Does this choice generate good outcomes downstream?
   - Am I building it right the first time?
   - Is this accurate and correct, or just fast?

### Decision Framework (Use When Stuck)

```
WHEN FACING A CHOICE:

1. "Choices dominate resources"
   → Which option has better ARCHITECTURE, not just faster delivery?

2. "Choices generate outcomes"  
   → What are the downstream consequences of each path?

3. "The constraints you accept determine the solution"
   → What constraints am I avoiding that I should embrace?

4. "Accuracy > Speed"
   → Am I rushing? Would slowing down produce a better result?

5. "Build it right the first time"
   → Am I creating debt that compounds?
```

### Ending a Session

1. **Update task statuses** in this document
2. **Document any blockers** or open questions
3. **Save transcript** to `/mnt/transcripts/`
4. **Update journal.txt** with summary

---

## PART 5: KEY FILES & LOCATIONS

### Source Code
```
/ui/src/
├── services/
│   └── export/
│       ├── wanMoveExport.ts      # WanMove trajectories (PATCHED)
│       ├── atiExport.ts          # ATI trajectories (NEW)
│       ├── cameraExportFormats.ts # Camera exports (PATCHED)
│       ├── poseExport.ts         # Pose exports
│       ├── vaceControlExport.ts  # VACE control
│       └── index.ts              # Export barrel
├── stores/                       # Pinia stores
├── components/                   # Vue components
└── types/                        # TypeScript definitions
```

### Test Files
```
/ui/src/__tests__/
├── export/
│   ├── wanMoveExport.test.ts        # 76 tests
│   ├── atiExport.test.ts            # 32 tests (NEW)
│   ├── cameraExportFormats.test.ts  # 86 tests
│   └── *.property.test.ts           # Property-based tests
└── integration/
    └── export-comfyui.integration.test.ts
```

### Reference Files
```
/tmp/kijai-reference/            # Cloned Kijai WanVideoWrapper
├── WanMove/nodes.py            # WanMove format spec
├── ATI/nodes.py                # ATI format spec (121 frames)
├── ATI/motion.py               # Coordinate normalization
├── fun_camera/nodes.py         # CameraCtrl poses format
├── recammaster/nodes.py        # ReCamMaster format
├── SCAIL/nodes.py              # SCAIL format
├── controlnet/nodes.py         # ControlNet format
└── uni3c/nodes.py              # Uni3C format (deprecated)
```

### Transcripts
```
/mnt/transcripts/
├── journal.txt                                              # Summary index
├── 2026-01-11-13-14-31-layer-data-type-audit-nulls-correction.txt
├── 2026-01-11-13-14-56-layer-data-security-threat-model.txt
├── 2026-01-11-14-31-39-security-validation-architecture-scope.txt
└── 2026-01-11-15-13-17-export-format-verification-kijai-wan.txt
```

---

## PART 6: OPEN QUESTIONS & BLOCKERS

### Unresolved Questions

1. **Nix deployment** - CTO's domain, do not touch
2. **VLA model integration** - How will autonomous agent drive compositor?
3. **Multi-user/collaboration** - Is this needed? Conflict resolution?
4. **Offline mode** - Does it need to work without network?
5. **Plugin architecture** - Third-party extensions?

### Known Blockers

1. **Old export functions not deprecated** - Call sites still use broken versions
2. **No CI/CD** - Can't enforce checkpoints automatically
3. **No staging environment** - Can't test deployment
4. **3,000+ line files** - Modularization incomplete

### Technical Debt Register

| Item | Severity | Location | Notes |
|------|----------|----------|-------|
| Duplicate export functions | HIGH | export/*.ts | Old + new coexist |
| Nullable required fields | HIGH | All layer types | 17/26 affected |
| Mixed color formats | MEDIUM | Entire codebase | 4 formats in use |
| Mixed alpha ranges | MEDIUM | Entire codebase | 0-1, 0-255, 0-100 |
| Unused Zod schemas | MEDIUM | validation/ | Never wired up |
| Giant files | LOW | Multiple | 3,000+ lines |

---

## APPENDIX A: VERIFIED EXPORT FORMAT SPECS

### A.1 Kijai WanMove JSON

**Source:** `/tmp/kijai-reference/WanMove/nodes.py:78-100`

```python
# Input: JSON string to track_coords parameter
tracks_data = json.loads(track_coords)
# Expected: [[{x, y}, {x, y}, ...], ...]
# - Outer array: tracks
# - Inner array: frames
# - Each point: {x: number, y: number} (PIXEL coordinates)
```

**Lattice function:** `exportAsKijaiWanMoveJSON()` ✅

### A.2 Kijai ATI

**Source:** `/tmp/kijai-reference/ATI/nodes.py`, `ATI/motion.py`

```python
FIXED_LENGTH = 121  # Always 121 frames

# Coordinate normalization (in process_tracks):
tracks = tracks - [width/2, height/2]  # Center
tracks = tracks / short_edge * 2       # Normalize to [-1, 1]

# Visibility encoding:
visibles * 2 - 1  # Convert 0/1 to -1/1
```

**Lattice function:** `exportAsKijaiATI()` ✅ (raw pixels, Kijai normalizes)

### A.3 CameraCtrl Poses

**Source:** `/tmp/kijai-reference/fun_camera/nodes.py:11-21`

```python
# Entry format: space-separated string
# [time, fx, fy, cx, cy, aspect, flag1, flag2, w2c[0], ..., w2c[11]]
# - time: frame number
# - fx, fy: focal length in pixels
# - cx, cy: principal point (0.5, 0.5 normalized)
# - aspect: width/height
# - flags: unused (0, 0)
# - w2c: 3x4 world-to-camera matrix, row-major
```

**Lattice function:** `exportAsCameraCtrlPoses()` ✅

---

## APPENDIX B: SESSION LOG

| Date | Session | Key Outcomes |
|------|---------|--------------|
| 2026-01-11 | Layer type audit | 17/26 types broken, nulls are bugs |
| 2026-01-11 | Security threat model | 90+ unvalidated boundaries |
| 2026-01-11 | Architecture scope | Export inventory, validation gap |
| 2026-01-11 | Export verification | 3 breaking mismatches, fixes applied |
| 2026-01-11 | Master plan creation | This document created |

---

## DOCUMENT REVISION HISTORY

| Version | Date | Changes |
|---------|------|---------|
| 1.0 | 2026-01-11 | Initial creation from 5 sessions of research |
| 1.1 | 2026-01-11 | Added CTO's Hypermodern Coding Axioms and decision framework |