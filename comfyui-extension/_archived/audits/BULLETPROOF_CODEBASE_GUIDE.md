# Bulletproof Codebase Guide

> **Purpose:** Hyper-modern coding ethos applied to Lattice Compositor
> **Last Updated:** 2026-01-12
> **Status:** Active methodology

---

## Core Principles (From WEYL_COMPOSITOR_MASTER_PLAN.md)

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

---

## Evidence-Based Analysis Methodology

### TRACE EVERYTHING BACK TO SOURCE

**Rule:** Every claim must have an exact file path and line number reference.

**Format:**
```
- **Line X:** Description of what's happening
- **Source:** `path/to/file.ts:X`
- **Verification:** What was checked/compared
```

**Example:**
```
- **Line 2234:** `tracks: JSON.stringify(params.motionData?.tracks)`
- **Source:** `ui/src/services/comfyui/workflowTemplates.ts:2234`
- **Node:** `WanVideoAddWanMoveTracks`
- **Tensor input property:** `tracks` (stringified JSON)
- **Expected format:** `Array<Array<{x, y}>>` (from `exportWanMoveTrackCoordsJSON()`)
```

### VERIFY BEFORE CREATING

**Rule:** Never create new files without:
1. Checking if something similar exists
2. Understanding what already exists
3. Verifying the actual code structure

**Checklist:**
- [ ] Search codebase for existing patterns
- [ ] Read actual implementation (not just types/interfaces)
- [ ] Verify against runtime usage
- [ ] Check test files for examples
- [ ] Only then create/update files

### SHOW EXACT TRACES IN OUTPUT

**Required Sections:**
1. **Summary** with exact traces (file:line references)
2. **"Why This Is Not Myopic"** section (master plan context)
3. **"Next Step"** section (single best path forward)
4. **"Steps Back to Main Refactor"** section (clear return path)

### DOCUMENT ASSUMPTIONS AND GAPS

**Format:**
- What was verified ✅
- What was assumed ⚠️
- What needs verification ❓
- What might be wrong

---

## Code Quality Standards

### Type System Rules

**CRITICAL:** CODE IS TRUTH, TYPES DESCRIBE
- NEVER delete properties or code to satisfy TypeScript
- ALWAYS update type definitions to match working code
- If fixing a type error, change the TYPE not the CODE

**Current Technical Debt:**
- 581 type escapes (`any`, `as any`)
- 3,417 type assertions (`as X`, `!`)
- 3,564 runtime guards (`??`, `?.`)
- 231 lazy defaults (`|| 0`, `|| []`)

**Cleanup Priority:**
1. P0: Fix `as any` in production (344 instances)
2. P1: Fix `: any` parameters (170 instances)
3. P2: Fix `|| 0` in math code (172 instances)
4. P3: Clean up `!` assertions (after types fixed)
5. P4: Clean up nullish coalesce (after types fixed)

### File Size Rules

**Maximum:** 500 lines per file

**If over 500 lines:**
1. Modularize FIRST before other changes
2. Split by domain/responsibility
3. Extract helpers to separate files
4. Use composition over inheritance

**Current Status:**
- 232 files > 500 lines need modularization
- compositorStore.ts: 3,292 lines (target: 13 domain stores)

### Schema Validation Rules

**Purpose:** Schemas define the API contract, not just validation

**Required:**
- Internal canonical form (matches TypeScript interfaces)
- Export mappings (model-specific property names)
- Import mappings (external format validation)

**Current Coverage:** ~40%
- ✅ Covered: project, animation, transform, primitives, text, particles
- ❌ Missing: physics, shapes, layerStyles, effects, presets, meshWarp, masks, assets
- 🔴 Wrong: ShapeLayerData (fixed, but needs verification)

**Validation Boundaries:**
- Store actions (input validation)
- File I/O (import/export validation)
- Component props (boundary validation)
- All numeric values use `.finite()` to reject NaN/Infinity

---

## Workflow Rules

### Before Making ANY Change

1. **Read the Master Plan**
   - `docs/MASTER_REFACTOR_PLAN.md` - Current phase and strategy
   - `docs/STORE_MIGRATION_CONSUMERS.md` - Consumer file mapping
   - `docs/CROSS_DOMAIN_ACTIONS.md` - Cross-store coordination

2. **Verify Existing Code**
   - Search codebase for similar patterns
   - Read actual implementation files
   - Check test files for examples
   - Verify against runtime usage

3. **Check Current Phase**
   - What phase are we in? (See MASTER_REFACTOR_PLAN.md)
   - What are the exit criteria?
   - What files are being migrated?

4. **Document Your Work**
   - Show exact traces (file:line references)
   - Explain why it's not myopic
   - Connect to master plan
   - Document assumptions and gaps

### Pattern-Based Fixes

**Rule:** Fix ALL instances of a pattern across codebase

**Never:**
- Fix one file and move on
- Create a new file without checking existing code
- Assume naming conventions
- Skip verification steps

**Always:**
- Search for all instances first
- Fix systematically
- Verify fixes with tests
- Document the pattern

---

## Testing Requirements

### Test Coverage Standards

**Current Status:**
- 4,874 tests passing
- 321+ schemas, 0 tests
- 16.4% service coverage
- 12% effect coverage

**Required:**
- All schemas must have tests
- All validation boundaries must have tests
- Property tests for math/transform functions
- Integration tests for cross-domain actions

### Test Types

1. **Unit Tests** - Individual functions
2. **Property Tests** - fast-check for math/transform functions
3. **Integration Tests** - Cross-store coordination
4. **Regression Tests** - Bug fixes must have tests
5. **E2E Tests** - Playwright for UI workflows

---

## Export Format Requirements

### Critical Principle

**If a user works for hours and can't export because property names don't match, that's a critical failure.**

### Export Targets (20+ formats)

Each target requires DIFFERENT property names:
- WanMove: `tracks: Array<Array<{x, y}>>`
- ATI: `trajectories: Array<Array<{x, y}>>`
- MotionCtrl: `camera_poses: number[][]` (4x4 matrices)
- TTM: `layers[]` with masks + trajectories
- SCAIL: `reference_image`, `pose_images`
- ControlNet: Various formats (depth, normal, pose, etc.)

### Verification Process

1. Read export function (`services/export/*.ts`)
2. Read workflow template (`services/comfyui/workflowTemplates.ts`)
3. Verify tensor input property names match
4. Create schema for exact format
5. Create transformation function if needed
6. Test with actual export output

---

## Memory Management Rules

### Canvas/WebGL Resources

**Required Patterns:**
- Use `CanvasPool.acquire()` for canvases
- Always `releaseCanvas()` in finally blocks
- Handle WebGL context loss
- Revoke blob URLs after use

**Current Issues (Fixed in Phase 0):**
- ✅ Canvas leaks in effectProcessor.ts
- ✅ Canvas leaks in layerStyleRenderer.ts
- ✅ WebGL context loss handling
- ✅ URL.createObjectURL leaks

---

## Documentation Requirements

### Required Documentation

1. **Architecture Docs** (`docs/ARCHITECTURE.md`)
2. **API Reference** (`docs/SERVICE_API_REFERENCE.md`)
3. **Schema Spec** (`docs/SCHEMA_SPECIFICATION.md`)
4. **Master Plan** (`docs/MASTER_REFACTOR_PLAN.md`)
5. **Evidence Traces** (file:line references in all analysis)

### Documentation Standards

- Every claim must have file:line reference
- Show what was read, verified, and compared
- Document assumptions and gaps
- Connect to master plan

---

## No-Go Criteria

**Do NOT proceed if:**
- TypeScript errors > 0
- Any test suite fails
- Manual smoke test shows regression
- Memory leak detected
- Performance regression > 20%
- Schema validation missing at boundaries
- Export format not verified against actual model requirements

---

## Quick Reference

### Key Documents

| Document | Purpose |
|----------|---------|
| `docs/MASTER_REFACTOR_PLAN.md` | Execution phases and timeline |
| `docs/STORE_MIGRATION_CONSUMERS.md` | Consumer file mapping |
| `docs/CROSS_DOMAIN_ACTIONS.md` | Cross-store coordination |
| `docs/EVIDENCE_BASED_ANALYSIS_METHODOLOGY.md` | Analysis methodology |
| `WEYL_COMPOSITOR_MASTER_PLAN.md` | Hyper-modern coding axioms |
| `CLAUDE.md` | Session protocol and rules |

### Key Commands

```bash
# Type checking
npx tsc --noEmit

# Tests
npm test

# Formatting
npx biome format --write

# Linting
npx biome check

# Find consumers
grep -r "useCompositorStore" --include="*.ts" --include="*.vue"

# Count lines
wc -l path/to/file.ts
```

---

## Anti-Patterns to Eliminate

| Anti-Pattern | Fix |
|--------------|-----|
| `any` types everywhere | Strict TypeScript |
| Nullable required fields | Validation at boundaries |
| 4 color formats | Canonical format |
| Old + new export functions | Deprecate old, wire new |
| 3,000 line files | Modularize strategically |
| 14% completion across codebase | Finish one thing completely |
| Creating files without verification | Verify first, create second |
| Fixing one instance | Fix all instances |

---

*This guide consolidates principles from:*
- `WEYL_COMPOSITOR_MASTER_PLAN.md` - Hyper-modern coding axioms
- `docs/EVIDENCE_BASED_ANALYSIS_METHODOLOGY.md` - Analysis methodology
- `docs/MASTER_REFACTOR_PLAN.md` - Refactoring strategy
- `CLAUDE.md` - Session protocol
- `docs/SCHEMA_SPECIFICATION.md` - Schema requirements
- `docs/EXPORT_TENSOR_INPUT_VERIFICATION.md` - Export verification
