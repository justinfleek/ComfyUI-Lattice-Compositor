# Audit Automation Strategy - Complete Plan

> **Problem:** 500+ files × 10 columns = 5000+ cells to verify manually  
> **Goal:** Automate 90%+ of verification, only manually verify what automation can't check  
> **Current Status:** Tests run ✅ | TypeScript has errors ⚠️ | Property tests need verification

---

## Executive Summary

**Before Automation:**
- Manual Work: 5000+ cells × 2 minutes = 10,000+ minutes (166+ hours)
- Accuracy: Low (human error, outdated info)
- Maintenance: Manual updates every time tests change

**After Automation:**
- Manual Work: ~50 cells (memory, performance) × 5 minutes = 4 hours
- Automated Work: Scripts run in <5 minutes
- Accuracy: High (based on actual test results)
- Maintenance: Re-run scripts when needed

**Time Savings:** ~162 hours per audit cycle

---

## Critical Prerequisites (MUST FIX FIRST)

### ✅ STEP 0: Fix TypeScript Errors

**Status:** ⚠️ **BLOCKING** - 12 TypeScript errors found

**Errors Found:**
1. `src/schemas/exports/index.ts:73,315` - Duplicate `TrackPointSchema`
2. `src/schemas/layers/index.ts:155` - Missing export `ShapeLayerDataSchema`
3. `src/schemas/layers/shapes-schema.ts:512` - Discriminated union type error
4. `src/services/export/exportToWorkflowParams.ts:39,61` - Implicit `any` types

**Why First:** Automation scripts need TypeScript to compile to parse files

**Time:** 1-2 hours to fix

**Action:** Fix these errors BEFORE building automation scripts

---

## Automation Scripts (Build After TypeScript Fixed)

### STEP 1: Test Discovery Script

**File:** `scripts/discover-tests.ts`

**Purpose:** Map source files to test files

**Logic:**
```typescript
// For each file in ui/src/**/*.{ts,vue}:
// 1. Extract filename (without extension)
// 2. Check if test files exist:
//    - src/__tests__/**/${filename}.test.ts
//    - src/__tests__/**/${filename}.property.test.ts
//    - src/__tests__/**/${filename}.regression.test.ts
//    - src/__tests__/**/${filename}.integration.test.ts
//    - playwright/**/${filename}.spec.ts
// 3. Output JSON mapping
```

**Output:** `test-discovery.json`
```json
{
  "ui/src/stores/compositorStore.ts": {
    "unit": "ui/src/__tests__/stores/compositorStore.test.ts",
    "property": null,
    "regression": null,
    "integration": null,
    "e2e": null
  }
}
```

**Time:** 2-3 hours to write

---

### STEP 2: Test Status Script

**File:** `scripts/test-status.ts`

**Purpose:** Run tests and capture pass/fail status

**Logic:**
```typescript
// 1. Run: npm test -- --run --reporter=json --outputFile=test-results.json
// 2. Parse test-results.json
// 3. Map test results to source files (via test-discovery.json)
// 4. Output JSON with pass/fail status
```

**Output:** `test-status.json`
```json
{
  "ui/src/stores/compositorStore.ts": {
    "unit": "pass",
    "property": "n/a",
    "regression": "n/a",
    "integration": "n/a",
    "e2e": "n/a"
  }
}
```

**Time:** 1 hour to write

**Note:** Vitest uses `--testNamePattern` not `--grep` for filtering

---

### STEP 3: Coverage Analysis Script

**File:** `scripts/coverage-analysis.ts`

**Purpose:** Parse coverage and map to files

**Logic:**
```typescript
// 1. Run: npm run test:coverage
// 2. Parse coverage/coverage-final.json
// 3. Map coverage to source files
// 4. Calculate percentages
```

**Output:** `coverage-analysis.json`
```json
{
  "ui/src/stores/compositorStore.ts": {
    "coverage": 45.2,
    "lines": { "covered": 150, "total": 332 }
  }
}
```

**Time:** 1-2 hours to write

---

### STEP 4: TypeScript Status Script

**File:** `scripts/tsc-status.ts`

**Purpose:** Check TypeScript errors per file

**Logic:**
```typescript
// 1. Run: npx tsc --noEmit --pretty false 2>&1
// 2. Parse errors (file:line:error)
// 3. Group by file
// 4. Count errors vs warnings
```

**Output:** `tsc-status.json`
```json
{
  "ui/src/stores/compositorStore.ts": {
    "errors": 0,
    "warnings": 0,
    "status": "pass"
  }
}
```

**Time:** 1 hour to write

---

### STEP 5: Checklist Generator Script

**File:** `scripts/generate-checklist.ts`

**Purpose:** Auto-generate checklist updates

**Logic:**
```typescript
// 1. Read test-discovery.json
// 2. Read test-status.json
// 3. Read coverage-analysis.json
// 4. Read tsc-status.json
// 5. Read MASTER_CHECKLIST.md (current)
// 6. For each file:
//    - Unit: test exists && passes ? ✅ : test exists ? ⚠️ : ❌
//    - Property: property test exists && passes ? ✅ : exists ? ⚠️ : ❌
//    - Regression: regression test exists && passes ? ✅ : exists ? ⚠️ : ❌
//    - TypeScript: errors === 0 ? ✅ : warnings only ? ⚠️ : ❌
//    - Memory: (check Phase 0 completion - manual)
//    - E2E: playwright test exists && passes ? ✅ : exists ? ⚠️ : ❌
//    - Integration: integration test exists && passes ? ✅ : exists ? ⚠️ : ❌
//    - Browser: browser test exists && passes ? ✅ : exists ? ⚠️ : ❌
//    - Performance: (manual - requires profiling)
//    - Security: security test exists && passes ? ✅ : exists ? ⚠️ : ❌
// 7. Generate updated MASTER_CHECKLIST.md
```

**Output:** Updated `MASTER_CHECKLIST.md`

**Time:** 3-4 hours to write

---

## Implementation Order

### Phase A: Fix Blockers (Day 1)
1. ✅ Fix TypeScript errors (1-2 hours)
2. ✅ Verify property tests work (30 min)
3. ✅ Verify coverage generation (30 min)

### Phase B: Build Automation (Days 2-4)
1. ✅ Write test-discovery.ts (2-3 hours)
2. ✅ Write test-status.ts (1 hour)
3. ✅ Write coverage-analysis.ts (1-2 hours)
4. ✅ Write tsc-status.ts (1 hour)
5. ✅ Write generate-checklist.ts (3-4 hours)

### Phase C: First Audit (Day 5)
1. ✅ Run all scripts (5 min)
2. ✅ Review results (1 hour)
3. ✅ Fix script bugs (2-4 hours if needed)
4. ✅ Manual verification (6 hours)

**Total Time:** ~20 hours to build + 6 hours manual = 26 hours  
**Savings:** ~162 hours per audit cycle

---

## Manual Verification (Only What Can't Be Automated)

### Memory Tests
- **Files:** ~50 files with canvas/WebGL usage
- **Check:** Canvas leaks, WebGL context loss
- **Status:** Phase 0 already fixed 6 critical bugs
- **Time:** 1-2 hours (mostly verified)

### Performance Tests
- **Files:** ~50 files with performance-critical code
- **Check:** Benchmark tests, profiling
- **Note:** Can be semi-automated with performance test framework
- **Time:** 2-3 hours

### Security Tests
- **Files:** ~20 files with security implications
- **Check:** Review audit findings, known vulnerabilities
- **Note:** Can be automated from audit files
- **Time:** 1-2 hours

**Total Manual:** ~6 hours vs 166+ hours manually

---

## Next Immediate Actions

1. **Fix TypeScript errors** (BLOCKING - 1-2 hours)
   - Fix duplicate `TrackPointSchema`
   - Fix missing `ShapeLayerDataSchema` export
   - Fix discriminated union type error
   - Fix implicit `any` types

2. **Verify property tests** (30 min)
   - Run: `npm test -- --testNamePattern "property" --run`
   - Verify they pass
   - If they fail, fix them

3. **Verify coverage** (30 min)
   - Run: `npm run test:coverage`
   - Verify reports generate
   - If broken, fix it

4. **Build automation scripts** (10-15 hours)
   - Start with test-discovery.ts
   - Build incrementally
   - Test each script as you build it

---

## Success Criteria

**Automation is successful when:**
- ✅ Scripts run in <5 minutes
- ✅ Checklist updates are 90%+ accurate
- ✅ Manual work reduced from 166 hours to 6 hours
- ✅ Can re-run audit anytime (not just once)

**Manual audit is successful when:**
- ✅ All automated cells verified
- ✅ All manual cells verified (memory, performance)
- ✅ Checklist reflects actual test status
- ✅ Can trust checklist for future work

---

*Strategy created: 2026-01-12*  
*Status: TypeScript errors blocking - fix first*  
*Next: Fix TypeScript errors, then build automation*
