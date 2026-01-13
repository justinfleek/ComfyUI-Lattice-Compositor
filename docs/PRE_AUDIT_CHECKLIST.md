# Pre-Audit Checklist - Steps Before Manual Audit

> **Goal:** Fix infrastructure and automate verification BEFORE doing 5000+ manual checks  
> **Principle:** Automate what can be automated, manually verify only what requires human judgment

---

## ✅ STEP 1: Verify Test Infrastructure Works

**Time:** 30 minutes  
**Status:** ⏳ **IN PROGRESS**

### Actions:
- [x] Run tests: `cd ui && npm test -- --run` ✅ **PASSES**
- [ ] Verify property tests: `npm test -- --testNamePattern "property" --run` (vitest uses --testNamePattern, not --grep)
- [ ] Verify coverage: `npm run test:coverage`
- [x] Verify TypeScript: `npx tsc --noEmit` ⚠️ **HAS ERRORS** (need to fix first)
- [ ] Check for broken tests (fix if found)

**TypeScript Errors Found:**
- `src/schemas/exports/index.ts` - Duplicate `TrackPointSchema` (lines 73, 315)
- `src/schemas/layers/index.ts` - Missing export `ShapeLayerDataSchema` (line 155)
- `src/schemas/layers/shapes-schema.ts` - Discriminated union type error (line 512)
- `src/services/export/exportToWorkflowParams.ts` - Implicit `any` types (lines 39, 61)

**Action Required:** Fix TypeScript errors BEFORE running audit automation

**Why First:** Can't audit if tests don't run

**Evidence:** Tests are running (verified 2026-01-12)

---

## ✅ STEP 2: Create Test Discovery Script

**Time:** 2-3 hours  
**Status:** ❌ **NOT STARTED**

**Script:** `scripts/discover-tests.ts`

**What it does:**
- Scans `ui/src/` for source files
- For each file, checks if test files exist:
  - `src/__tests__/**/filename.test.ts` (unit)
  - `src/__tests__/**/filename.property.test.ts` (property)
  - `src/__tests__/**/filename.regression.test.ts` (regression)
  - `src/__tests__/**/filename.integration.test.ts` (integration)
  - `playwright/**/filename.spec.ts` (E2E)
- Outputs JSON mapping source → test files

**Output:** `test-discovery.json`

**Why:** Eliminates manual file checking (500+ files)

---

## ✅ STEP 3: Create Test Status Script

**Time:** 1 hour  
**Status:** ❌ **NOT STARTED**

**Script:** `scripts/test-status.ts`

**What it does:**
- Runs: `npm test -- --run --reporter=json --outputFile=test-results.json`
- Parses test results
- Maps test results to source files
- Outputs JSON: `{ file: "path.ts", tests: { unit: "pass", property: "fail" } }`

**Output:** `test-status.json`

**Why:** Eliminates manual test running (500+ files)

---

## ✅ STEP 4: Create Coverage Analysis Script

**Time:** 1-2 hours  
**Status:** ❌ **NOT STARTED**

**Script:** `scripts/coverage-analysis.ts`

**What it does:**
- Runs: `npm run test:coverage`
- Parses `coverage/coverage-final.json`
- Maps coverage to source files
- Calculates coverage percentages
- Outputs JSON: `{ file: "path.ts", coverage: 85.5 }`

**Output:** `coverage-analysis.json`

**Why:** Eliminates manual coverage checking (500+ files)

---

## ✅ STEP 5: Create TypeScript Status Script

**Time:** 1 hour  
**Status:** ❌ **NOT STARTED**

**Script:** `scripts/tsc-status.ts`

**What it does:**
- Runs: `npx tsc --noEmit --pretty false 2>&1`
- Parses TypeScript errors
- Maps errors to files
- Outputs JSON: `{ file: "path.ts", errors: 0, warnings: 2 }`

**Output:** `tsc-status.json`

**Why:** Eliminates manual TypeScript checking (500+ files)

---

## ✅ STEP 6: Create Checklist Generator Script

**Time:** 3-4 hours  
**Status:** ❌ **NOT STARTED**

**Script:** `scripts/generate-checklist.ts`

**What it does:**
- Reads all JSON files from steps 2-5
- Reads current `MASTER_CHECKLIST.md`
- For each file in checklist:
  - **Unit:** test exists && passes ? ✅ : test exists ? ⚠️ : ❌
  - **Property:** property test exists && passes ? ✅ : exists ? ⚠️ : ❌
  - **Regression:** regression test exists && passes ? ✅ : exists ? ⚠️ : ❌
  - **TypeScript:** errors === 0 ? ✅ : warnings only ? ⚠️ : ❌
  - **Memory:** (manual - check Phase 0 completion)
  - **E2E:** playwright test exists && passes ? ✅ : exists ? ⚠️ : ❌
  - **Integration:** integration test exists && passes ? ✅ : exists ? ⚠️ : ❌
  - **Browser:** browser test exists && passes ? ✅ : exists ? ⚠️ : ❌
  - **Performance:** (manual - requires profiling)
  - **Security:** security test exists && passes ? ✅ : exists ? ⚠️ : ❌
- Generates updated `MASTER_CHECKLIST.md`

**Output:** Updated `MASTER_CHECKLIST.md`

**Why:** Eliminates 90%+ of manual checklist updates (4500+ cells)

---

## ✅ STEP 7: Manual Verification (Only What Can't Be Automated)

**Time:** 1-2 hours per domain  
**Status:** ❌ **NOT STARTED**

### Categories Requiring Manual Check:

1. **Memory Tests** (50 files × 2 min = 100 min)
   - Check for canvas leaks
   - Check for WebGL context loss
   - Check for memory leaks
   - **Note:** Phase 0 already fixed 6 critical bugs

2. **Performance Tests** (50 files × 3 min = 150 min)
   - Benchmark tests
   - Profiling results
   - **Note:** Can be semi-automated with performance test framework

3. **Security Tests** (20 files × 5 min = 100 min)
   - Review security audit findings
   - Check for known vulnerabilities
   - **Note:** Can be automated from audit files

**Total Manual Work:** ~350 minutes (6 hours) vs 5000+ cells manually

---

## Implementation Timeline

### Week 1: Infrastructure + Scripts
- **Day 1:** Verify test infrastructure (30 min)
- **Day 1-2:** Write test-discovery.ts (2-3 hours)
- **Day 2:** Write test-status.ts (1 hour)
- **Day 2:** Write coverage-analysis.ts (1-2 hours)
- **Day 3:** Write tsc-status.ts (1 hour)
- **Day 3-4:** Write generate-checklist.ts (3-4 hours)

### Week 2: First Automated Audit
- **Day 1:** Run all scripts (5 min)
- **Day 1:** Review automated results (1 hour)
- **Day 1-2:** Fix script bugs if any (2-4 hours)
- **Day 2:** Manual verification (6 hours)

**Total Time:** ~20 hours to build automation + 6 hours manual = 26 hours  
**Savings:** ~162 hours per audit cycle (5000 cells × 2 min = 10,000 min)

---

## Critical Questions to Answer NOW

1. ✅ **Do tests run?** YES - Verified 2026-01-12
2. ⏳ **Do property tests work?** NEED TO VERIFY
3. ⏳ **Does coverage work?** NEED TO VERIFY
4. ⏳ **Does TypeScript compile?** NEED TO VERIFY

**If any fail, fix them FIRST before building automation.**

---

## Next Immediate Actions

1. **Verify property tests:** `cd ui && npm test -- --grep "property" --run`
2. **Verify coverage:** `cd ui && npm run test:coverage`
3. **Verify TypeScript:** `cd ui && npx tsc --noEmit`
4. **If all pass:** Start writing scripts
5. **If any fail:** Fix them first

---

*Checklist created: 2026-01-12*  
*Purpose: Avoid wasting tokens on manual 5000+ cell audit*  
*Strategy: Automate 90%+, manually verify 10%*
