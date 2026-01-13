# Audit Roadmap - Steps to Avoid 5000+ Manual Checks

> **Created:** 2026-01-12  
> **Problem:** 500+ files × 10 columns = 5000+ cells to verify manually  
> **Solution:** Automate 90%+, manually verify 10%

---

## Current Status (Verified 2026-01-12)

### ✅ What Works
- **Tests Run:** ✅ `npm test -- --run` works
- **Property Tests:** ✅ `npm test -- --testNamePattern "property" --run` works
- **Test Framework:** Vitest + fast-check (TypeScript) + Hypothesis (Python)
- **Coverage:** Needs verification

### ⚠️ What's Broken
- **TypeScript:** 12 errors (BLOCKING - must fix first)
  - Duplicate `TrackPointSchema` (2 instances)
  - Missing `ShapeLayerDataSchema` export
  - Discriminated union type error
  - Implicit `any` types

---

## Strategic Steps (In Order)

### 🔴 STEP 0: Fix TypeScript Errors (BLOCKING)

**Time:** 1-2 hours  
**Status:** ⚠️ **MUST DO FIRST**

**Why:** Automation scripts need TypeScript to compile to parse files

**Errors to Fix:**
1. `src/schemas/exports/index.ts:73,315` - Remove duplicate `TrackPointSchema`
2. `src/schemas/layers/index.ts:155` - Export `ShapeLayerDataSchema` from correct file
3. `src/schemas/layers/shapes-schema.ts:512` - Fix discriminated union type
4. `src/services/export/exportToWorkflowParams.ts:39,61` - Add proper types

**Action:** Fix these BEFORE building automation

---

### ✅ STEP 1: Verify Coverage Works

**Time:** 30 minutes  
**Status:** ⏳ **PENDING**

**Action:** `cd ui && npm run test:coverage`

**Verify:**
- Coverage reports generate
- `coverage/coverage-final.json` exists
- Coverage percentages are reasonable

**If broken:** Fix coverage generation first

---

### ✅ STEP 2: Build Automation Scripts

**Time:** 10-15 hours total  
**Status:** ❌ **NOT STARTED**

**Scripts to Build:**

1. **`scripts/discover-tests.ts`** (2-3 hours)
   - Maps source files → test files
   - Output: `test-discovery.json`

2. **`scripts/test-status.ts`** (1 hour)
   - Runs tests, captures pass/fail
   - Output: `test-status.json`

3. **`scripts/coverage-analysis.ts`** (1-2 hours)
   - Parses coverage reports
   - Output: `coverage-analysis.json`

4. **`scripts/tsc-status.ts`** (1 hour)
   - Parses TypeScript errors
   - Output: `tsc-status.json`

5. **`scripts/generate-checklist.ts`** (3-4 hours)
   - Combines all data sources
   - Generates updated `MASTER_CHECKLIST.md`

**Total:** ~10-15 hours to build, runs in <5 minutes

---

### ✅ STEP 3: Run First Automated Audit

**Time:** 5 minutes + review  
**Status:** ❌ **NOT STARTED**

**Action:**
1. Run all scripts
2. Review generated checklist
3. Fix any script bugs
4. Re-run if needed

**Output:** Updated `MASTER_CHECKLIST.md` with ✅/⚠️/❌ based on actual data

---

### ✅ STEP 4: Manual Verification (Only What Can't Be Automated)

**Time:** ~6 hours  
**Status:** ❌ **NOT STARTED**

**Categories:**
- **Memory:** ~50 files (Phase 0 already fixed 6 critical bugs)
- **Performance:** ~50 files (can be semi-automated)
- **Security:** ~20 files (can be automated from audit files)

**Total:** ~6 hours vs 166+ hours manually

---

## Expected Outcomes

### Before Automation
- **Manual Work:** 5000+ cells × 2 min = 10,000+ min (166+ hours)
- **Accuracy:** Low (human error, outdated info)
- **Maintenance:** Manual updates every time

### After Automation
- **Manual Work:** ~50 cells × 5 min = 4 hours
- **Automated Work:** Scripts run in <5 minutes
- **Accuracy:** High (based on actual test results)
- **Maintenance:** Re-run scripts when needed

**Time Savings:** ~162 hours per audit cycle

---

## Next Actions (In Order)

1. **Fix TypeScript errors** (1-2 hours) - **BLOCKING**
2. **Verify coverage works** (30 min)
3. **Build test-discovery.ts** (2-3 hours)
4. **Build test-status.ts** (1 hour)
5. **Build coverage-analysis.ts** (1-2 hours)
6. **Build tsc-status.ts** (1 hour)
7. **Build generate-checklist.ts** (3-4 hours)
8. **Run first audit** (5 min)
9. **Manual verification** (6 hours)

**Total Time:** ~20 hours to build automation + 6 hours manual = 26 hours  
**Ongoing:** ~5 minutes per audit cycle

---

## Key Insights

1. **Fix infrastructure FIRST** - Can't audit if tests don't run
2. **Automate what can be automated** - 90%+ of checklist can be automated
3. **Manual only what requires judgment** - Memory, performance, security reviews
4. **Build incrementally** - Test each script as you build it
5. **Re-run anytime** - Not a one-time audit, but ongoing verification

---

*Roadmap created: 2026-01-12*  
*Status: TypeScript errors blocking - fix first*  
*Strategy: Automate 90%+, manually verify 10%*
