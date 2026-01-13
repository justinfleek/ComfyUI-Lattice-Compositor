# Comprehensive Consumer File Audit

**Date:** 2026-01-12
**Purpose:** Systematically audit ALL files that call compositorStore methods

## Current State

**Total Files Found:** 107 files calling `store.*` methods
- 77 component files (696 matches)
- 9 service files (130 matches)
- 8 composable files (152 matches)
- 12 test files (2,649 matches)
  - 9 test files in `__tests__/` (integration, performance, regression, services, tutorials)
  - 3 test files in `__tests__/stores/` (keyframeActions.test.ts, particlePreferences.property.test.ts, projectActions.test.ts) ✅ **FOUND**

**Original Count:** 109 files
**Missing:** 2 files (need to identify - possibly miscounted or files were deleted/renamed)

## Audit Strategy

### Step 1: Identify Missing Files
- Check git history for deleted files
- Check if any files were renamed/moved
- Verify against original documentation

### Step 2: Categorize All 106 Files
For each file, determine:
1. **Domain:** Which domain store should handle this?
   - layerStore (Phase 1)
   - keyframeStore (Phase 2)
   - animationStore (Phase 2)
   - expressionStore (Phase 2)
   - audioStore (Phase 3)
   - effectStore (Phase 3)
   - cameraStore (Phase 4)
   - projectStore (Phase 5)
   - uiStore (Phase 5)

2. **Migration Status:** 
   - ✅ Already migrated (uses domain store)
   - ⚠️ Partially migrated (some calls migrated, some not)
   - ❌ Not migrated (still calls compositorStore)

3. **Priority:**
   - P0: Critical (blocks other work)
   - P1: High (frequently used)
   - P2: Medium (occasionally used)
   - P3: Low (rarely used)

### Step 3: Verify Method Migration
For each method called, verify:
1. Is it properly delegated in compositorStore?
2. Does the domain store implementation exist?
3. Is the implementation correct?
4. Are there any bugs or missing features?

### Step 4: Update Consumers
For each file that needs updates:
1. Import appropriate domain store
2. Replace `store.method()` with `domainStore.method(store, ...)`
3. Verify types are correct
4. Test the change
5. Document the change

## Files to Audit

### Components (77 files)
[Will be populated during audit]

### Services (9 files)
[Will be populated during audit]

### Composables (8 files)
[Will be populated during audit]

### Tests (12 files)
[Will be populated during audit]

## Methods with Implementation Code

See `docs/COMPOSITORSTORE_METHOD_AUDIT.md` for list of 17 methods that still have implementation code in compositorStore.ts.

## Next Steps

1. ✅ Create audit document (this file)
2. ✅ Find 3 missing test files (found in `__tests__/stores/`)
3. ⏳ Find remaining 2 files (if original count of 109 was correct)
4. ⏳ Categorize all 107 files
5. ⏳ Verify method migrations
6. ⏳ Update consumers systematically
