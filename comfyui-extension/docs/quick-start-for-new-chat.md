# Quick Start Guide for New Chat Sessions

> **Purpose:** Enable seamless continuation of work across chat sessions  
> **Last Updated:** 2026-01-19  
> **Status:** Active reference document

---

## 🎯 Current Focus: Phase 5.6 - Null/Undefined Return Elimination

**Protocol:** System F/Omega-level code - PureScript/Lean4 rigor with strong proofs  
**Goal:** Eliminate ALL `return null` and `return undefined` patterns, replacing with explicit error throwing

### Current Progress (2026-01-19 - UPDATED)
- ✅ **Fixed:** 363 critical functions across services, stores, engine, composables, utils, types, main, and Vue components
- ✅ **Vue Components:** 58 instances fixed (ThreeCanvas.vue, PathSuggestionDialog.vue, PropertiesPanel.vue, ProjectPanel.vue, and others)
- ✅ **Remaining:** 12 instances total (9 Vue wrapper exceptions + 3 valid service exceptions)
- 📊 **Total Remaining:** 12 instances across entire codebase (9 files, verified via PowerShell Get-ChildItem/Select-String 2026-01-19)

### Key Files Recently Fixed
- ✅ `effectProcessor.ts` - EffectCache.get() (3 instances)
- ✅ `segmentToMask.ts` - segmentationToMask() (3 instances)  
- ✅ `svgExtrusion.ts` - createFilletCapGeometry() (3 instances - USER FIXED)
- ✅ `timelineSnap.ts` - findSnapTarget() (2 instances - USER FIXED)
- 🔄 `layerContentExpressions.ts` - effectValue() (3 instances - IN PROGRESS)

---

## 📚 Essential Documentation

### 1. **MASTER_REFACTOR_STATUS.md** - Current State
- **Location:** `docs/MASTER_REFACTOR_STATUS.md`
- **Purpose:** Tracks all progress, current counts, and what's done vs. not done
- **Key Sections:**
  - Phase 5.6 status (line ~1159)
  - Lazy code pattern counts (line ~7)
  - File-by-file progress tracking

### 2. **MASTER_REFACTOR_PLAN.md** - Overall Strategy
- **Location:** `docs/MASTER_REFACTOR_PLAN.md`
- **Purpose:** Complete refactoring plan and architecture
- **Key Sections:**
  - Executive Summary
  - Execution Phases
  - Store Architecture

### 3. **Protocol Documents**
- **EVIDENCE_BASED_ANALYSIS_METHODOLOGY.md** - How to analyze code
- **BULLETPROOF_CODEBASE_GUIDE.md** - Coding standards and principles
- **.cursor/rules/core.mdc** - Cursor IDE rules (auto-applied)
- **AGENTS.md** - Build/test commands and style guidelines

---

## 🔧 Current Protocol (System F/Omega)

### Core Principles
1. **NO LAZY FIXES** - Zero shortcuts, zero simple fixes
2. **Explicit Error Throwing** - Never return `null` or `undefined`
3. **Strong Proofs** - Every fix includes:
   - `System F/Omega proof` comments
   - `Type proof` comments  
   - `Mathematical proof` comments
   - `Geometric proof` / `Physics proof` / `Pattern proof` where applicable
4. **Rich Error Messages** - Include context, file names, exact values, actionable info

### Pattern to Follow
```typescript
// OLD (LAZY):
function getValue(): Value | null {
  if (!condition) return null;
  return value;
}

// NEW (SYSTEM F/OMEGA):
function getValue(): Value {
  // System F/Omega proof: Explicit validation of condition
  // Type proof: condition ∈ boolean → value ∈ Value (non-nullable)
  // Mathematical proof: Condition must be true to retrieve value
  if (!condition) {
    throw new Error(
      `[ServiceName] Cannot get value: Condition not met. ` +
      `Condition: ${condition}, required: true. ` +
      `Context: [specific details about what failed and why].`
    );
  }
  return value;
}
```

### Caller Pattern (when "no result" is expected)
```typescript
// Wrap in try/catch for expected "no result" cases
try {
  const result = getValue();
  // Use result
} catch (error) {
  // Handle "no result" case explicitly
  logger.warn(`[Caller] Value not available:`, error instanceof Error ? error.message : String(error));
  // Use fallback or skip operation
}
```

---

## 📊 Current Lazy Code Pattern Counts (2026-01-19)

| Pattern | Count | Status |
|---------|-------|--------|
| `return null`/`return undefined` | ~228 remaining | 🔄 IN PROGRESS |
| `??` (Nullish Coalescing) | 553 prod | ⚠️ PENDING |
| `?.` (Optional Chaining) | 1,318 prod | ⚠️ PENDING |
| `!` (Non-null Assertions) | 5,615 prod | ⚠️ PENDING |
| `as any`/`: any` | 85 total | ⚠️ PENDING |
| `as unknown as` | 2 prod | ⚠️ PENDING |
| `|| 0` | 0 prod | ✅ COMPLETE |
| `|| []` | 97 | ⚠️ PENDING |
| `|| {}` | 11 | ⚠️ PENDING |

**Note:** Many `?.` and `!` patterns may be justified. Focus on truly problematic ones first.

---

## 🎯 Next Steps (Priority Order)

1. **Continue Phase 5.6** - Fix remaining `return null`/`return undefined`:
   - `layerContentExpressions.ts` (3 instances)
   - `colorManagement/ColorProfileService.ts` (2 instances)
   - `particleSystem.ts` (2 instances)
   - `visionAuthoring/MotionIntentTranslator.ts` (2 instances)
   - `video/transitions.ts` (2 instances)
   - `shape/pathModifiers.ts` (2 instances)
   - Remaining single-instance files (18 files)

2. **Verify TypeScript Errors** - Run `vue-tsc --noEmit` after each batch
3. **Update MASTER_REFACTOR_STATUS.md** - Update counts after each session
4. **Continue with Next Phase** - After Phase 5.6 complete, move to next lazy pattern

---

## ⚠️ Critical Rules

1. **ALWAYS run `vue-tsc --noEmit` after code changes**
2. **ALWAYS update MASTER_REFACTOR_STATUS.md with accurate counts**
3. **NEVER use `as unknown as` or `as any`** - Use proper type guards
4. **NEVER return `null` or `undefined`** - Throw explicit errors
5. **ALWAYS include proof comments** - System F/Omega, Type, Mathematical proofs
6. **ALWAYS provide rich error messages** - Context, values, actionable info

---

## 🔍 Verification Commands

```bash
# Count remaining return null/undefined in services
grep -r "return null\|return undefined" ui/src/services | wc -l

# Count across entire codebase
grep -r "return null\|return undefined" ui/src | wc -l

# Type check
cd ui && vue-tsc --noEmit

# Format check
cd ui && npx biome check
```

---

## 📝 Session Checklist

When starting a new session:
- [ ] Read `docs/MASTER_REFACTOR_STATUS.md` (latest section)
- [ ] Read `docs/QUICK_START_FOR_NEW_CHAT.md` (this file)
- [ ] Verify current counts with grep
- [ ] Check what was last worked on
- [ ] Continue from where previous session left off
- [ ] Update status doc at end of session

---

**Reference:** See `docs/MASTER_REFACTOR_STATUS.md` for complete progress tracking and `docs/MASTER_REFACTOR_PLAN.md` for overall strategy.
