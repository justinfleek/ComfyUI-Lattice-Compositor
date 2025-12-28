# Audit Progress - FULL RE-AUDIT v4.0

## 🔥 ADVERSARIAL MINDSET (READ EVERY SESSION)

**YOU WROTE THIS CODE. YOU ARE TRYING TO BREAK IT.**

### Mental Model
- Every function is guilty until proven innocent
- Every input is malicious until validated
- Every "it should never happen" WILL happen
- Every shortcut you took is a bug waiting to trigger
- Every edge case you dismissed is a crash waiting to happen

### Forbidden Phrases
- "This is probably fine" → NO. PROVE IT.
- "The caller handles this" → NO. VALIDATE HERE.
- "TypeScript prevents this" → NO. RUNTIME HAS NO TYPES.
- "This would never happen in practice" → MAKE IT HAPPEN. TEST IT.
- "I already checked this" → CHECK IT AGAIN.
- "The documentation says..." → THE CODE IS THE TRUTH.

### Self-Check Questions (Ask After Every File)
- "What input would crash this?"
- "What input would corrupt state silently?"
- "What input would cause infinite loop?"
- "What input would leak memory?"
- "What if this runs during dispose?"
- "What if this runs before init?"
- "What if this runs twice simultaneously?"

**If you cannot answer these with LINE NUMBERS and CODE, YOU ARE NOT DONE.**

---

## Current Status
- **Phase:** FRESH RE-AUDIT STARTING
- **Current file:** None - initializing
- **Overall:** 0/506 files (0%)

## File Inventory (506 files - ALL FILES, NOTHING EXCLUDED)

| Directory | Files | Priority | Status |
|-----------|-------|----------|--------|
| services/expressions/ | 17 | CRITICAL | [ ] |
| services/effects/ | 17 | HIGH | [ ] |
| services/ (other) | 140 | HIGH | [ ] |
| stores/actions/ | 25 | HIGH | [ ] |
| stores/ (other) | 11 | MEDIUM | [ ] |
| engine/layers/ | 25 | HIGH | [ ] |
| engine/particles/ | 18 | HIGH | [ ] |
| engine/core/ | 5 | MEDIUM | [ ] |
| engine/ (other) | 12 | MEDIUM | [ ] |
| components/ | 160 | MEDIUM | [ ] |
| composables/ | 18 | LOW | [ ] |
| types/ | 23 | LOW | [ ] |
| utils/ | 8 | HIGH | [ ] |
| workers/ | 3 | LOW | [ ] |
| __tests__/ | 18 | LOW | [ ] |
| __mocks__/ | 1 | LOW | [ ] |
| Other (main.ts, App.vue, config/, styles/, vite-env.d.ts) | 5 | LOW | [ ] |

**TOTAL: 506 files - nothing excluded**

## Statistics
- Files analyzed: 0
- Bugs found: 0
- Bugs fixed: 0
- Files verified clean: 0
- Critical bugs: 0
- High bugs: 0
- Medium bugs: 0
- Low bugs: 0

## Processing Order

### Phase 1: Critical Security (services/expressions/)
17 files - Code execution, sandbox escape risk
```
1. expressionEvaluator.ts (CRITICAL - sandbox)
2. expressionValidation.ts
3. expressionHelpers.ts
4. expressionNamespaces.ts
5. expressionPresets.ts
6. easing.ts
7. audioExpressions.ts
8. coordinateConversion.ts
9. jitterExpressions.ts
10. loopExpressions.ts
11. motionExpressions.ts
12. textAnimator.ts
13. vectorMath.ts
14. layerContentExpressions.ts
15. types.ts
16. index.ts
17. expressions.ts (root service)
```

### Phase 2: Effects Pipeline (services/effects/)
17 files - Canvas/WebGL corruption, performance cliffs

### Phase 3: State Management (stores/)
36 files - Data corruption, invalid state

### Phase 4: Render Engine (engine/)
60 files - GPU crashes, memory leaks

### Phase 5: Utils & Validation
8 files - Foundation for all fixes

### Phase 6: UI Layer (components/)
160 files - Memory leaks, event handling

### Phase 7: Vue Composables
18 files - Reactive state issues

### Phase 8: Type Definitions
23 files - Usually clean, verify contracts

### Phase 9: Workers & Misc
8 files - Threading issues

## Session Log
- 2025-12-28 FULL RE-AUDIT INITIALIZED
- Previous audit had documentation drift (duplicate bug IDs, incorrect fix tracking)
- Starting fresh with strict protocols from CLAUDE.md v4.0
- All previous analysis archived, starting from 0/506
- Corrected file count: 506 (not 487 - include ALL files)

## Rules For This Audit
1. ONE file at a time, fully complete before next
2. EVERY public function gets Rule 14 A-Z testing
3. BUGS.md is single source of truth
4. NEVER reuse bug IDs
5. VERIFY fixes with grep before marking [x]
6. After compaction: read ALL tracking files first
7. Build must pass after every fix batch
