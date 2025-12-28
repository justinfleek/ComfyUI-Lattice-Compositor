# Bug Registry - FULL RE-AUDIT v4.0

## Summary
- Total bugs: 11
- Critical: 0
- High: 0
- Medium: 11
- Low: 0
- Fixed: 11
- Unfixed: 0

## Rules
1. **NEVER reuse bug IDs** - Always increment from highest existing
2. **Every bug gets EVIDENCE file** - EVIDENCE/BUG-XXX.md
3. **Single source of truth** - FIX_TRACKER must reference these IDs exactly
4. **Append only** - Never delete entries, mark as INVALID if needed

---

## Bug Format

```markdown
## BUG-XXX: [SEVERITY] - [Short Title]
- **File:** /full/path/to/file.ts
- **Lines:** X-Y
- **Function:** functionName()
- **Type:** [CRASH/CORRUPTION/LEAK/SECURITY/INFINITE-LOOP]
- **Found:** [timestamp]
- **Fixed:** [x] 2025-12-28 or [x] with date
- **Evidence:** See EVIDENCE/BUG-XXX.md

**Crash Path:**
Line X: `code here`
  → input=NaN: result
  → input=null: result
```

---

## Bugs

*Previous bugs (BUG-001 through BUG-175) documented in BUGS_ARCHIVED_20251228.md and EVIDENCE/*

---

## BUG-176: MEDIUM - Division by Zero in periodic()
- **File:** ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 61-63
- **Function:** timeExpressions.periodic()
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-176.md

**Crash Path:** `return (time % period) / period;` → period=0 → NaN

---

## BUG-177: MEDIUM - NaN Propagation in Wave Functions
- **File:** ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 65-78
- **Function:** sawtooth(), triangle(), square()
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-177.md

**Crash Path:** `time * Infinity` → `Infinity - Infinity` → NaN

---

## BUG-178: MEDIUM - NaN Bypasses Clamp in smoothstep()
- **File:** ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 115-118
- **Function:** mathExpressions.smoothstep()
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-178.md

**Crash Path:** `(x - edge0) / (edge1 - edge0)` → edge1=edge0 → div/0 → NaN bypasses clamp

---

## BUG-179: MEDIUM - NaN Bypasses Clamp in smootherstep()
- **File:** ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 120-123
- **Function:** mathExpressions.smootherstep()
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-179.md

**Crash Path:** Same as BUG-178

---

## BUG-180: MEDIUM - Division by Zero in mod()
- **File:** ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 125-127
- **Function:** mathExpressions.mod()
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-180.md

**Crash Path:** `((a % b) + b) % b` → b=0 → NaN

---

## BUG-181: MEDIUM - Math.max Doesn't Protect NaN in gaussRandom()
- **File:** ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 153-162
- **Function:** mathExpressions.gaussRandom()
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-181.md

**Crash Path:** `Math.max(0.0001, seededRand(NaN))` → Math.max(0.0001, NaN) → NaN

---

## BUG-182: MEDIUM - NaN Bypasses Normalization in expressionEase()
- **File:** ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 173-192
- **Function:** expressionEase()
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-182.md

**Crash Path:** `(t - tMin) / (tMax - tMin)` → tMax=tMin → NaN bypasses Math.max/min

---

## BUG-183: MEDIUM - NaN Bypasses Normalization in expressionEaseIn()
- **File:** ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 197-214
- **Function:** expressionEaseIn()
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-183.md

**Crash Path:** Same as BUG-182

---

## BUG-184: MEDIUM - NaN Bypasses Normalization in expressionEaseOut()
- **File:** ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 219-236
- **Function:** expressionEaseOut()
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-184.md

**Crash Path:** Same as BUG-182

---

## BUG-185: MEDIUM - Division by fps in createThisCompObject()
- **File:** ui/src/services/expressions/expressionEvaluator.ts
- **Lines:** 339-342
- **Function:** createThisCompObject()
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-185.md

**Crash Path:** `frameDuration: 1 / ctx.fps` → fps=0 → Infinity; fps=NaN → NaN

---

## BUG-186: MEDIUM - No Input Validation in All Easing Functions
- **File:** ui/src/services/expressions/easing.ts
- **Lines:** 27-218, 377-430
- **Function:** ALL 30+ easing functions
- **Type:** CORRUPTION
- **Found:** 2025-12-28
- **Fixed:** [x] 2025-12-28
- **Evidence:** See EVIDENCE/BUG-186.md

**Crash Path:** `easeInSine(NaN)` → `1 - Math.cos(NaN * Math.PI / 2)` → NaN propagation

---
