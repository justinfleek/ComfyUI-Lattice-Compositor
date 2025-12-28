# CLAUDE.md - FORENSIC AUDIT PROTOCOL v3.0

## 🔒 MANDATORY ANALYSIS FORMAT (NO EXCEPTIONS)

For EVERY function/method, you MUST provide:

### CRASH PATH TRACE (Required)
```
Function: functionName(param1, param2)
Line X: [exact code] → [what happens with bad input]
Line Y: [exact code] → [crash/corruption point]
Result: [TypeError/NaN/Infinity/silent corruption]
```

### What counts as a BUG:
1. **Crash** - TypeError, ReferenceError, RangeError at runtime
2. **Silent corruption** - NaN/Infinity/undefined stored without error
3. **Silent no-op** - Expected behavior doesn't happen, no error/warning
4. **Resource leak** - Memory/handles not cleaned up
5. **Security** - Injection, traversal, prototype pollution

### What does NOT count:
- "TypeScript contract" - Runtime doesn't have types
- "Caller's responsibility" - This file must validate
- "Internal utility" - Still needs defensive code
- "Probably won't happen" - If it CAN happen, it's a bug

### Example of PROPER analysis:
```
Function: setMaterialBlendMode(material, mode)
Line 20: material.blending = THREE.NormalBlending
  - material=null → TypeError: Cannot set properties of null
  - material=undefined → TypeError: Cannot set properties of undefined
  - material={} → Sets property, no crash, but corrupts non-Material object
Result: CRASH on null/undefined, CORRUPTION on wrong type
Verdict: BUG-XXX - No input validation
```

---

## 🛑 MANDATORY OUTPUT FORMAT (EVERY FILE, NO EXCEPTIONS)

After analyzing each file, you MUST output this COMPLETE template. Do not skip any section.

---

### [FILENAME] - ANALYSIS COMPLETE

**Lines read:** [X]
**Bugs found:** [N]

| Bug ID | Line(s) | Function | Issue | Severity |
|--------|---------|----------|-------|----------|
| BUG-XXX | 123 | functionName() | [one-line description] | LOW |
| BUG-YYY | 456-460 | otherFunction() | [one-line description] | MEDIUM |

**Crash Path Traces:**

```
Function: functionName(param1, param2)
Line X: [exact code]
  → param1=null: [exact error or behavior]
  → param1=NaN: [exact error or behavior]
Result: [CRASH/SILENT CORRUPTION/SILENT NO-OP] → BUG-XXX

Function: otherFunction(param)
Line Y: [exact code]
  → param=0: [exact error or behavior]
  → param=Infinity: [exact error or behavior]
Result: [CRASH/SILENT CORRUPTION/SILENT NO-OP] → BUG-YYY
```

**Safe Patterns (brief):**
- Line Z: [what makes it safe]
- Line W: [what makes it safe]

**Files Written (confirm each):**
- [ ] EVIDENCE/BUG-XXX.md created
- [ ] EVIDENCE/BUG-YYY.md created
- [ ] BUGS.md registry entries added
- [ ] BUGS.md summary counts updated
- [ ] FILES_ANALYZED.md entry added
- [ ] PROGRESS.md stats updated
- [ ] PROGRESS.md session log updated

**Checklist complete?** YES / NO

**Next file:** [filename]

---

## ⚠️ RULES FOR THIS FORMAT

1. DO NOT proceed to next file until "Checklist complete? YES"
2. If interrupted mid-file, resume by checking which boxes are incomplete
3. Every [ ] must become [x] before moving on
4. If you find 0 bugs, still complete the format with "VERIFIED CLEAN"
5. Crash path traces are REQUIRED even for clean files (showing what you tested)

---

## 🔧 AUDIT + TEST + FIX PROTOCOL

The audit now TESTS everything AND FIXES bugs as they are found.

### Validation Utilities
All fixes use: `/ui/src/utils/validation.ts`
- `safeNumber(value, default, options)` - SYSTEMIC-004, SYSTEMIC-005
- `safeFps(fps)` - SYSTEMIC-003
- `safeDivide(num, denom, default)` - SYSTEMIC-003
- `safeIndex(index, length)` - SYSTEMIC-002
- `safeFrame(frame, default)` - SYSTEMIC-001
- `framesEqual(a, b)` - SYSTEMIC-001
- `safeLoopCount(count, default, max)` - SYSTEMIC-006
- `isValidObject(obj)` - null checks
- `safeGet(obj, key, default)` - safe property access

### For EXISTING bugs (already documented):
1. Read the EVIDENCE file for the bug
2. Go to the file and line number
3. Apply the appropriate fix pattern
4. Test the fix mentally (what happens with bad input NOW?)
5. Update EVIDENCE file with "## Fix Applied" section
6. Update FIX_TRACKER.md
7. Move to next bug

### For NEW files (not yet audited):
1. Read complete file
2. Run ALL 26 adversarial test categories
3. Find bugs with crash path traces
4. **FIX EACH BUG** using validation utilities
5. Document everything
6. Update all tracking files

### Fix Patterns Reference

**SYSTEMIC-001: NaN Frame Equality**
- Find: `k.frame === frame`
- Replace: `framesEqual(k.frame, frame)`

**SYSTEMIC-002: NaN Bypasses Index Guards**
- Find: `if (index < 0 || index >= length)`
- Replace: `const idx = safeIndex(index, length); if (idx === null) return;`

**SYSTEMIC-003: Division by Zero / fps=0**
- Find: `/ fps` or `1 / fps`
- Replace: `safeDivide(numerator, fps, defaultValue)` or use `safeFps(fps)`

**SYSTEMIC-004: NaN Config Values Stored**
- Find: `this.value = input`
- Replace: `this.value = safeNumber(input, defaultValue, options)`

**SYSTEMIC-005: Math.max/min NaN Bypass**
- Find: `Math.max(0, Math.min(1, value))`
- Replace: `safeNumber(value, defaultValue, { min: 0, max: 1 })`

**SYSTEMIC-006: Unbounded Loop Count**
- Find: `for (let i = 0; i < this.maxParticles; i++)`
- Replace: `const count = safeLoopCount(this.maxParticles, 10000); for (let i = 0; i < count; i++)`

---

## ⚠️ CRITICAL: ALL OUTPUT GOES TO FILES, NOT CHAT

Previous audits failed because findings were lost to conversation compaction.

**NEW RULE: You write to files FIRST, then summarize to chat.**

---

## 📁 REQUIRED FILE STRUCTURE

Before reading ANY source code, create these files:

```
/AUDIT/
├── PROGRESS.md          # Current status, file queue
├── BUGS.md              # All bugs found (append-only)
├── FILES_ANALYZED.md    # Every file with verdict
└── EVIDENCE/            # Code snippets for each bug
    ├── BUG-001.md
    ├── BUG-002.md
    └── ...
```

### Create with this command FIRST:
```bash
mkdir -p AUDIT/EVIDENCE
```

---

## 🔄 ATOMIC WORKFLOW (NEVER SKIP STEPS)

For EVERY source file, you MUST do these steps IN ORDER:

### Step 1: Append to FILES_ANALYZED.md BEFORE reading
```markdown
## [filename] - PENDING
Started: [timestamp]
Lines: TBD
Status: READING
```

### Step 2: Read the file completely
Use view tool. Chunk if needed. Don't proceed until 100% read.

### Step 3: Do 6-category analysis (in your head or scratchpad)

### Step 4: IMMEDIATELY write findings to files

If bugs found → Append to BUGS.md AND create EVIDENCE/BUG-XXX.md
If clean → Update FILES_ANALYZED.md with verdict

### Step 5: Update FILES_ANALYZED.md with final verdict
```markdown
## [filename] - [BUGS FOUND / VERIFIED CLEAN]
Started: [timestamp]
Completed: [timestamp]
Lines: [X]
Bugs: [list or "None"]
Status: COMPLETE
```

### Step 6: Update PROGRESS.md with counts

### Step 7: ONLY THEN move to next file

---

## 📝 BUGS.md FORMAT (APPEND ONLY)

```markdown
# Bug Registry

## BUG-001: [SEVERITY] - [Short Title]
- **File:** /full/path/to/file.ts
- **Lines:** X-Y
- **Type:** [Category]
- **Found:** [timestamp]
- **Evidence:** See EVIDENCE/BUG-001.md

---

## BUG-002: [SEVERITY] - [Short Title]
...
```

**NEVER delete from this file. Only append.**

---

## 📝 EVIDENCE/BUG-XXX.md FORMAT

```markdown
# BUG-XXX: [Title]

## Summary
[One paragraph description]

## Severity: [CRITICAL/HIGH/MEDIUM/LOW]

## Location
- File: [path]
- Lines: [X-Y]
- Function: [name]

## The Bug
[Detailed explanation]

## Code Evidence
```[language]
// Exact code copied from file
// With line numbers as comments
```

## Impact
[What breaks, when, how bad]

## Suggested Fix
[Brief fix approach]
```

---

## 📝 FILES_ANALYZED.md FORMAT

```markdown
# Files Analyzed

## Summary
- Total files: X
- Analyzed: Y
- Bugs found: Z
- Verified clean: W
- Pending: P

---

## /ui/src/types/

### animation.ts - VERIFIED CLEAN
- Lines: 152
- Analyzed: [timestamp]
- Notes: Pure type definitions, no runtime code

### project.ts - VERIFIED CLEAN  
- Lines: 2077
- Analyzed: [timestamp]
- Notes: Type schema, well-organized

---

## /ui/src/stores/actions/

### layerActions.ts - BUGS FOUND
- Lines: 1635
- Analyzed: [timestamp]
- Bugs: BUG-041

### effectActions.ts - VERIFIED CLEAN
- Lines: 212
- Analyzed: [timestamp]
- Evidence: Bounds checking at lines 150-151 handles all edge cases
```

---

## 📝 PROGRESS.md FORMAT

```markdown
# Audit Progress

## Current Status
- **Phase:** [services/effects, stores/actions, etc.]
- **Current file:** [filename]
- **Overall:** X/473 files (Y%)

## Statistics
- Critical bugs: X
- High bugs: Y
- Medium bugs: Z
- Low bugs: W
- Files verified clean: N

## Completed Directories
- [x] types/ - 23/23 files
- [x] stores/ - 36/36 files
- [ ] services/ - 45/173 files (IN PROGRESS)
- [ ] engine/ - 0/60 files
- [ ] components/ - 0/160 files
- [ ] composables/ - 0/18 files
- [ ] workers/ - 0/3 files

## Current Queue
1. [next file]
2. [next file]
...

## Session Log
- [timestamp] Started audit
- [timestamp] Completed types/ directory
- [timestamp] Found BUG-041 in layerActions.ts
- [timestamp] Conversation compacted - all data preserved in files
```

---

## 🛑 COMPACTION SURVIVAL

When conversation compacts, your FIRST action must be:

```
1. Read PROGRESS.md - "Where was I?"
2. Read BUGS.md - "What have I found?"
3. Read FILES_ANALYZED.md - "What's done, what's pending?"
4. Resume from where you left off
```

**The files ARE the audit. Chat is just status updates.**

---

## ⚠️ POST-COMPACTION ADVERSARIAL RESET (READ AFTER EVERY COMPACTION)

You just recovered from compaction. Reset to ADVERSARIAL MODE:

1. **"Well-guarded" is FORBIDDEN** - say "protected by [code] at line [X]"
2. **"No bugs possible" is FORBIDDEN** - there are ALWAYS edge cases
3. **"Verified clean" requires ADVERSARIAL TEST CASES** showing what you tried to break
4. **Every || guard:** What values slip through? (NaN? -1? Infinity?)
5. **Every loop bound:** What if the bound is NaN/Infinity/negative?
6. **Every null check:** What happens in the else branch?
7. **Don't assume delegation = safety.** WRAPPERS MUST VALIDATE INPUTS.
8. **ALWAYS READ THE FULL FILES.** Partial reads do not pass. Chunk if necessary.
9. **Null/undefined analysis requires LINE-BY-LINE evidence table.**
10. **For large files (>500 lines):** group SAFE patterns, list EVERY risk individually.
11. **ONE FILE AT A TIME.** No batching.
12. **After compaction, READ FILES AGAIN** - don't trust summaries.
13. **A bug is a bug** - no dismissing as "minor".

**YOU ARE AUDITING YOUR OWN CODE. Claude wrote this. Don't trust it.**

If you catch yourself praising the code or wanting to skip thorough analysis, STOP.

---

## 🚀 STARTING THE AUDIT

Your first message should be:

```
FORENSIC AUDIT V3 INITIALIZED

Creating audit file structure...
[create directory and files]

Reading PROGRESS.md to check for existing state...
[if empty, start fresh]
[if has data, resume from last position]

Beginning systematic analysis.
All findings will be written to files immediately.
Chat output is summary only - files are source of truth.
```

Then:
1. Create /AUDIT/ directory structure
2. Initialize all .md files with headers
3. Build file inventory (list all 473 files)
4. Begin reading in priority order

---

## 📋 6-CATEGORY CHECKLIST (Reference)

For each file, verify:

1. **Error Handling**
   - Try/catch coverage
   - Graceful degradation
   
2. **Loops & Iteration**
   - Termination guaranteed
   - No unbounded user input
   
3. **Input Validation**
   - Parameters validated
   - Bounds checked
   
4. **Null/Undefined**
   - Optional chaining used
   - Non-null assertions (!) justified
   
5. **Async Operations**
   - Promises handled
   - Race conditions checked
   
6. **State & Side Effects**
   - Global state identified
   - Cleanup verified

---

## 💀 RULES THAT CANNOT BE BROKEN

1. **NEVER say "no bugs found" without writing to FILES_ANALYZED.md first**
2. **NEVER move to next file without updating all tracking files**
3. **NEVER output a bug to chat without FIRST writing to BUGS.md and EVIDENCE/**
4. **NEVER skip the 6-category checklist**
5. **NEVER trust previous session memory - always read from files**
6. **NEVER mark a file "VERIFIED CLEAN" without completing Rule 14 adversarial input testing**
7. **NEVER reuse a bug ID** - Check BUGS.md for highest existing ID before assigning new ones
8. **NEVER mark a bug "FIXED" without grep/read verification** - Must show line number with fix code
9. **BUGS.md is the SINGLE SOURCE OF TRUTH** - FIX_TRACKER.md must match it exactly
10. **NEVER batch multiple files in one analysis** - Complete one file fully before starting next
11. **After ANY compaction, reconcile FIX_TRACKER against BUGS.md** - IDs must match

---

## 🔄 FRESH START PROTOCOL (Full Re-Audit)

When starting a complete re-audit of the entire codebase:

### Step 1: Archive Old Audit Data
```bash
mv AUDIT AUDIT_ARCHIVED_$(date +%Y%m%d)
mkdir -p AUDIT/EVIDENCE
```

### Step 2: Initialize Fresh Tracking Files
- BUGS.md: Start with `## Summary` header, bug count = 0
- FILES_ANALYZED.md: Empty, ready for entries
- PROGRESS.md: Fresh status with 0/N files
- FIX_TRACKER.md: Empty, will be populated as bugs are found and fixed

### Step 3: Build Complete File Inventory
```bash
find ui/src -name "*.ts" -o -name "*.vue" | wc -l
```
Record exact count in PROGRESS.md

### Step 4: Systematic Processing Order
1. Types first (establish contracts)
2. Utils/helpers (shared validation)
3. Services (business logic)
4. Stores (state management)
5. Engine (rendering)
6. Components (UI)
7. Composables (Vue hooks)
8. Workers (threading)

### Step 5: Per-File Protocol
For EACH file:
1. Add PENDING entry to FILES_ANALYZED.md
2. Read ENTIRE file (chunk if >1000 lines)
3. Run Rule 14 A-Z tests on EVERY public function
4. Document bugs with UNIQUE IDs (check max ID first)
5. Apply fixes using validation.ts utilities
6. Verify fix with grep showing new code
7. Update all tracking files
8. Mark file COMPLETE
9. ONLY THEN proceed to next file

---

## 🎯 RULE 14: MANDATORY ADVERSARIAL INPUT TESTING

For EVERY public method/function, you MUST test ALL applicable input types:

### 14A: Numeric Inputs
| Test Value | Why It Breaks Things |
|------------|---------------------|
| `0` | Division by zero, empty loops, falsy checks |
| `-1` | Array index -1, negative counts, sign flip bugs |
| `NaN` | Comparisons always false, propagates through math |
| `Infinity` / `-Infinity` | Infinite loops, memory exhaustion |

### 14B: String Inputs
| Test Value | Why It Breaks Things |
|------------|---------------------|
| `""` (empty) | Falsy, .length=0, split() returns [""] |
| Very long string (1MB+) | Memory, performance, buffer overflow |
| Unicode/emoji | Encoding issues, .length lies (surrogate pairs) |
| Special chars `<>'"&\` | XSS, injection, escaping bugs |
| `null` / `undefined` | Type coercion to "null" or crash |

### 14C: Array Inputs
| Test Value | Why It Breaks Things |
|------------|---------------------|
| `[]` (empty) | .length=0, [0] undefined, reduce() throws |
| Single element `[x]` | Off-by-one in loops |
| Sparse `[1,,3]` | forEach skips holes, map doesn't |
| Contains `null`/`undefined` | Element access crashes |
| Very large (100k+ elements) | Performance cliff, memory |

### 14D: Object Inputs
| Test Value | Why It Breaks Things |
|------------|---------------------|
| `{}` (empty) | Missing required properties |
| Missing properties | `obj.prop.sub` crashes |
| `null` / `undefined` | Cannot read property of null |
| Circular references | JSON.stringify throws, infinite loops |

### 14E: Async/State Edge Cases
| Scenario | Why It Breaks Things |
|----------|---------------------|
| Operation cancelled mid-flight | Dangling promises, state corruption |
| Rapid repeated calls | Race conditions, stale closures |
| Component unmounts during async | Memory leaks, setState on unmounted |
| Concurrent modifications | State inconsistency |

### 14F: Resource Exhaustion
| Scenario | Why It Breaks Things |
|----------|---------------------|
| 10,000+ items | O(n²) algorithms explode |
| WebGL context loss | Browser reclaims under pressure |
| Disk full / network timeout | Unhandled I/O errors |

### 14G: Boundary Conditions
| Test | Why It Breaks Things |
|------|---------------------|
| Off-by-one (`array[length]` vs `[length-1]`) | Index out of bounds |
| First/last element (frame 0, final frame) | Edge case logic errors |
| Exactly at threshold (`if x > 100`, test `x=100`) | Fence-post errors |
| `Number.MAX_SAFE_INTEGER` | Integer overflow in calculations |
| Min/max of ranges | Boundary logic failures |

### 14H: Type Coercion Traps
| Test | Why It Breaks Things |
|------|---------------------|
| `"5" + 5` = `"55"` | String concat instead of math |
| `[] == false` but `!![]` = true | Truthy/falsy confusion |
| Object keys become strings | `obj[1]` same as `obj["1"]` |
| `typeof null === "object"` | Null check failures |
| `Number("") === 0` | Empty string coerces to 0 |

### 14I: Ordering/Timing
| Test | Why It Breaks Things |
|------|---------------------|
| init() called twice | Double initialization, leaks |
| Methods called BEFORE init() | Null refs, undefined state |
| Operations AFTER dispose() | Use-after-free pattern |
| Event A assumed before B | Race condition logic |
| Callbacks fire in wrong order | State assumptions broken |

### 14J: Lifecycle/Cleanup
| Test | Why It Breaks Things |
|------|---------------------|
| dispose() called twice | Double-free crashes |
| dispose() never called | Memory/resource leak |
| Partial init failure | Cleanup of half-initialized state |
| Re-init after dispose | Resurrection bugs |
| Parent disposed before child | Orphaned references |

### 14K: Error Recovery State
| Test | Why It Breaks Things |
|------|---------------------|
| State after exception thrown | Corrupted mid-operation state |
| catch/finally cleanup | Resource leaks on error path |
| Retry after failure | Stale state from previous attempt |
| Partial operation rollback | Half-committed changes |
| Error in error handler | Unhandled exception cascade |

### 14L: Security Patterns
| Test | Why It Breaks Things |
|------|---------------------|
| `__proto__` / `constructor.prototype` | Prototype pollution |
| `../../../etc/passwd` in paths | Path traversal |
| ReDoS patterns `(a+)+$` | Regex catastrophic backtracking |
| Untrusted data in eval/Function | Code injection |
| innerHTML with user data | XSS vulnerabilities |

### 14M: Concurrency
| Test | Why It Breaks Things |
|------|---------------------|
| Same operation started twice simultaneously | Race conditions |
| TOCTOU (check then use) | State changed between check and use |
| Shared mutable state in async | Concurrent modification |
| Lock/mutex missing | Data corruption |
| Deadlock potential | System freeze |

### 14N: Floating Point Precision
| Test | Why It Breaks Things |
|------|---------------------|
| `0.1 + 0.2 !== 0.3` | Precision comparison failures |
| Very small (`1e-300`) | Underflow to zero |
| Very large (`1e+300`) | Overflow, precision loss |
| Epsilon comparisons | `Math.abs(a-b) < 0.0001` edge cases |
| Accumulated error over iterations | Matrix math drift |

### 14O: Time/Animation Specific
| Test | Why It Breaks Things |
|------|---------------------|
| Frame 0, frame -1, last frame | Boundary logic |
| Backwards playback (speed < 0) | Reversed iteration assumptions |
| Speed = 0 (paused) | Division by zero, stuck state |
| Very high frame rates (120fps+) | Timing assumptions |
| Sub-frame interpolation (frame 1.5) | Integer cast truncation |
| Loop boundaries (last→first frame) | Discontinuity bugs |

### 14P: WebGL/GPU Specific
| Test | Why It Breaks Things |
|------|---------------------|
| Context loss mid-render | Resources become invalid |
| Texture size > MAX_TEXTURE_SIZE | Silent failure or crash |
| Shader compile failure | Fallback missing |
| Framebuffer incomplete | Missing attachment error |
| Too many draw calls | Performance cliff |
| VRAM exhaustion | Textures evicted silently |

### 14Q: Serialization/Persistence
| Test | Why It Breaks Things |
|------|---------------------|
| Circular references in JSON | stringify throws |
| Missing fields after schema change | undefined access |
| Corrupted file headers | Parse failure cascade |
| Version mismatch | Migration bugs |
| Partial save (crash mid-write) | Corrupted state on reload |
| Very large file (100MB+) | Memory exhaustion on load |

### 14R: DOM/UI Specific
| Test | Why It Breaks Things |
|------|---------------------|
| Element removed mid-operation | Null reference |
| Resize during render | Stale dimensions |
| Focus lost unexpectedly | Keyboard state stuck |
| Scroll position edge cases | Off-screen element access |
| Very long text without bounds | Layout overflow/break |
| Z-index stacking conflicts | Hidden elements |

### 14S: Event/Listener Patterns
| Test | Why It Breaks Things |
|------|---------------------|
| Listener not removed on cleanup | Memory leak |
| Event fired during handler (reentrant) | Infinite loop, corruption |
| stopPropagation side effects | Other handlers skipped |
| Event fired on destroyed object | Null reference |
| Too many listeners on one event | Performance degradation |

### 14T: Mathematical Edge Cases
| Test | Why It Breaks Things |
|------|---------------------|
| `-5 % 3` negative modulo | Different than expected (-2 vs 1) |
| `atan2(0, 0)` | Undefined angle |
| Matrix with determinant = 0 | Inverse fails, NaN propagation |
| Quaternion normalization drift | Accumulated error |
| Bezier curve at t=0, t=1 exactly | Endpoint tangent handling |
| Log/sqrt of negative numbers | NaN result |

### 14U: Composition/Nesting
| Test | Why It Breaks Things |
|------|---------------------|
| Deeply nested comps (100+ levels) | Stack overflow |
| Circular composition reference | Infinite recursion |
| Empty composition (0 layers) | Nothing to iterate |
| Composition with 1000+ layers | O(n²) algorithm explosion |
| Mixed frame rates in nesting | Time calculation errors |
| Self-referencing composition | Infinite loop |

### 14V: State Machine/Workflow
| Test | Why It Breaks Things |
|------|---------------------|
| Invalid state transition | Unexpected state reached |
| Operation during transition | Partial/inconsistent state |
| Missing state handler | Silent failure, stuck state |
| State machine reset mid-operation | Orphaned resources |
| Concurrent state transitions | Race to invalid state |

### 14W: Caching/Memoization
| Test | Why It Breaks Things |
|------|---------------------|
| Stale cache after mutation | Wrong data returned |
| Cache key collision | Wrong cached value used |
| Cache eviction during use | Dangling reference |
| Cache never invalidated | Memory leak, stale data |
| Cache size unbounded | Memory exhaustion |

### 14X: Platform/Environment
| Test | Why It Breaks Things |
|------|---------------------|
| Safari WebGL quirks | Different shader behavior |
| Firefox audio API differences | Timing variations |
| Mobile GPU limitations | Features missing/different |
| High DPI (2x, 3x scale) | Coordinate scaling bugs |
| Low memory device | OOM crashes |
| Older browser versions | Missing APIs |

### 14Y: Configuration/Settings
| Test | Why It Breaks Things |
|------|---------------------|
| Missing config value | undefined property access |
| Invalid config combination | Conflicting settings |
| Config changed mid-operation | Inconsistent state |
| Default value wrong type | Type error downstream |
| Config file corrupted | Partial load, bad state |

### 14Z: Inheritance/Polymorphism
| Test | Why It Breaks Things |
|------|---------------------|
| Super not called in constructor | Parent state missing |
| Method override incomplete | Base behavior lost |
| Abstract method not implemented | Runtime error |
| `this` binding lost in callbacks | Wrong context, undefined |
| Diamond inheritance issues | Ambiguous method resolution |
| Prototype chain corruption | Method lookup fails |

### Required Format in FILES_ANALYZED.md

```markdown
- Rule 14 Adversarial Tests:
  | Method | Parameter | Type | Test Cases | Result |
  |--------|-----------|------|------------|--------|
  | setFPS | fps | number | 0:DIV/0, NaN:PROPAGATES | **BUG** |
  | setName | name | string | "":OK, null:CRASH | **BUG** |
  | setLayers | layers | array | []:OK, sparse:OK | SAFE |
```

### "Delegates to X" is NOT an excuse
If your file accepts a parameter and passes it to another system without validation, YOUR FILE has a bug. The wrapper is responsible for validating inputs before delegation.

### No shortcuts after compaction
This rule exists because previous sessions marked files "clean" without proper testing. If you catch yourself wanting to skip this, STOP and do it anyway.

---

## 🔍 PRIORITY ORDER

1. `services/expressions/` - Code execution risk (CRITICAL)
2. `services/effects/` - Performance cliffs, canvas bugs
3. `stores/actions/` - State management
4. `engine/layers/` - Render pipeline
5. `engine/particles/` - Complex simulation
6. `services/` (remaining) - Business logic
7. `components/` - UI, memory leaks
8. `composables/` - Vue hooks
9. `workers/` - Threading
10. `types/` - Usually clean, do last

---

**THE FILES ARE THE AUDIT. CHAT IS DISPOSABLE. WRITE EVERYTHING DOWN.**

---

## ✅ VERIFICATION CHECKLIST (Run After Each Session)

Before ending any audit session, verify:

### Bug ID Integrity
```bash
# Check for duplicate bug IDs in BUGS.md
grep -oP 'BUG-\d+' AUDIT/BUGS.md | sort | uniq -d
# Should output NOTHING - any output means duplicate IDs exist
```

### Fix Verification
For each bug marked "FIXED" in FIX_TRACKER.md:
1. Read the EVIDENCE file for the fix pattern
2. Grep the source file for the fix code
3. Confirm line numbers match
4. If grep finds nothing, bug is NOT actually fixed

### Documentation Sync
- [ ] BUGS.md bug count matches actual entries
- [ ] FIX_TRACKER.md references only bugs that exist in BUGS.md
- [ ] FILES_ANALYZED.md lists every file touched this session
- [ ] PROGRESS.md has current session log entry

### Build Verification
```bash
npm run build 2>&1 | tail -5
# Must show "built in X.XXs" with no errors
```

---

## 🚨 LESSONS LEARNED (Do Not Repeat)

### Documentation Drift (2025-12-28)
**Problem:** BUGS.md contained duplicate bug IDs (BUG-029-049 appeared twice with different meanings). FIX_TRACKER.md tracked the wrong set, leaving real bugs unfixed.

**Prevention:**
1. Always check `grep -oP 'BUG-\d+' BUGS.md | sort | uniq -d` for duplicates
2. When assigning new bug ID, first find max: `grep -oP 'BUG-\d+' BUGS.md | sort -t- -k2 -n | tail -1`
3. Never copy-paste bug entries - always append fresh

### False "Fixed" Claims (2025-12-28)
**Problem:** Bugs marked [x] fixed in tracker but code showed no validation.

**Prevention:**
1. Before marking fixed: `grep "Number.isFinite\|safeNumber\|validate" file.ts`
2. Must see actual code at claimed line number
3. **DO NOT TRUST. VERIFY EVERYTHING.** Read the actual code.

---

## 🔥 ADVERSARIAL MINDSET (MANDATORY)

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

### Required Behavior
1. **Assume every parameter is NaN, null, undefined, Infinity, -1, empty, or malicious**
2. **Trace every code path to its crash point**
3. **Question every assumption in comments**
4. **Test boundary conditions explicitly**
5. **If you can imagine it failing, it WILL fail**

### Self-Check Questions (Ask After Every File)
- "What input would crash this?"
- "What input would corrupt state silently?"
- "What input would cause infinite loop?"
- "What input would leak memory?"
- "What if this runs during dispose?"
- "What if this runs before init?"
- "What if this runs twice simultaneously?"

**If you cannot answer these questions with specific line numbers and code evidence, YOU ARE NOT DONE.**