# Evidence-Based Analysis Methodology

> **Purpose:** Standard methodology for code analysis and refactoring work
> **Created:** 2026-01-10
> **Status:** Active

---

## Core Principles

### 1. Trace Everything Back to Source

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

---

### 2. Verify Before Creating

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

---

### 3. Show Exact Traces

**Rule:** When making changes, show:
1. What was read (file paths, line ranges)
2. What was verified (exact code snippets)
3. What was changed (before/after)
4. Why it was changed (evidence-based reasoning)

**Format:**
```
**File:** `path/to/file.ts` (MODIFIED/NEW)
**Changes:**
- **Line X-Y:** Added/Modified/Removed
- **Reason:** Evidence from line Z in file A

**Verification Traces:**
- Read: `file1.ts:100-150`
- Compared: `file2.ts:200-250`
- Verified: `file3.ts:50-75`
```

---

### 4. Connect to Master Plan

**Rule:** Every task must reference:
1. Master Refactor Plan phase/section
2. Why it's not myopic (how it fits bigger picture)
3. Steps back to main refactor
4. Time estimates

**Format:**
```
**Master Plan Reference:** Phase X (Weeks Y-Z) - Section Name
**Why Not Myopic:**
- Foundation before refactoring (explain)
- Prevents silent failures (explain)
- Enables systematic work (explain)

**Steps Back to Main Refactor:**
1. Complete current task (time estimate)
2. Next verification step (time estimate)
3. Return to Phase X (reference)
```

---

### 5. Document Assumptions and Gaps

**Rule:** Explicitly state:
1. What was verified
2. What was assumed
3. What needs verification
4. What might be wrong

**Format:**
```
**Verified:**
- ✅ Property names match tensor inputs (lines X-Y)
- ✅ Export functions produce correct format (lines A-B)

**Assumed:**
- ⚠️ Node expects JSON string (needs verification)
- ⚠️ Format matches documentation (needs verification)

**Needs Verification:**
- ❓ Actual ComfyUI node source code
- ❓ Runtime behavior
```

---

## Output Format Template

### Summary Section
```
## Summary: [Task Name]

### Changes Made (with Exact Traces)

**1. [Change Name]**
- **File:** `path/to/file.ts` (NEW/MODIFIED, X lines)
- **Verification Traces:**
  - **Line X:** Description
  - **Source:** `file.ts:X`
  - **Compared:** `other-file.ts:Y`
- **Result:** What was achieved
```

### Why Not Myopic Section
```
### Why This Is Not Myopic

**1. [Reason Name]**
- **Master Plan Reference:** Phase X, Section Y
- **Current Work:** What we're doing
- **Why Critical:** Why it matters
- **Impact:** What it prevents/enables
```

### Next Steps Section
```
### Next Step (with Master Refactor Reference)

**Immediate:** [Task] (time estimate)
- **Issue:** What needs fixing
- **File:** Where to make changes
- **Action:** What to do

**After That:** [Next task] (time estimate)

**Then Return to Main Refactor:**
- **Reference:** `docs/MASTER_REFACTOR_PLAN.md` - Phase X
- **Checklist:** What to verify
- **Exit Criteria:** When complete
- **Time Estimate:** How long
```

### Steps Back Section
```
### Steps Back to Main Refactor

**1. [Current Task]** (time estimate)
- What to complete
- How to verify

**2. [Next Task]** (time estimate)
- What comes next
- Dependencies

**3. [Return Point]** (reference)
- Phase/section to return to
- What to check
```

---

## Anti-Patterns to Avoid

### ❌ Don't Do This:
- Create files without checking what exists
- Make claims without line number references
- Suggest options without recommending best path
- Work in isolation without master plan context
- Assume without verifying

### ✅ Do This Instead:
- Search codebase first
- Show exact traces (file:line)
- Give single best next step
- Reference master plan phases
- Verify assumptions

---

## Usage Instructions

**For AI Assistants:**
1. Read this methodology before starting work
2. Follow the output format template
3. Always show exact traces
4. Always connect to master plan
5. Always show path back to main refactor

**For Human Reviewers:**
1. Check that traces are exact (file:line)
2. Verify master plan references are correct
3. Ensure "why not myopic" section is present
4. Confirm "steps back" section exists
5. Validate time estimates are reasonable

---

## Examples

See `docs/EXPORT_TENSOR_INPUT_VERIFICATION.md` for a complete example following this methodology.
