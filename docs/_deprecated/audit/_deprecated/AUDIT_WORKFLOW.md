# Lattice Compositor Audit Workflow

**Version:** 3.0 | **Updated:** December 25, 2025

---

## How This Works
````
You work → Checkpoint → Output reviewed → "confirmed" or feedback → Continue
````

The user passes messages. Another Claude reviews your output.
"Confirmed" means the review passed. Then you continue.

---

## The Audit Cycle

### 1. DISCOVERY

Search ALL file categories for the feature:
````bash
find ui/src/components -name "*.vue" | xargs grep -l "KEYWORD"
find ui/src/stores -name "*.ts" | xargs grep -l "KEYWORD"
find ui/src/engine -name "*.ts" | xargs grep -l "KEYWORD"
find ui/src/services -name "*.ts" | xargs grep -l "KEYWORD"
find ui/src/types -name "*.ts" | xargs grep -l "KEYWORD"
````

Check FEATURE_INVENTORY.md for listed files.

**Document what you searched and found.** This is reviewed.

### 2. READ FILES

Read every line of every relevant file.

- Exact line counts required
- Large files: read in chunks, track progress
- Note observations from each file/chunk

**Prohibited:**
- Grep instead of reading
- Reading one chunk and assuming the rest
- Estimates like "~400 lines"

### 3. TRACE USER FLOW

Follow the complete path for at least 2 user actions:
````
User clicks [X]
→ Component: [file.vue] handles event
→ Store: [action()] called
→ Engine: [method()] updates state
→ Render: [result] displayed
→ Export: [survives/breaks]
````

### 4. DOCUMENT FINDINGS

Use required format from CLAUDE.md:
````markdown
## AUDIT COMPLETE: [Feature X.X] [Name]

**Discovery:**
- Searched: [keywords]
- Directories: [list]
- Files found: [count]

**Files Read:**
| File | Lines | Method |
|------|-------|--------|
| [file] | [exact] | [full/chunked] |

**What This Code Does:**
[your words]

**Data Flow:**
[UI] → [Store] → [Engine] → [Render] → [Export]

**User Flow Verification:**
1. [action]: [expected] → [actual]: PASS/FAIL
2. [action]: [expected] → [actual]: PASS/FAIL

**Bugs Found:** [count]
[bug details with file:line:evidence:impact:fix]

OR

**Bugs Found:** 0
**Justification:** [detailed reasoning]

---

Waiting for confirmation before proceeding.
````

### 5. CHECKPOINT

After documenting, state:
````
Waiting for confirmation before proceeding.
````

**STOP. Do not continue until you receive "confirmed" or feedback.**

### 6. AFTER CONFIRMATION

- Update AUDIT_PROGRESS.md (mark complete, add line count, bug count)
- Add bugs to BUGS_FOUND.md
- Begin discovery for next feature

### 7. AFTER FEEDBACK

- Address the specific issues raised
- Re-submit the audit
- Wait for confirmation again

---

## Automatic Pause Triggers

**These are reviewed. You cannot skip them.**

| Trigger | Required Action |
|---------|-----------------|
| 3+ consecutive 0-bug features | Pause. State trigger. Review methodology. |
| AI/ML layer with 0 bugs | Pause. State trigger. Provide detailed justification. |
| Session has 0 bugs after 3+ features | Pause. State trigger. Something is wrong. |

When triggered, output:
````
PAUSE TRIGGER: [which trigger]
[explanation of what you're doing about it]
````

---

## AI/ML Layer Checklist

For DepthLayer, NormalLayer, PoseLayer, GeneratedLayer, ProceduralMatteLayer:

**Must verify ALL:**
- [ ] Process spawn mechanism
- [ ] Input handling (resolution, format, frames)
- [ ] Output capture mechanism
- [ ] Output parsing
- [ ] Value normalization
- [ ] Hardcoded assumptions
- [ ] Timeline rendering
- [ ] Scrubbing determinism
- [ ] Expression access
- [ ] Export format
- [ ] Error handling

**0 bugs requires addressing every checkbox with evidence.**

---

## File Reading Rules

**Under ~800 lines:** Read entire file, report exact count

**Over ~800 lines:** Read in chunks
````
Lines 1-800: [observations]
Lines 801-1600: [observations]
Lines 1601-2400: [observations]
Total: 2400 lines in 3 chunks
````

**Always:**
- Exact counts (no ~ estimates)
- Note key findings from each section
- Track chunk progress for large files

---

## Bug Format
````markdown
### BUG-XXX: [Short Title]

- **Severity:** CRITICAL / HIGH / MEDIUM / LOW
- **Feature:** [X.X Name]
- **File:** [exact path]
- **Line:** [number or range]
- **Problem:** [what's wrong]
- **Evidence:**
```typescript
[the problematic code]
```
- **Impact:** [what breaks for users]
- **Suggested Fix:** [how to fix]
````

---

## Quality Checks (Applied During Review)

Your output is checked for:

1. **Discovery thoroughness** - Did you search all categories?
2. **Line count accuracy** - Exact numbers, no estimates?
3. **Flow completeness** - UI through Export traced?
4. **Bug quality** - File:line:evidence:impact:fix present?
5. **Justification quality** - If 0 bugs, is reasoning specific and credible?
6. **Format compliance** - Required sections present?
7. **Statistical sanity** - Too many clean features in a row?

Weak audits get sent back for rework.
````

---

## 4. Startup Message for Claude Code
````
You are auditing the Lattice Compositor codebase.

HOW THIS WORKS:
- You do the work and pause at checkpoints
- Your output gets reviewed by another Claude instance
- The user just passes messages between us
- "Confirmed" means your output passed review
- Feedback means address the issues and resubmit

START BY:
1. Reading docs/audit/SESSION_STARTUP_CHECKLIST.md
2. Typing back ALL 5 acknowledgments
3. Reading docs/audit/CLAUDE.md completely
4. Reading docs/audit/AUDIT_WORKFLOW.md completely
5. Reading docs/audit/AUDIT_PROGRESS.md to find your position

THEN:
- Begin discovery for the next incomplete feature
- Follow the audit process in CLAUDE.md
- Use the required output format exactly
- Stop at "Waiting for confirmation before proceeding"

Your output is reviewed for:
- Discovery thoroughness (did you search all file categories?)
- Exact line counts (no estimates)
- Complete user flow traces (UI → Export)
- Bug quality (file:line:evidence:impact)
- Justification quality (if 0 bugs)

Weak audits get sent back. Quality matters more than speed.

Begin by reading the checklist and typing back the acknowledgments.