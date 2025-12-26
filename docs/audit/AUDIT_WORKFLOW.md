# Lattice Compositor Audit Workflow

**Version:** 4.0 | **Updated:** December 25, 2025

---

## How This Works

You work → Checkpoint → Output reviewed → "confirmed" or feedback → Continue

The user passes messages. Another Claude reviews your output.
"Confirmed" means the review passed. Then you continue.

---

## The Audit Cycle

### 1. DISCOVERY

Search ALL file categories for the feature. Check FEATURE_INVENTORY.md for listed files.

Document what you searched and found. This is reviewed.

### 2. READ FILES

Read every line of every relevant file.

- Exact line counts required
- Large files: read in chunks, track progress
- Note observations from each file/chunk

Prohibited:
- Grep instead of reading
- Reading one chunk and assuming the rest
- Estimates like "~400 lines"

### 3. TRACE USER FLOW

Follow the complete path for at least 2 user actions:

User clicks [X] → Component handles event → Store action called → Engine updates state → Render displays → Export survives/breaks

### 4. DOCUMENT FINDINGS

Use required format from CLAUDE.md.

### 5. CHECKPOINT

After documenting, state: "Waiting for confirmation before proceeding."

STOP. Do not continue until you receive "confirmed" or feedback.

### 6. AFTER CONFIRMATION

- Update AUDIT_PROGRESS.md (mark complete, add line count, bug count)
- Add bugs to BUGS_FOUND.md
- Git commit fixes and docs
- Begin discovery for next feature

### 7. AFTER FEEDBACK

- Address the specific issues raised
- Re-submit the audit
- Wait for confirmation again

---

## Automatic Pause Triggers

These are reviewed. You cannot skip them.

| Trigger | Required Action |
|---------|-----------------|
| 3+ consecutive 0-bug features | Pause. State trigger. Review methodology. |
| AI/ML layer with 0 bugs | Pause. State trigger. Provide detailed justification. |
| Session has 0 bugs after 3+ features | Pause. State trigger. Something is wrong. |

---

## Context Analysis Methodology

When a function is missing context it might need (fps, duration, composition settings, layer data, etc.):

Default assumption: It is a problem that needs fixing.

Step 1: Trace the Call Chain Upward

- Does the immediate caller have the context?
- If not, does THEIR caller have it?
- Keep tracing until you find where context originates

Step 2: Classify the Problem

| Finding | Classification | Action |
|---------|----------------|--------|
| Caller has context, does not pass it | BUG | Fix the caller to pass it |
| Context exists higher in chain, never passed down | ARCHITECTURE GAP | Refactor chain to pass context through |
| Function uses wrong default value | BUG | Fix the default |
| Feature is unfinished/stubbed | STUB | Document as TODO, file bug |

Step 3: Document Your Analysis

| Caller | Location | Has context? | Passes it? | Classification |
|--------|----------|--------------|------------|----------------|
| [name] | file:line | YES/NO | YES/NO | BUG / ARCH GAP / STUB |

Step 4: No Dismissals

There is no "by design" category for missing context. If code needs context and does not have it, something is wrong somewhere in the chain. Find it. Document it. Fix it or file it.

---

## AI/ML Layer Checklist

For DepthLayer, NormalLayer, PoseLayer, GeneratedLayer, ProceduralMatteLayer:

Must verify ALL:
- Process spawn mechanism
- Input handling (resolution, format, frames)
- Output capture mechanism
- Output parsing
- Value normalization
- Hardcoded assumptions
- Timeline rendering
- Scrubbing determinism
- Expression access
- Export format
- Error handling

0 bugs requires addressing every checkbox with evidence.

---

## File Reading Rules

Under ~800 lines: Read entire file, report exact count

Over ~800 lines: Read in chunks, track progress, report total

Always:
- Exact counts (no ~ estimates)
- Note key findings from each section
- Track chunk progress for large files

---

## Quality Checks (Applied During Review)

Your output is checked for:

1. Discovery thoroughness - Did you search all categories?
2. Line count accuracy - Exact numbers, no estimates?
3. Flow completeness - UI through Export traced?
4. Bug quality - File:line:evidence:impact:fix present?
5. Justification quality - If 0 bugs, is reasoning specific and credible?
6. Format compliance - Required sections present?
7. Statistical sanity - Too many clean features in a row?
8. Context analysis - Did you trace missing context to its source?

Weak audits get sent back for rework.

---

## Git Workflow

After each bug fix:
git add -A && git commit -m "fix(BUG-XXX): [description]"

After documentation updates:
git add -A && git commit -m "docs: [description]"
