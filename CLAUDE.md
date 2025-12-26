# CLAUDE.md - Lattice Compositor Development Guide

**Version:** 15.0 | **Last Updated:** December 25, 2025

---

## 🔄 HOW THIS AUDIT WORKS

**You (Claude Code) do the work. Your output gets reviewed by another Claude instance.**
````
You work → You pause → Output gets reviewed → You receive "confirmed" or feedback → You continue
````

The user is a dumb terminal passing messages. They don't evaluate your work.
Another Claude reviews your output and decides what to send back.

**"Confirmed" means your output passed review. It's not a human judgment.**

---

## ⛔ MANDATORY SESSION START

**Complete these steps BEFORE any audit work:**

1. Read `docs/audit/SESSION_STARTUP_CHECKLIST.md`
2. Type back all acknowledgments
3. Read this entire CLAUDE.md file
4. Read `docs/audit/AUDIT_WORKFLOW.md`
5. Read `docs/audit/AUDIT_PROGRESS.md` to find current position
6. Begin work on next incomplete feature

**If you skip these steps, the session is INVALID.**

---

## 🚨 AUTOMATIC PAUSE TRIGGERS

**These are HARD RULES. If triggered, you MUST pause and state the trigger.**

| Trigger | Action |
|---------|--------|
| 3+ consecutive features with 0 bugs | STOP. State: "PAUSE TRIGGER: 3 consecutive clean features. Reviewing methodology." |
| Any AI/ML layer with 0 bugs | STOP. State: "PAUSE TRIGGER: AI layer marked clean. Providing detailed justification." |
| Line count uses "~" or "approximately" | INVALID. You must have exact counts. |
| No bugs found in entire session (3+ features) | STOP. State: "PAUSE TRIGGER: No bugs in session. Something is wrong." |
| Grep/search used instead of full file read | INVALID. Read entire files. |

**These triggers are reviewed. Ignoring them will be caught.**

---

## 📋 THE AUDIT PROCESS

### For Every Feature:

**PHASE 1: DISCOVERY (Document, Don't Wait)**

Search ALL categories and document what you found:
````bash
# Search all relevant directories
find ui/src/components -name "*.vue" | xargs grep -l "KEYWORD"
find ui/src/stores -name "*.ts" | xargs grep -l "KEYWORD"
find ui/src/engine -name "*.ts" | xargs grep -l "KEYWORD"
find ui/src/services -name "*.ts" | xargs grep -l "KEYWORD"
find ui/src/types -name "*.ts" | xargs grep -l "KEYWORD"
````

Cross-reference with FEATURE_INVENTORY.md.

**Document your discovery in the output:**
````markdown
**Discovery:**
- Searched: [keywords]
- Directories: [list]
- Files found: [count]
````

**PHASE 2: READ ALL FILES**

- Read every line of every file
- Large files: read in chunks, track progress
- Document exact line counts (no estimates)
- Note observations from each file

**PHASE 3: TRACE USER FLOW**

Follow the complete path:
````
UI interaction → Store action → Engine update → Render → Export
````

Verify each step actually works, not just exists.

**PHASE 4: DOCUMENT FINDINGS**

Use the required format (see below).

**PHASE 5: CHECKPOINT**

After documenting findings, state:
````
Waiting for confirmation before proceeding.
````

Then STOP. Wait for response.

---

## 📄 REQUIRED OUTPUT FORMAT

**Every feature audit MUST use this exact format:**
````markdown
## AUDIT COMPLETE: [Feature X.X] [Name]

**Discovery:**
- Searched: [keywords used]
- Directories: [ui/src/components, ui/src/stores, ui/src/engine, ui/src/services, ui/src/types]
- Files found: [count]

**Files Read:**
| File | Lines | Method |
|------|-------|--------|
| [path/file.ts] | [exact] | [full read / chunked] |
| [path/file.vue] | [exact] | [full read / chunked] |
| **Total** | **[sum]** | |

**What This Code Does:**
[2-4 sentences in your own words]

**Data Flow:**
[UI] → [Store] → [Engine] → [Render] → [Export]

**User Flow Verification:**
1. [Action]: [Expected] → [Actual]: PASS/FAIL
2. [Action]: [Expected] → [Actual]: PASS/FAIL

**Bugs Found:** [count]

[For each bug:]
### BUG-XXX: [Title]
- **Severity:** [CRITICAL/HIGH/MEDIUM/LOW]
- **File:** [path]
- **Line:** [number]
- **Problem:** [description]
- **Evidence:** [code snippet]
- **Impact:** [what breaks]
- **Suggested Fix:** [code or description]

OR

**Bugs Found:** 0
**Justification:** [Detailed explanation of why no bugs exist - must be specific, not just "code looks correct"]

---

Waiting for confirmation before proceeding.
````

---

## 📄 LARGE FILE HANDLING

**Files over ~800 lines must be read in chunks:**
````
1. Read lines 1-800
2. Read lines 801-1600
3. Continue until EOF
4. Report: "[file]: [total] lines in [X] chunks"
````

**Track your progress:**
````markdown
[filename] chunk reading:
- Lines 1-800: [key observations]
- Lines 801-1600: [key observations]
- Lines 1601-2400: [key observations]
- Total: [N] lines in [X] chunks ✓
````

**PROHIBITED:**
- Reading one chunk and assuming the rest is similar
- Skipping to "interesting" sections
- Claiming file read after partial read

---

## 🔬 AI/ML LAYER REQUIREMENTS

**Architecture:** These layers spawn Python processes to run AI models. Model output becomes layer content on the timeline.
````
Source Content → Python AI Process → Model Output → Layer Content → Timeline → Export
````

| Layer | Process | Output |
|-------|---------|--------|
| DepthLayer | DepthAnything v2, MiDaS, ZoeDepth, Marigold | Depth map |
| NormalLayer | NormalCrafter, DSINE | Normal map (RGB) |
| PoseLayer | DWPose, OpenPose, MediaPipe | Keypoint JSON |
| GeneratedLayer | Stable Diffusion, Flux | RGB frames |
| ProceduralMatteLayer | SAM, GroundingDINO | Mask |

**AI layers require verification of:**

1. Process invocation (spawn, parameters, error handling)
2. Output capture (format, parsing, frame sync)
3. Data normalization (value ranges, assumptions)
4. Timeline integration (render, scrub, properties, expressions)
5. Export (ControlNet format, ComfyUI compatibility)

**AI layer audit checklist:**
- [ ] Process spawn mechanism documented
- [ ] Input handling verified
- [ ] Output parsing verified
- [ ] Value normalization traced
- [ ] Hardcoded assumptions identified
- [ ] Timeline rendering verified
- [ ] Scrubbing determinism verified
- [ ] Export format verified
- [ ] Error handling verified

**0 bugs on AI layer triggers automatic pause.**

---

## 🚫 ABSOLUTE PROHIBITIONS

| Prohibited | Required Instead |
|------------|------------------|
| grep to verify correctness | Read entire file |
| "~400 lines" estimates | Exact count: "421 lines" |
| "Similar to X" assumptions | Read this specific file |
| "Looks correct" conclusions | Trace actual execution |
| Continuing without checkpoint | Wait for confirmation |
| Skipping file categories | Search UI, Store, Engine, Services, Types |

---

## 📈 SEVERITY DEFINITIONS

| Severity | Definition |
|----------|------------|
| **CRITICAL** | Crashes, data loss, nothing renders |
| **HIGH** | Wrong values, broken animation, undo fails |
| **MEDIUM** | Edge cases broken, wrong fps, hardcoded values |
| **LOW** | Visual glitches, console warnings |

**Every issue gets logged. No "too minor" category.**

---

## 🎯 PROJECT CONTEXT

**Lattice Compositor** - Motion graphics for ComfyUI AI video generation.

| Metric | Value |
|--------|-------|
| Lines of Code | 750,000+ |
| Layer Types | 24 |
| Effects | 102 |
| Total Audit Items | 127 features |

**Architecture:**
````
UI (Vue) → Store (Pinia) → Engine (Three.js) → Render → Export
````

**Determinism Rule:** Every frame must be reproducible.
````
Frame 50 → Frame 10 → Frame 50 = IDENTICAL output
````

Forbidden: `Date.now()`, `Math.random()`, accumulated state
Required: Pure functions of frame number, seeded RNG, reset on seek

---

## 📝 TERMINOLOGY

| ❌ Avoid | ✅ Use |
|----------|--------|
| Pickwhip | PropertyLink |
| Graph Editor | CurveEditor |
| Adjustment Layer | EffectLayer |
| loopOut/loopIn | repeatAfter/repeatBefore |
| Null Object | Control |
| Precomp | NestedComp |
| Anchor Point | origin |

---

## 🔄 SESSION WORKFLOW

1. Complete startup checklist acknowledgments
2. Find next incomplete feature in AUDIT_PROGRESS.md
3. Discovery: Search all file categories, document findings
4. Read: All files completely (chunk if needed)
5. Trace: UI → Store → Engine → Render → Export
6. Document: Use required format
7. Checkpoint: "Waiting for confirmation before proceeding"
8. Wait: For response
9. After "confirmed": Update AUDIT_PROGRESS.md, proceed to next feature
10. After feedback: Address issues, re-submit

---

## 📁 FILE LOCATIONS
````
docs/audit/
├── CLAUDE.md                    # This file
├── SESSION_STARTUP_CHECKLIST.md # Acknowledgments
├── AUDIT_PROGRESS.md            # Track completion
├── BUGS_FOUND.md                # Log all bugs
├── FEATURE_INVENTORY.md         # What to audit
├── AUDIT_WORKFLOW.md            # Detailed process
└── sessions/                    # Session reports
````