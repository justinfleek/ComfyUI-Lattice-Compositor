# LATTICE COMPOSITOR - AUDIT WORKFLOW

**Version:** 5.0
**Updated:** 2025-12-26
**Phase:** Tier 3+ (Integration Testing Added)

---

## HOW THIS WORKS

You work → Checkpoint → Output reviewed → "confirmed" or feedback → Continue

The user passes messages. Another Claude reviews your output.
"Confirmed" means the review passed. Then you continue.

---

## THE AUDIT CYCLE

### 1. DISCOVERY

Identify ALL files related to the feature:
- Check FEATURE_INVENTORY.md for listed files
- Check ui/src/components for related .vue files
- Check ui/src/stores for related actions
- Check ui/src/engine for related classes
- Check ui/src/services for related services
- Check ui/src/types for related types

List every file you will read.

### 2. READ FILES

READ EVERY LINE of every file identified.

- Exact line counts required
- Large files: read in chunks, track progress
- Note observations from each file/chunk

Prohibited:
- Using grep/search to verify code
- Reading one chunk and assuming the rest
- Estimates like "~400 lines"
- Skipping files
- Referencing "previously read" files after context compaction

### 3. PHASE A: PATTERN CHECKS

Static code analysis for known bug patterns:

#### A1. FPS Defaults/Fallbacks
- **Check for:** Hardcoded fps values (24, 30, 60)
- **Correct value:** 16 (WAN standard)
- **Search:** `grep -r "|| 24\||| 30\||| 60\|fps.*=.*24\|fps.*=.*30\|fps.*=.*60" --include="*.ts" --include="*.vue"`
- **Found in:** BUG-001, BUG-002, BUG-037, BUG-038, BUG-048, BUG-052

#### A2. Direct Mutation Bypassing Store
- **Check for:** Components directly mutating `props.layer.*` without store methods
- **Correct pattern:** `store.updateLayer()`, `store.updateLayerData()`, `emit('update', {...})`
- **Search:** `grep -r "props.layer\." --include="*.vue" | grep "="`
- **Found in:** BUG-042, BUG-043, BUG-047, BUG-049, BUG-050

#### A3. Determinism
- **Check for:** `Math.random()` or `Date.now()` in render/evaluation paths
- **Acceptable:** At creation time for IDs, in user-triggered actions
- **Unacceptable:** In `onEvaluateFrame()`, render loops, animation calculations
- **Correct pattern:** Seeded RNG, frame-based calculations

#### A4. Resource Disposal
- **Check for:** THREE.js resources (geometry, material, texture) not disposed
- **Correct pattern:** `dispose()` called in `onDispose()` method

#### A5. Missing History Tracking
- **Check for:** State changes without `pushHistory()` or store methods
- **Correct pattern:** All user-initiated changes go through store

### 4. PHASE B: INTEGRATION TESTING (NEW - REQUIRED FOR TIER 3+)

This verifies features actually work across file boundaries.

#### B1. Define a Real User Scenario

For each feature, define a concrete scenario a user would actually do. Example:

> **Feature:** Text on Path (3.2)
> **Scenario:** User creates a curved path with animated control points, attaches text to follow it, scrubs timeline from frame 0 → 40 → 20.

#### B2. Trace Data Flow Across Files

Map the exact function calls and data handoffs:

```
[UserAction] → [Component] → [Store] → [Service/Engine] → [Output]
```

For each step:
- What function is called?
- What parameters are passed?
- What is returned?
- Is frame/fps passed correctly?

#### B3. Verify Handoff Points

Identify where data crosses file boundaries and verify:
- Does the caller pass the right data?
- Does the receiver use it correctly?
- Is frame context preserved?

#### B4. Test Scrubbing/Seeking

For any animated feature:
- Does frame 40 produce correct output?
- Does scrubbing backward to frame 20 produce correct output?
- Is the result deterministic (same frame always = same output)?

#### B5. Document Integration Gaps

If handoffs are broken or missing:
- File as a bug with "INTEGRATION" prefix in description
- Document what's missing
- Fix immediately per "always fix now" policy

### 5. DOCUMENT FINDINGS

Use the required format (see AUDIT REPORT FORMAT below).

### 6. CHECKPOINT

After documenting, state: "Waiting for confirmation before proceeding."

STOP. Do not continue until you receive "confirmed" or feedback.

### 7. AFTER CONFIRMATION

- Update AUDIT_PROGRESS.md (mark complete, add line count, bug count)
- Add bugs to BUGS_FOUND.md
- Git commit fixes and docs
- Begin discovery for next feature

### 8. AFTER FEEDBACK

- Address the specific issues raised
- Re-submit the audit
- Wait for confirmation again

---

## AUTOMATIC PAUSE TRIGGERS

These are reviewed. You cannot skip them.

| Trigger | Required Action |
|---------|-----------------|
| 3+ consecutive 0-bug features | Pause. State trigger. Review methodology. |
| AI/ML layer with 0 bugs | Pause. State trigger. Provide detailed justification. |
| Session has 0 bugs after 3+ features | Pause. State trigger. Something is wrong. |
| Integration test shows broken handoff | Pause. File bug. Fix immediately. |

---

## FPS ARCHITECTURE

Reference: docs/audit/FPS_ARCHITECTURE.md

**Single Source of Truth:** composition.settings.fps

**Default Values (WAN AI model standard):**
- fps: 16
- duration: 5 seconds
- frameCount: 81 (4n+1 pattern)

When auditing fps-related code:

1. Imported media with fps (video, animated assets) creates comp at that fps OR goes into subcomp with frame blending alert
2. Static assets inherit composition settings
3. New compositions default to 16fps / 81 frames
4. Export handles fps conversion for different AI models (WAN 16, Hunyuan 24, etc.)

If a function needs fps and does not have it, trace the call chain to find where fps originates (usually composition.settings.fps or store.fps) and determine why it was not passed.

---

## CONTEXT ANALYSIS METHODOLOGY

When a function is missing context (fps, duration, composition settings, layer data, etc.):

**Step 1: Trace the Call Chain Upward**

- Does the immediate caller have the context?
- If not, does THEIR caller have it?
- Keep tracing until you find where context originates

**Step 2: Classify and Act**

| Finding | Classification | Action |
|---------|----------------|--------|
| Caller has context, does not pass it | BUG | Fix the caller to pass it |
| Context exists higher in chain, never passed down | ARCHITECTURE GAP | Refactor chain to pass context through |
| Function uses wrong default value | BUG | Fix the default |
| Feature is unfinished/stubbed | STUB | Document as TODO, file bug |

**Step 3: Document Your Analysis**

| Caller | Location | Has context? | Passes it? | Classification |
|--------|----------|--------------|------------|----------------|
| [name] | file:line | YES/NO | YES/NO | BUG / ARCH GAP / STUB |

---

## AI/ML LAYER CHECKLIST

For DepthLayer, NormalLayer, PoseLayer, GeneratedLayer, ProceduralMatteLayer, and any layer that triggers AI inference:

Must verify ALL:
- [ ] Process spawn mechanism (or delegation to service)
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

0 bugs requires addressing every checkbox with evidence.

**Note from Tier 2 audit:** Most "AI" layers are actually visualization-only:
- DepthLayer, NormalLayer, PoseLayer = visualization only
- ProceduralMatteLayer = pure procedural math
- GeneratedLayer = actually triggers AI (delegates to preprocessorService)

---

## FIX POLICY

**ALWAYS FIX BUGS WHEN FOUND. No exceptions.**

If you discover a bug while auditing Feature X that belongs to Feature Y:
- Fix it NOW
- Log it under the current feature
- Note the connection in the bug description

We do not:
- "File for later"
- "Address in a future sprint"
- "Defer to the appropriate feature audit"
- Put anything off

If you find it, you fix it. Period.

---

## AUDIT REPORT FORMAT

Each feature audit must include:

```markdown
## AUDIT COMPLETE: [Feature X.X] FeatureName

### Discovery
- Files found: N
- Directories searched: list

### Files Read
| File | Lines | Method |
|------|-------|--------|
| path/to/file.ts | 456 | full read |
| path/to/big.ts | 1200 | chunked (2 reads) |
| Total | XXXX | |

### What This Code Does
Brief description of the feature's purpose.

### Phase A: Pattern Checks

#### A1. FPS Check
- [ ] No hardcoded fps (or justified)
- Lines checked: X, Y, Z
- Result: PASS/FAIL

#### A2. Store Pattern Check
- [ ] All mutations use store methods
- Lines checked: X, Y, Z
- Result: PASS/FAIL

#### A3. Determinism Check
- [ ] No Math.random()/Date.now() in render path
- Result: PASS/FAIL

#### A4. Disposal Check
- [ ] Resources properly disposed
- Result: PASS/FAIL

#### A5. History Check
- [ ] All state changes tracked
- Result: PASS/FAIL

### Phase B: Integration Testing

#### Scenario
> Describe the real user scenario being tested

#### Data Flow Trace
```
Step 1: [User Action] → [File:Function(params)] → [Output]
Step 2: [Input] → [File:Function(params)] → [Output]
Step 3: [Input] → [File:Function(params)] → [Output]
...
```

#### Handoff Verification
| From | To | Data Passed | Frame/FPS Included? | Verified |
|------|-----|-------------|---------------------|----------|
| Component.vue | storeAction | layerId, value | N/A | ✓ |
| storeAction | Service | layer, frame, fps | YES | ✓ |
| Service | Engine | result | N/A | ✓ |

#### Scrubbing Test
- Frame 0 state: [describe]
- Frame 0 → 40: [describe expected change]
- Frame 40 → 20: [describe - should show frame 20 state, not residual from 40]
- Deterministic: YES/NO

### Bugs Found
| ID | Severity | Description |
|----|----------|-------------|
| BUG-XXX | HIGH/MEDIUM/LOW | Brief description |

### Integration Gaps
List any missing connections or broken handoffs discovered during Phase B.
```

---

## FILE READING RULES

**Under ~800 lines:** Read entire file, report exact count

**Over ~800 lines:** Read in chunks, track progress, report total

**Always:**
- Exact counts (no ~ estimates)
- Note key findings from each section
- Track chunk progress for large files
- Re-read files after context compaction (no "previously read" references)

---

## QUALITY CHECKS (Applied During Review)

Your output is checked for:

1. **Discovery thoroughness** - Did you identify all related files?
2. **Line count accuracy** - Exact numbers, no estimates?
3. **Full file reads** - Did you read every line, not grep?
4. **Phase A completeness** - All 5 pattern checks performed?
5. **Phase B completeness** - Real scenario, data flow traced, handoffs verified, scrubbing tested?
6. **Bug quality** - File:line:evidence:impact:fix present?
7. **Justification quality** - If 0 bugs, is reasoning specific and credible?
8. **Statistical sanity** - Too many clean features in a row?
9. **Context analysis** - Did you trace missing context to its source?
10. **Integration verification** - Did you actually verify data flows across file boundaries?

Weak audits get sent back for rework.

---

## GIT WORKFLOW

After each bug fix:
```
git add -A && git commit -m "fix(BUG-XXX): [description]"
```

After documentation updates:
```
git add -A && git commit -m "docs: [description]"
```

After completing a tier:
```
git push origin master
```

---

## TIER 3 RE-AUDIT DIRECTIVE

**Feature 3.1 (Text Animators) must be re-audited with Phase B integration testing.**

Phase A pattern checks are complete (BUG-052 found and fixed). Now add Phase B:

1. **Scenario:** User adds typewriter animator to TextLayer with 20 characters, scrubs from frame 0 → 40 → 20. Characters should reveal progressively (more at 40, fewer at 20).

2. **Trace the data flow:**
   - TextProperties.vue: How does user add animator? What function?
   - TextAnimatorActions: What store method is called? What params?
   - TextLayer.onEvaluateFrame(): How does it get animator data? What frame/fps?
   - TextAnimator.calculateCompleteCharacterInfluence(): What params? Returns what?
   - TextLayer render: How are invisible characters handled?

3. **Verify handoffs:**
   - Does frame number flow from store → actions → service → layer?
   - Does fps flow correctly?
   - Is composition context available at each step?

4. **Scrubbing test:**
   - At frame 0: How many characters visible?
   - At frame 40: How many characters visible?
   - Scrub back to frame 20: Correct number visible? Or stuck at 40's state?

Then proceed to 3.2 with full Phase A + Phase B audit.

---

## QUESTIONS TO ASK FOR EVERY FEATURE

1. What would a user actually DO with this feature?
2. What files are involved when they do it?
3. Does data flow correctly between those files?
4. Does frame/fps context get passed at every handoff?
5. Does scrubbing produce correct results?
6. Is the output deterministic?
7. Would this survive export and render the same on re-import?
