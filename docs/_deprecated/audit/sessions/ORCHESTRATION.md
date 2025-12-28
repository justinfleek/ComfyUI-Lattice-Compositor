# LATTICE COMPOSITOR - AUTONOMOUS AUDIT ORCHESTRATION

---

## STARTING A NEW SESSION

When you begin, execute these steps IN ORDER:

### Step 1: Read Current State
````bash
cat docs/audit/AUDIT_PROGRESS.md
````
Find the FIRST item with `[ ]` (not complete).

### Step 2: Read Protocol
````bash
cat docs/audit/MASTER_AUDIT_PROTOCOL.md
````
Refresh on the methodology.

### Step 3: Check Dependencies
````bash
cat docs/audit/DEPENDENCY_GRAPH.md
````
Verify upstream dependencies are audited first.

### Step 4: Begin Audit
Start with the feature identified in Step 1.
Follow the MASTER_AUDIT_PROTOCOL exactly.

---

## DURING THE SESSION

### For Each Feature:

1. **Discovery Phase**
   - Find all files touching this feature
   - List them explicitly

2. **Audit Phases (UI → Store → Engine → Render → Export)**
   - Follow protocol for each phase
   - Document findings in real-time
   - If bug found: immediately add to BUGS_FOUND.md

3. **Completion**
   - Update AUDIT_PROGRESS.md: change `[ ]` to `[x]`
   - Fill in Bugs, Time, Session columns
   - Move to next feature

### Context Management

If context limit approaches (>80% used):
1. Complete current feature if possible
2. Save progress to AUDIT_PROGRESS.md
3. Create session summary
4. Stop gracefully

---

## ENDING A SESSION

### Step 1: Update Progress
Edit `docs/audit/AUDIT_PROGRESS.md`:
- Mark completed items `[x]`
- Update bug counts
- Update session log

### Step 2: Save Session Report
Create file: `docs/audit/sessions/SESSION_[YYYY-MM-DD]_[HH-MM].md`
Use SESSION_TEMPLATE.md format.

### Step 3: Update Bugs
Ensure all bugs found are in `docs/audit/BUGS_FOUND.md`
Update summary counts.

### Step 4: Note Next Steps
In session report, clearly state what to do next session.

---

## AUDIT COMMANDS

### Start Audit
````
Begin Lattice Compositor audit. Read docs/audit/ORCHESTRATION.md and start from where we left off.
````

### Continue Audit
````
Continue Lattice Compositor audit. Check AUDIT_PROGRESS.md for current state.
````

### Audit Specific Feature
````
Audit feature [ID] from FEATURE_INVENTORY.md. Follow MASTER_AUDIT_PROTOCOL.
````

### Generate Report
````
Generate final audit report. Read all session files and BUGS_FOUND.md. Output FINAL_REPORT.md.
````

---

## DECISION RULES

### When to Stop Current Feature
- Bug found that blocks further testing → Log bug, continue to next feature
- Missing dependency not audited → Skip, note in progress
- File not found → Log as CRITICAL bug, continue

### When to Skip a Feature
- Dependency (per DEPENDENCY_GRAPH.md) not yet audited
- Feature marked as deprecated/orphaned
- External service unavailable (AI features)

### When to Escalate
- More than 10 CRITICAL bugs in one tier → Note pattern
- Entire subsystem appears broken → Document scope
- Conflicting behavior discovered → Document both paths

---

## FILE LOCATIONS
````
docs/audit/
├── MASTER_AUDIT_PROTOCOL.md    # How to audit
├── FEATURE_INVENTORY.md         # What to audit
├── DEPENDENCY_GRAPH.md          # Audit order
├── AUDIT_PROGRESS.md            # Current state (UPDATE THIS)
├── BUGS_FOUND.md                # Bug log (APPEND TO THIS)
├── ORCHESTRATION.md             # This file
├── SESSION_TEMPLATE.md          # Template for sessions
├── FINAL_REPORT_TEMPLATE.md     # Template for final report
└── sessions/                    # Session reports
    ├── SESSION_2024-XX-XX_XX-XX.md
    └── ...
````

---

## QUALITY CHECKS

Before marking a feature complete, verify:

- [ ] All files discovered were actually read
- [ ] All 5 questions answered (Exists? Wired? Computes? Renders? Exports?)
- [ ] All phases completed (UI/Store/Engine/Render/Export)
- [ ] Cross-cutting concerns checked
- [ ] Any bugs logged with full details
- [ ] Progress tracker updated

---

## ERROR RECOVERY

### If session crashes mid-feature:
1. Check last saved AUDIT_PROGRESS.md
2. Feature may be partially complete
3. Re-run discovery for that feature
4. Continue from last documented phase

### If progress file corrupted:
1. Check session reports in sessions/
2. Reconstruct progress from session logs
3. Conservative approach: re-audit uncertain items

### If bug file lost:
1. Check session reports for bug references
2. Re-audit recently completed features
3. Bugs will be re-discovered