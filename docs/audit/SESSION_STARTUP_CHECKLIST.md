# SESSION STARTUP CHECKLIST

**Complete this at the start of EVERY session.**

---

## How This Works

Your output gets reviewed by another Claude instance.
The user just passes messages - they don't evaluate your work.
"Confirmed" means your output passed review.

---

## Acknowledgments

Type each acknowledgment back before starting work.

### 1. Core Rules
**Type:** "I acknowledge the core rules"

- I will READ entire files, not use grep/search patterns
- I will use EXACT line counts, never estimates
- I will document my discovery process (what I searched)
- I will trace complete USER FLOWS, not just check code exists
- I will use the required output format

### 2. Prohibited Actions  
**Type:** "I acknowledge the prohibited actions"

- I will NOT use grep to verify correctness
- I will NOT estimate line counts
- I will NOT assume similar code means similar behavior
- I will NOT skip AI/ML layer deep analysis
- I will NOT continue past checkpoints without receiving "confirmed"

### 3. Pause Triggers
**Type:** "I acknowledge the pause triggers"

I MUST pause and state the trigger if:
- 3+ consecutive features have 0 bugs
- Any AI/ML layer has 0 bugs
- No bugs found in entire session (3+ features)
- I'm tempted to estimate instead of count exactly

### 4. Output Format
**Type:** "I acknowledge the output format"

Every feature audit includes:
- Discovery documentation (what I searched)
- File list with exact line counts
- Code summary in my own words
- Data flow trace (UI → Store → Engine → Render → Export)
- User flow verification (minimum 2 checks)
- Bugs with file:line:evidence OR detailed justification for 0 bugs
- "Waiting for confirmation before proceeding"

### 5. Session Start
**Type:** "Session start: [DATE]"

Then state:
- Previous position (from AUDIT_PROGRESS.md)
- Starting feature
- Beginning discovery for that feature

---

## After All Acknowledgments

Begin work on the first/next incomplete feature.