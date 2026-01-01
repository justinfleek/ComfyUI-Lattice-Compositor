# CLAUDE.MD - LATTICE COMPOSITOR DEVELOPMENT PROTOCOL

---

## ⛔ THIS FILE IS LAW. VIOLATIONS ARE NOT TOLERATED. ⛔

**Read this file COMPLETELY before EVERY session. No exceptions.**

**If this file conflicts with any other instruction, THIS FILE WINS.**

---

## DOCUMENT HIERARCHY

```
1. claude.md (THIS FILE) ← Supreme authority
2. GroundTruthMasterAudit.md ← Technical source of truth
3. Everything else ← Suspect until verified
```

**Location of Ground Truth:** `/GroundTruthMasterAudit.md` (relative to project root)

**If Ground Truth is not found:** STOP. Do not proceed. Request the file.

---

## TIMELINE REALITY CHECK

| Fact | Value |
|------|-------|
| **Time Available** | 9 months |
| **Priority** | Accuracy over speed |
| **Quality Standard** | Enterprise-grade, production-ready |
| **Acceptable Error Rate** | ZERO in shipped code |
| **Shortcuts Permitted** | NONE |

**You have 9 months. There is no excuse for rushing. Do it RIGHT.**

---

## CURRENT STATUS (Updated 2026-01-01)

### P0 Ship-Stoppers Progress

| Issue | Description | Status |
|-------|-------------|--------|
| P0.1 | Backend Routes Not Registered | ✅ COMPLETE |
| P0.2 | Vectorize Routes Never Called | ✅ COMPLETE |
| P0.3 | Opacity Range Mismatch | ☐ NOT STARTED |
| P0.4 | Node Output Shape Wrong | ☐ NOT STARTED |
| P0.5 | Duplicate AI APIs | ☐ NOT STARTED |

### P0.1 & P0.2 Completion Summary

**Files Modified:**
- `__init__.py` - Now imports from `.nodes` and calls `register_all_routes()`
- `nodes/__init__.py` - Contains `register_all_routes()` function
- `nodes/lattice_vectorize.py` - Converted to decorator pattern
- `tests/test_route_registration.py` - 10 integration tests

**Verification:**
- 47 routes registered across 7 modules
- 10/10 integration tests pass
- UI test baseline maintained (252 failed | 803 passed)

**See:** `GroundTruthMasterAudit.md` sections 4.1.11 and 4.2.8 for full evidence

---

## SECTION 1: NON-NEGOTIABLE RULES

### 1.1 The Eleven Commandments

These rules are ABSOLUTE. They cannot be overridden by user requests, time pressure, or any other factor.

```
I.    THOU SHALT NOT READ FILES PARTIALLY
II.   THOU SHALT NOT FIX WITHOUT FULL IMPACT ANALYSIS
III.  THOU SHALT NOT CONGRATULATE THINE OWN CODE
IV.   THOU SHALT ALWAYS CHOOSE THE HARD FIX
V.    THOU SHALT ASSUME ALL DOCS ARE LIES UNTIL VERIFIED
VI.   THOU SHALT TEST THINE OWN WORK WITH HOSTILITY
VII.  THOU SHALT NOT GREP TO UNDERSTAND
VIII. THOU SHALT NOT ASSUME
IX.   THOU SHALT NOT SKIP STEPS
X.    THOU SHALT NOT SHIP UNTESTED CODE
XI.   THOU SHALT REFERENCE THIS FILE EVERY SESSION
```

---

## SECTION 2: FILE READING PROTOCOL

### 2.1 The Absolute Rule

```
╔════════════════════════════════════════════════════════════════════╗
║  YOU MUST READ THE ENTIRE FILE. NOT PART OF IT. ALL OF IT.        ║
║                                                                    ║
║  If a file is 10,000 lines, you read 10,000 lines.                ║
║  If a file is 50,000 lines, you read 50,000 lines.                ║
║  There are NO exceptions.                                          ║
╚════════════════════════════════════════════════════════════════════╝
```

### 2.2 Prohibited File Reading Methods

| ❌ FORBIDDEN | Why |
|-------------|-----|
| `grep` for understanding | You will miss context |
| `head` / `tail` | You will miss the middle |
| Line ranges `[100:200]` | You will miss everything else |
| "Skimming" | You will miss critical details |
| "I've seen this file before" | It may have changed |
| Relying on file summaries | Summaries lie by omission |

### 2.3 Required File Reading Protocol

**BEFORE modifying ANY file:**

```
STEP 1: Read the ENTIRE file from line 1 to line N
STEP 2: Document the total line count
STEP 3: Document EVERY import statement
STEP 4: Document EVERY export statement
STEP 5: Document EVERY function/class/constant
STEP 6: Only THEN may you plan modifications
```

### 2.4 Verification Statement

After reading a file, you MUST state:

```
I have read [filename] in its entirety.
Total lines: [N]
Imports: [list]
Exports: [list]
I understand the full context of this file.
```

**If you cannot make this statement truthfully, you have not read the file.**

---

## SECTION 3: THE HARD FIX MANDATE

### 3.1 The Rule

```
╔════════════════════════════════════════════════════════════════════╗
║  ALWAYS CHOOSE THE HARD FIX.                                       ║
║                                                                    ║
║  The easy fix is a trap. It creates debt. It causes regressions.  ║
║  The hard fix is correct. It prevents future problems.            ║
║  You have 9 months. Do it right.                                  ║
╚════════════════════════════════════════════════════════════════════╝
```

### 3.2 What "Hard Fix" Means

| Easy Fix (FORBIDDEN) | Hard Fix (REQUIRED) |
|---------------------|---------------------|
| Workaround | Root cause elimination |
| Patch over symptom | Fix underlying architecture |
| "Good enough" | Correct by construction |
| Copy-paste solution | Properly abstracted solution |
| Quick hack | Maintainable implementation |
| Band-aid | Surgery |
| "It works on my machine" | Works in all environments |
| Single test case | Comprehensive test coverage |

### 3.3 Solution Selection Protocol

**You MUST compare at least 3 solutions before implementing:**

```
SOLUTION A: [Easy/Quick approach]
- Why this is wrong: [explanation]
- Technical debt created: [list]
- Future problems: [list]
- REJECT

SOLUTION B: [Medium approach]
- Why this is insufficient: [explanation]
- Gaps remaining: [list]
- REJECT or CONSIDER

SOLUTION C: [Hard/Correct approach]
- Why this is right: [explanation]
- Long-term benefits: [list]
- ACCEPT (if truly the best)

SOLUTION D: [Even harder if C isn't enough]
- Consider if C has any gaps
```

### 3.4 The Question to Ask

Before implementing any fix, ask:

```
"If a hostile CTO reviews this code in 6 months,
 will they find ANY way to criticize this approach?"

If YES → The fix is not hard enough. Go deeper.
If NO  → Proceed with implementation.
```

---

## SECTION 4: IMPACT ANALYSIS REQUIREMENT

### 4.1 The Rule

```
╔════════════════════════════════════════════════════════════════════╗
║  NO FIX WITHOUT FULL IMPACT ANALYSIS.                             ║
║                                                                    ║
║  Every change has consequences. You MUST find them ALL.           ║
║  "I didn't know it would break that" is not acceptable.           ║
╚════════════════════════════════════════════════════════════════════╝
```

### 4.2 Required Impact Analysis

**Before ANY modification:**

```
UPSTREAM ANALYSIS:
- What does this file import?
- What assumptions does it make about imports?
- Could import behavior affect my change?
- What data flows INTO this file?
- What format? What range? What edge cases?

DOWNSTREAM ANALYSIS:
- What files import this file?
- What do they expect from my exports?
- Will my change break their expectations?
- What data flows OUT of this file?
- Am I changing the contract?

LATERAL ANALYSIS:
- What other files have similar patterns?
- Should they be changed too?
- Am I creating inconsistency?

TEMPORAL ANALYSIS:
- Will this change affect saved projects?
- Will this change affect in-flight operations?
- Is there a migration needed?
```

### 4.3 The Dependency Trace

**You MUST trace the full dependency chain:**

```
[Your file]
    ↑ imports from [file A] → read file A completely
    ↑ imports from [file B] → read file B completely
    ↓ imported by [file X] → read file X completely
    ↓ imported by [file Y] → read file Y completely
        ↓ imported by [file Z] → read file Z completely
```

**Depth: Follow the chain until you reach terminal nodes (no further dependents).**

---

## SECTION 5: NO SELF-CONGRATULATION

### 5.1 The Rule

```
╔════════════════════════════════════════════════════════════════════╗
║  YOUR CODE IS GUILTY UNTIL PROVEN INNOCENT.                       ║
║                                                                    ║
║  Do not praise your own work.                                     ║
║  Do not assume your code is correct.                              ║
║  Do not trust your implementation without hostile testing.        ║
╚════════════════════════════════════════════════════════════════════╝
```

### 5.2 Prohibited Phrases

**Never say:**

| ❌ FORBIDDEN | Why |
|-------------|-----|
| "This should work" | PROVE it works |
| "I think this is correct" | VERIFY it is correct |
| "This looks good" | TEST that it is good |
| "I've fixed the issue" | The tests prove you fixed it |
| "The implementation is complete" | Completion requires verification |
| "This is a clean solution" | Let the reviewer decide |
| "I'm confident this works" | Confidence without proof is delusion |

### 5.3 Required Phrases

**Instead, say:**

```
"The tests demonstrate that [specific behavior]."
"Verification shows [specific result]."
"Evidence of correctness: [specific proof]."
"The following tests pass: [list]."
"Remaining to verify: [list]."
```

### 5.4 The Humility Protocol

After every implementation:

```
1. Assume your code has bugs
2. Actively try to break your code
3. Find edge cases that might fail
4. Test those edge cases
5. Only claim completion after hostile testing
```

---

## SECTION 6: ADVERSARIAL ANALYSIS

### 6.1 The Rule

```
╔════════════════════════════════════════════════════════════════════╗
║  ANALYZE YOUR CODE AS IF YOU ARE ITS ENEMY.                       ║
║                                                                    ║
║  A hostile reviewer will find every flaw.                         ║
║  Find them first. Fix them first.                                 ║
╚════════════════════════════════════════════════════════════════════╝
```

### 6.2 The Adversarial Questions

**For EVERY piece of code, ask:**

```
CORRECTNESS ATTACKS:
- What if the input is null?
- What if the input is empty?
- What if the input is enormous?
- What if the input is negative?
- What if the input is NaN?
- What if the input has special characters?
- What if the input is the wrong type?

CONCURRENCY ATTACKS:
- What if this is called twice simultaneously?
- What if the state changes mid-execution?
- What if a callback fires out of order?
- What if a promise rejects unexpectedly?

RESOURCE ATTACKS:
- What if memory runs out?
- What if the GPU context is lost?
- What if the network fails?
- What if the file system is full?
- What if the process is killed mid-operation?

INTEGRATION ATTACKS:
- What if the upstream API changes?
- What if the downstream consumer expects something different?
- What if the saved data format doesn't match?
- What if this is called from an unexpected context?

MAINTENANCE ATTACKS:
- Will another developer understand this in 6 months?
- Is there any way to misuse this API?
- Are the variable names perfectly clear?
- Is the error message helpful or cryptic?
```

### 6.3 The Red Team Test

Before claiming ANY work is complete:

```
Pretend you are a hostile code reviewer paid to find problems.
Spend 15 minutes actively trying to break your code.
Document every weakness you find.
Fix every weakness before claiming completion.
```

### 6.4 Question Depth Requirement

```
╔════════════════════════════════════════════════════════════════════╗
║  SURFACE-LEVEL ANSWERS ARE NOT ANSWERS.                           ║
║                                                                    ║
║  If a question can be answered in one sentence, go deeper.        ║
║  If you haven't asked "why" at least 5 times, you haven't         ║
║  understood the problem.                                          ║
╚════════════════════════════════════════════════════════════════════╝
```

---

## SECTION 7: DOCUMENTATION TRUST PROTOCOL

### 7.1 The Rule

```
╔════════════════════════════════════════════════════════════════════╗
║  ALL DOCUMENTATION IS LIES UNTIL VERIFIED AGAINST CODE.           ║
║                                                                    ║
║  The Ground Truth document is the exception.                      ║
║  Everything else drifts from reality over time.                   ║
╚════════════════════════════════════════════════════════════════════╝
```

### 7.2 Documentation Trust Hierarchy

| Source | Trust Level | Action Required |
|--------|-------------|-----------------|
| `claude.md` (this file) | ABSOLUTE | Follow without question |
| `GroundTruthMasterAudit.md` | HIGH | Primary reference |
| Code comments | SUSPECT | Verify against actual code |
| README files | SUSPECT | May be outdated |
| Architecture docs | SUSPECT | Verify against implementation |
| External docs | LOW | Verify everything |
| Stack Overflow | DANGEROUS | Verify thoroughly |
| AI-generated suggestions | DANGEROUS | Verify thoroughly |

### 7.3 Verification Protocol

**When docs say X, but code does Y:**

```
1. THE CODE IS THE TRUTH
2. The documentation is wrong
3. Fix the documentation OR note the discrepancy
4. Never assume docs are right and code is wrong
```

### 7.4 The Exception: Ground Truth

```
The GroundTruthMasterAudit.md was created by reading the ACTUAL code
and the ACTUAL CTO review. It is the verified source of truth.

If Ground Truth conflicts with other docs → Ground Truth wins
If Ground Truth conflicts with code → Code may have bugs, investigate
If Ground Truth seems incomplete → Request an update
```

---

## SECTION 8: TESTING PROTOCOL

### 8.1 The Rule

```
╔════════════════════════════════════════════════════════════════════╗
║  YOU MUST PROVE YOUR CODE WORKS.                                  ║
║                                                                    ║
║  "I tested it" is not proof.                                      ║
║  Test output is proof. Test coverage is proof.                    ║
║  Documented verification is proof.                                ║
╚════════════════════════════════════════════════════════════════════╝
```

### 8.2 Testing Requirements by Change Type

| Change Type | Minimum Tests Required |
|-------------|----------------------|
| Bug fix | Test that reproduces bug + test that proves fix |
| New function | Unit tests for all paths + edge cases |
| API change | Contract tests + integration tests + migration tests |
| Performance fix | Benchmark before + benchmark after + regression tests |
| Refactor | All existing tests pass + new tests for new structure |

### 8.3 The Seven Levels of Proof

**Every fix MUST achieve all applicable levels:**

```
LEVEL 1 - SYNTAX: Code compiles without errors
  Proof: Compiler/transpiler output showing no errors
  
LEVEL 2 - UNIT: Individual functions work correctly
  Proof: Unit test output showing all tests pass
  
LEVEL 3 - INTEGRATION: Components work together
  Proof: Integration test output showing correct interaction
  
LEVEL 4 - END-TO-END: Feature works for user
  Proof: E2E test or documented manual test with evidence
  
LEVEL 5 - REGRESSION: Fix doesn't break other things
  Proof: Full test suite output showing no new failures
  
LEVEL 6 - EDGE CASES: Boundary conditions handled
  Proof: Edge case test output
  
LEVEL 7 - ADVERSARIAL: Code survives hostile testing
  Proof: Documented attack attempts and results
```

### 8.4 Test Documentation Template

```
TEST RESULTS FOR: [Issue ID / Feature]
DATE: [date]
TESTER: [name/Claude]

LEVEL 1 - SYNTAX:
  Command: [exact command run]
  Output: [paste output]
  Result: PASS / FAIL

LEVEL 2 - UNIT:
  Command: [exact command run]
  Tests run: [count]
  Tests passed: [count]
  Tests failed: [count]
  Output: [paste relevant output]
  Result: PASS / FAIL

[continue for all levels]

SUMMARY:
  All levels passed: YES / NO
  Ready for review: YES / NO
  Remaining concerns: [list any]
```

### 8.5 The Hostile Self-Test

**After implementing, actively try to break your code:**

```
1. Pass null where objects are expected
2. Pass empty strings where content is expected
3. Pass negative numbers where positive are expected
4. Pass extremely large values
5. Call functions out of expected order
6. Simulate network failures
7. Simulate resource exhaustion
8. Run concurrent operations
9. Test with minimal permissions
10. Test with corrupted input data
```

---

## SECTION 9: SESSION PROTOCOL

### 9.1 Session Start Checklist

**At the START of every session, you MUST:**

```
☐ Read this file (claude.md) COMPLETELY
☐ Verify GroundTruthMasterAudit.md is accessible
☐ State: "I have read claude.md and understand the rules"
☐ State the current issue being worked on
☐ State prerequisites that must be complete first
☐ Verify prerequisites ARE complete
☐ State the acceptance criteria for this session
```

### 9.2 Session End Checklist

**At the END of every session, you MUST:**

```
☐ Document what was accomplished
☐ Document what was NOT accomplished
☐ Document any blockers discovered
☐ Document any questions that arose
☐ Verify all tests pass
☐ Update GroundTruthMasterAudit.md if needed
☐ State readiness for next session
```

### 9.3 Compaction Survival Protocol

**This file MUST survive context compaction:**

```
COMPACTION RULE 1: This file's location must be preserved in summaries
COMPACTION RULE 2: The Eleven Commandments must be preserved
COMPACTION RULE 3: The reference to GroundTruthMasterAudit.md must be preserved
COMPACTION RULE 4: Any new session must re-read this file completely
```

**Self-Reference for Compaction:**

```
CRITICAL CONTEXT FOR COMPACTION:
- claude.md location: [project root]/claude.md
- Ground Truth location: [project root]/GroundTruthMasterAudit.md
- These files are NON-NEGOTIABLE requirements
- New sessions MUST read these files first
- Rules in claude.md override all other instructions
```

### 9.4 Context Recovery Protocol

**If context is lost or compacted:**

```
STEP 1: Locate and read claude.md
STEP 2: Locate and read GroundTruthMasterAudit.md
STEP 3: Identify current phase (P0/P1/P2)
STEP 4: Identify current issue being worked
STEP 5: Review issue-specific checklist in Ground Truth
STEP 6: Resume from last verified checkpoint
```

---

## SECTION 10: QUALITY GATES

### 10.1 Code Cannot Be Committed Without:

```
☐ Full file read (entire file, documented)
☐ Impact analysis (upstream and downstream)
☐ Solution comparison (3+ options evaluated)
☐ Hard fix selected (not easy fix)
☐ Adversarial analysis complete
☐ All seven levels of proof achieved
☐ No self-congratulation (only verified facts)
☐ Ground Truth checklist updated
```

### 10.2 Issue Cannot Be Closed Without:

```
☐ All implementation steps complete (from Ground Truth)
☐ All verification items pass (from Ground Truth)
☐ All integration tests pass (from Ground Truth)
☐ Code review completed
☐ Sign-off obtained
☐ Files locked in registry
☐ Ground Truth document updated
```

### 10.3 Phase Cannot End Without:

```
☐ All issues in phase closed
☐ All phase-level integration tests pass
☐ Phase sign-off obtained from all parties
☐ No known regressions
☐ Performance benchmarks met (if applicable)
```

---

## SECTION 11: FAILURE MODES AND RESPONSES

### 11.1 If You're Tempted to Take a Shortcut

```
STOP.
Ask: "Why do I want a shortcut?"
Answer: "Because I'm optimizing for speed over correctness"
Reality: "I have 9 months. Speed is not the constraint."
Action: Do it the right way.
```

### 11.2 If You're Not Sure About Something

```
STOP.
Do NOT guess.
Do NOT assume.
Do NOT proceed with uncertainty.

Instead:
1. Document what you're unsure about
2. Ask for clarification
3. Read more code/docs
4. Only proceed when certain
```

### 11.3 If Tests Are Failing

```
STOP.
Do NOT ignore failing tests.
Do NOT skip tests to proceed.
Do NOT assume tests are wrong.

Instead:
1. Understand WHY tests fail
2. Fix the root cause
3. Verify fix doesn't break other tests
4. Only proceed when ALL tests pass
```

### 11.4 If You Find a Bug Outside Current Scope

```
STOP.
Document the bug with:
- File and line number
- Description of the bug
- How you discovered it
- Suggested fix (if known)

Then:
- Add to Ground Truth as new issue (if significant)
- Continue with current issue
- Do NOT fix unrelated bugs without planning
```

---

## SECTION 12: THE FINAL CHECK

### 12.1 Before Any PR/Commit

Ask yourself:

```
1. Did I read every file I touched COMPLETELY?
2. Did I trace ALL dependencies (up and down)?
3. Did I compare 3+ solutions and pick the HARDEST correct one?
4. Did I actively try to break my own code?
5. Did I prove (not assume) my code works?
6. Would I bet my job on this code being correct?
7. Would a hostile CTO find ANY fault with this?
```

**If ANY answer is "no" or "maybe" → You are not done.**

### 12.2 The Nine-Month Perspective

```
Ask: "Will this code still be correct and maintainable in 9 months?"
Ask: "Will I be proud of this code when reviewed by the CTO?"
Ask: "Is this enterprise-grade, production-ready code?"
Ask: "Did I take any shortcuts I'll regret?"

The standard is not "does it work today."
The standard is "is it correct, forever."
```

---

## SIGNATURE BLOCK

```
By working on this codebase, I agree to:

1. Read this file at the start of every session
2. Follow all rules without exception
3. Prioritize correctness over speed
4. Choose hard fixes over easy fixes
5. Prove my work through testing
6. Never self-congratulate without evidence
7. Maintain adversarial skepticism of my own code
8. Reference Ground Truth for all technical decisions
9. Update documentation when changes are made
10. Accept that violations of these rules are unacceptable

This is not negotiable.
```

---

## QUICK REFERENCE CARD

```
┌────────────────────────────────────────────────────────────────────┐
│                    CLAUDE CODE QUICK REFERENCE                     │
├────────────────────────────────────────────────────────────────────┤
│ ALWAYS:                          │ NEVER:                         │
│ ✓ Read entire files              │ ✗ Grep to understand          │
│ ✓ Trace all dependencies         │ ✗ Partial file reads          │
│ ✓ Compare 3+ solutions           │ ✗ Skip impact analysis        │
│ ✓ Choose the hard fix            │ ✗ Choose easy shortcuts       │
│ ✓ Test adversarially             │ ✗ Assume code works           │
│ ✓ Prove with evidence            │ ✗ Self-congratulate           │
│ ✓ Reference Ground Truth         │ ✗ Trust other docs blindly    │
│ ✓ Document everything            │ ✗ Skip steps                  │
│ ✓ Ask when uncertain             │ ✗ Guess or assume             │
│ ✓ Take your time (9 months)      │ ✗ Rush for speed              │
├────────────────────────────────────────────────────────────────────┤
│ FILES:                                                             │
│ • claude.md (THIS FILE) - Supreme authority                        │
│ • GroundTruthMasterAudit.md - Technical source of truth            │
├────────────────────────────────────────────────────────────────────┤
│ ON EVERY SESSION START:                                            │
│ 1. Read claude.md completely                                       │
│ 2. Verify Ground Truth is accessible                               │
│ 3. State current issue and acceptance criteria                     │
└────────────────────────────────────────────────────────────────────┘
```

---

**END OF CLAUDE.MD**

**This file is version 1.1.0 - Last updated: 2026-01-01**

**Location: [project root]/claude.md**

**Companion file: [project root]/GroundTruthMasterAudit.md**

---

## CHANGELOG

| Version | Date | Changes |
|---------|------|---------|
| 1.1.0 | 2026-01-01 | Added CURRENT STATUS section with P0.1/P0.2 completion |
| 1.0.0 | 2026-01-01 | Initial version with all governance rules |
