# NEXT SESSION PROMPT TEMPLATE

Copy and customize this for handoff:

---

# FRESH SESSION START - [DATE]

## CONTEXT
Previous session ended at [checkpoint/compaction limit]. Start by verifying state.

## FIRST ACTIONS
1. Read ui/.claude/MANDATORY_READ.md
2. Read CLAUDE.md
3. Read ui/.claude/CURRENT_FOCUS.md
4. Run: `npx tsc --noEmit 2>&1 | wc -l` (check TS errors)
5. Run: `npm test -- --reporter=dot 2>&1 | tail -3` (verify tests)

## CORE RULE (CRITICAL)
CODE IS TRUTH. TYPES DESCRIBE CODE.
Never delete properties/code to satisfy TypeScript.
Always update TYPE DEFINITIONS to match working code.

## LAST COMMIT
[commit hash] - [commit message]

## CURRENT TASK
[describe what was being worked on]

## NEXT STEPS
1. [step 1]
2. [step 2]
3. [step 3]

---
