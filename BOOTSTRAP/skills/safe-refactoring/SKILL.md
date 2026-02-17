---
name: safe-refactoring
description: Safely refactor code without breaking functionality. Use when refactoring, restructuring code, or improving code quality while maintaining behavior.
license: MIT
compatibility: opencode
---

# Safe Refactoring Skill

## Golden Rule
Working code is more valuable than clean code. Never break working code to make it "cleaner."

## Before ANY Refactor

### 1. Create a Baseline
```bash
git stash
git status  # Should be clean
npm test    # Should pass
npx tsc --noEmit  # Note current error count
```

### 2. Understand the Code
- Read ENTIRE file(s) being refactored
- List all exports and their consumers
- Document current behavior

### 3. Make Changes Incrementally
- One logical change at a time
- Verify after EACH change
- If tests fail, REVERT immediately

### 4. Verify No Functionality Lost
```bash
git diff  # Review every deleted line
```
Ask: "Does this deletion remove functionality or just cleanup?"

## Refactor Checklist
- [ ] Tests pass before starting
- [ ] Tests pass after each change
- [ ] No exports removed without updating consumers
- [ ] No properties deleted from objects
- [ ] Type definitions updated (not code forced to match types)

## Red Flags (STOP if you see these)
- "I need to delete this property to fix the type error"
- "This code doesn't match the type, so I'll change the code"
- "I'll add backwards compatibility for the old way"
- "Let me just use `as any` to make this work"
