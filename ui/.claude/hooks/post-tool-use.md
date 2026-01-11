---
match: Edit|Write|MultiEdit|Update|str_replace
---

# MANDATORY POST-EDIT VERIFICATION

After this edit, immediately:

## 1. TypeScript Check
```bash
npx tsc --noEmit 2>&1 | head -50
```
If errors introduced, FIX or REVERT immediately.

## 2. Deletion Audit
Review the diff:
- Were any properties removed? → REVERT unless explicitly approved
- Were any code paths removed? → REVERT unless explicitly approved
- Were any exports removed? → REVERT unless explicitly approved

## 3. Pattern Completion
- Did I fix ALL instances of this pattern?
- If no, continue fixing before claiming done

## 4. Test Verification (for significant changes)
```bash
npm test -- --reporter=dot 2>&1 | tail -20
```

## 5. Documentation Update
If this was a significant change, update:
- CLAUDE.md (if workflow changed)
- Relevant docs/ file (if architecture changed)
