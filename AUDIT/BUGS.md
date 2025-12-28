# Bug Registry - FULL RE-AUDIT v4.0

## Summary
- Total bugs: 0
- Critical: 0
- High: 0
- Medium: 0
- Low: 0
- Fixed: 0
- Unfixed: 0

## Rules
1. **NEVER reuse bug IDs** - Always increment from highest existing
2. **Every bug gets EVIDENCE file** - EVIDENCE/BUG-XXX.md
3. **Single source of truth** - FIX_TRACKER must reference these IDs exactly
4. **Append only** - Never delete entries, mark as INVALID if needed

---

## Bug Format

```markdown
## BUG-XXX: [SEVERITY] - [Short Title]
- **File:** /full/path/to/file.ts
- **Lines:** X-Y
- **Function:** functionName()
- **Type:** [CRASH/CORRUPTION/LEAK/SECURITY/INFINITE-LOOP]
- **Found:** [timestamp]
- **Fixed:** [ ] or [x] with date
- **Evidence:** See EVIDENCE/BUG-XXX.md

**Crash Path:**
Line X: `code here`
  → input=NaN: result
  → input=null: result
```

---

## Bugs

*Fresh audit starting - new bugs will be numbered BUG-176 and higher*
*Previous bugs (BUG-001 through BUG-175) documented in BUGS_ARCHIVED_20251228.md and EVIDENCE/*

---
