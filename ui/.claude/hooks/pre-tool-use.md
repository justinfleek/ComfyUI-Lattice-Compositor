---
match: Edit|Write|MultiEdit|Update|str_replace
---

# MANDATORY PRE-EDIT CHECKLIST

STOP. Answer these questions OUT LOUD before proceeding:

## 1. FILE KNOWLEDGE
- [ ] I have read the ENTIRE target file (not grep, not head)
- [ ] I can state: "File has [N] lines, [M] exports"
- [ ] I have listed all imports and exports

## 2. CHANGE TYPE
- [ ] This changes TYPES ONLY (safe) OR
- [ ] This changes FUNCTIONALITY (requires explicit approval)

## 3. DELETION CHECK
- [ ] I am NOT deleting any properties from objects
- [ ] I am NOT removing any code paths
- [ ] I am NOT simplifying working functionality

## 4. PATTERN CHECK
- [ ] I have searched for this pattern across the ENTIRE codebase
- [ ] This is not a one-off fix that leaves similar issues elsewhere

## 5. TYPE FIX DIRECTION
- [ ] If there's a type mismatch, I am fixing the TYPE DEFINITION
- [ ] I am NOT changing code to match incorrect types

If ANY answer is NO or UNCERTAIN, STOP and clarify before proceeding.
