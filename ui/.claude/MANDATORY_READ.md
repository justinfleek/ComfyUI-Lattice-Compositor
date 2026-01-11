# MANDATORY SESSION START - READ BEFORE ANY ACTION

## CRITICAL RULES (Violations = Session Failure)

### 1. CODE IS TRUTH, TYPES DESCRIBE
- NEVER delete properties, code, or functionality to satisfy TypeScript
- ALWAYS update type definitions to match working code
- If you're about to use `as any`, `as unknown as`, STOP and fix the types instead

### 2. FULL FILE READS ONLY
- No grep, head, tail, or line ranges to "understand" a file
- Read the ENTIRE file or don't touch it
- State: "Read [filename]: [N] lines, [M] exports"

### 3. PATTERN-BASED, NOT FILE-BASED
- When fixing issues, fix ALL instances of a pattern across the codebase
- Never fix one file then move on - audit the whole codebase for that pattern
- Group by: INPUT BOUNDARIES → NUMERIC CODE → INTERNAL

### 4. NO BACKWARDS COMPATIBILITY
- One name per concept
- If old code uses wrong name, fix the old code
- No "legacy aliases", no "deprecated but kept"

### 5. VERIFY BEFORE CLAIMING DONE
- Run: `npx tsc --noEmit`
- Run: `npm test`
- State evidence, not "should work"

## BEFORE ANY EDIT, ASK:

1. Have I read the ENTIRE target file? (Not grep, not head)
2. Does this change FUNCTIONALITY or just TYPES?
3. Am I DELETING any properties/code? → STOP, get approval
4. Have I checked for this pattern ACROSS the codebase?
5. Have I updated type definitions (not code) if there's a type mismatch?

## SESSION WORKFLOW

1. START: Read this file → Read CLAUDE.md → Read relevant docs/
2. WORK: Follow the rules above
3. END: Update docs → Verify tests pass → Commit with clear message

## UTILITIES AVAILABLE

- `src/utils/validation.ts` - Input boundary validation
- `src/utils/typeGuards.ts` - Runtime type narrowing
- `src/utils/numericSafety.ts` - NaN/Infinity guards

## QUICK REFERENCE

| Task | Tool | Location |
|------|------|----------|
| External input validation | ValidationResult<T> | validation.ts |
| Runtime type checks | isObject, hasXY, etc | typeGuards.ts |
| Math safety | ensureFinite, safeDivide | numericSafety.ts |
| Type issues | FIX THE TYPE DEFINITION | src/types/*.ts |
