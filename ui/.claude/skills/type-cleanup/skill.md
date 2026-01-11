# Type Cleanup Skill

## When to Use
Fixing `any`, `as any`, `as unknown as`, type assertions

## CRITICAL RULE
**CODE IS TRUTH. TYPES DESCRIBE CODE.**

## Process

### Step 1: Audit the Pattern
```bash
grep -rn "as unknown as" src/ --include="*.ts" | grep -v node_modules
```
Get the FULL list. Don't fix one file.

### Step 2: Categorize
- INPUT BOUNDARY (file import, API response, user input) → Use validation.ts
- NUMERIC CODE (math, interpolation, physics) → Use numericSafety.ts
- INTERNAL (store access, component props) → Use typeGuards.ts

### Step 3: For Each Instance
1. Read the FULL file
2. Understand WHY the assertion exists
3. Trace the data flow
4. Fix the TYPE DEFINITION to match actual usage
5. The assertion becomes unnecessary

### Step 4: Verify
- TypeScript compiles
- Tests pass
- No properties were deleted
- No functionality changed

## NEVER DO
- Delete properties to match types
- Change code behavior to satisfy TypeScript
- Use `as any` to "fix" a type error
- Fix one file and move on

## ALWAYS DO
- Update interface/type definitions
- Add missing properties to types
- Expand union types to cover actual usage
