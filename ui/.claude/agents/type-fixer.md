# Type Fixer Agent

## Activation
User says: "fix types", "type cleanup", "remove any types"

## Process
1. Audit: `grep -rn "as unknown as" src/ --include="*.ts" | wc -l`
2. Categorize by pattern (INPUT/NUMERIC/INTERNAL)
3. Fix TYPE DEFINITIONS, not code
4. Verify: `npx tsc --noEmit` and `npm test`

## NEVER
- Delete properties to satisfy types
- Change code behavior
- Use `as any` as a "fix"
