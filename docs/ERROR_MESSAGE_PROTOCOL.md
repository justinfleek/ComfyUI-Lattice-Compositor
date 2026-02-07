# Error Message Protocol

## Core Principle

```
ALL ERRORS MUST BE EXPLICIT
NO SILENT FAILURES
NO CRYPTIC MESSAGES
```

Every error message must include:
1. **What went wrong** - Clear description of the failure
2. **Where it happened** - Location/context where the error occurred
3. **How to fix it** - Explicit instructions with "Fix:" directive

## Format

### Lean 4

```lean
throwError "FunctionName: Description of what failed at '{location}'. Fix: Clear instructions on how to resolve"
```

**Examples:**
```lean
throwError "isLevelFVar: Variable '{n}' not found in local context. This universe parameter is referenced but not declared. Fix: Add '{n} : Level' to your local context or check for typos in the variable name."

throwError "isRedundantLocalInst: Failed to synthesize instance for type '{ldecl.type}' (variable '{inst}', name: '{ldecl.userName}'). This instance cannot be synthesized from the context. Fix: Add the required instance to your context, or ensure all dependencies are available."
```

### TypeScript

```typescript
throw new Error(`[Context] Action failed: Reason. Fix: Solution`)
```

**Examples:**
```typescript
throw new Error(`[SecureActionExecutor] Tool '${name}' not available. Tool is blocked by security scope restrictions. Fix: Add tool to allowed scope or request approval.`)

throw new Error(`[SpriteValidation] Invalid format "${ext}". Supported: ${SUPPORTED_FORMATS.join(", ")}. Fix: Use one of the supported formats.`)
```

### Haskell

```haskell
error "[Module] Function failed: Reason. Fix: Solution"
```

**Examples:**
```haskell
error "[ProjectValidation] Invalid project structure: Missing required field '{field}'. Fix: Add required field '{field}' to project structure."

error "[WorkflowTemplates] Template validation failed: Invalid node type '{nodeType}'. Fix: Use valid node type from supported list."
```

## CI/CD Enforcement

The CI/CD pipeline automatically checks all error messages:

```bash
bash scripts/check-error-messages.sh
```

**What it checks:**
- ✅ All `throwError` (Lean) include "Fix:" or "fix:"
- ✅ All `throw new Error` (TypeScript) include "Fix:" or "fix:"
- ✅ All `error` (Haskell) include "Fix:" or "fix:"
- ⚠️ Warns on error messages < 50 characters (likely missing context)

**CI Failure:**
If any error message doesn't follow the format, CI will fail with:
```
❌ BANNED PATTERN DETECTED: Error messages without explicit format
PROTOCOL VIOLATION: All error messages must include:
  1. What went wrong (clear description)
  2. Where it happened (location/context)
  3. How to fix it (must include 'Fix:' or 'fix:' directive)
```

## Banned Patterns

**❌ BANNED:**
```lean
throwError "Variable not found"  -- Missing context and fix
throwError "Error"  -- Too vague
throwError "Failed"  -- No information
```

**✅ REQUIRED:**
```lean
throwError "isLevelFVar: Variable '{n}' not found in local context. This universe parameter is referenced but not declared. Fix: Add '{n} : Level' to your local context or check for typos in the variable name."
```

## Exception Handling

When catching errors, preserve the original error message:

```lean
catch e =>
  let errMsg := e.toMessageData
  throwError m!"unbound level param {newLevelName}. Original error:\n{errMsg}"
```

This ensures users see both:
- The new context-specific error
- The original underlying error

## Benefits

1. **Faster debugging** - Users immediately know what's wrong and how to fix it
2. **Better UX** - No cryptic error messages requiring deep knowledge
3. **Consistency** - All errors follow the same format
4. **Automated enforcement** - CI catches violations before merge

## Examples from Codebase

### Good Examples

**Lean:**
```lean
throwError "removeDollar: Name '{n}' does not start with '$' and cannot have dollar removed. Expected name starting with '$' for unquoted variable. Fix: Ensure variable names in quoted expressions use '$' prefix."
```

**TypeScript:**
```typescript
throw new Error(`[ActionExecutor] Layer "${layerId}" not found. Cannot remove expression from non-existent layer. Fix: Check the layer ID and ensure the layer exists before removing expressions.`)
```

**Haskell:**
```haskell
error "[ProjectValidation] Invalid project structure: Missing required field 'layers'. Fix: Add 'layers' field to project structure with at least one layer."
```

### Bad Examples (Will Fail CI)

**Too vague:**
```lean
throwError "Error"
throwError "Failed"
throwError "Invalid"
```

**Missing fix:**
```lean
throwError "Variable '{n}' not found"  -- No "Fix:" directive
```

**Missing context:**
```lean
throwError "Fix: Add variable"  -- No "what" or "where"
```

## Checklist

Before committing, verify:
- [ ] Error message includes "Fix:" or "fix:" directive
- [ ] Error message explains what went wrong
- [ ] Error message includes location/context
- [ ] Error message is > 50 characters (sufficient detail)
- [ ] Error message is actionable (user can fix it)

## Related Documentation

- [AGENTS.md](./AGENTS.md) - Development protocol
- [.cursorrules](./.cursorrules) - Coding standards
- [CI_CD_SETUP.md](./CI_CD_SETUP.md) - CI/CD pipeline details
