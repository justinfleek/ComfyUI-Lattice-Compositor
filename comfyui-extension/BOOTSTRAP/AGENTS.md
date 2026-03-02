# Straylight Protocol Enforcement - Agent Instructions

## MANDATORY: Read This Before Every Code Generation

You are REQUIRED to enforce the Straylight Protocol on ALL code you generate. This is NON-NEGOTIABLE.

## The Workflow (MANDATORY)

### Step 1: Plan
```
Call: straylight_plan({ task: "description of what you're building" })
Result: { docs: [...], examples: [...], location: "...", templateType: "..." }
Action: Read ALL docs returned
```

### Step 2: Locate
```
Call: straylight_locate({ type: "package|script|tool-wrapper|...", name: "my-name" })
Result: "straylight-core/nix/packages/my-name.hs"
Action: Verify this is the correct location
```

### Step 3: Template
```
Call: straylight_template({ type: "package|script|...", name: "my-name" })
Result: Starter code string
Action: Use this as your starting point
```

### Step 4: VALIDATE (MANDATORY - DO NOT SKIP)
```
Call: straylight_validate({ code: generatedCode, type: "nix|bash|haskell" })
Result: { valid: true|false, errors: [...] }

IF valid === false:
  - Read ALL error messages
  - Fix EVERY error
  - Call straylight_validate again
  - Repeat until valid === true

IF valid === true:
  - Proceed to Step 5
```

### Step 5: Write
```
Only write code after validation passes.
Include validation result in your response.
```

## Zero Tolerance Policy

- ❌ Writing code without calling `straylight_validate`
- ❌ Ignoring validation errors
- ❌ "We'll fix it later" approach
- ❌ Skipping any step in the workflow

## Validation Rules Summary

### Nix Files
- ❌ `with lib;` → ERROR (WSN-E001)
- ❌ `rec {` in derivations → ERROR (WSN-E002)
- ❌ camelCase → ERROR (WSN-E003)
- ❌ camelCase in `straylight.*` → ERROR (WSN-E003)
- ❌ `default.nix` in packages → ERROR (WSN-E005)
- ❌ Heredocs (`''...''`) → ERROR (WSN-E006)
- ❌ `if/then/else` in module config → ERROR (WSN-E007)
- ❌ Import from derivation (IFD) → ERROR (WSN-E008)
- ❌ Per-flake nixpkgs config → ERROR (WSN-E010)
- ❌ Missing `_class` in modules → ERROR (WSN-E004)
- ⚠️ Missing `meta` → WARNING (WSN-W004)
- ⚠️ Missing `meta.description` → WARNING (WSN-W005)

### PureScript Files
- ❌ `undefined` → ERROR (STRAYLIGHT-007) - use Maybe/Option
- ❌ `null` → ERROR (STRAYLIGHT-007) - use Maybe/Option
- ❌ `unsafeCoerce` → ERROR (STRAYLIGHT-007) - use proper type conversions
- ❌ `unsafePartial` → ERROR (STRAYLIGHT-007) - handle all cases explicitly
- ❌ `unsafePerformEffect` → ERROR (STRAYLIGHT-007) - use Effect/Either properly
- ✅ Scripts must `import Straylight.Script` (STRAYLIGHT-004)

### Lean4 Files
- ❌ `sorry` → ERROR (STRAYLIGHT-009)
- ❌ `axiom` → ERROR (STRAYLIGHT-009)
- ❌ `admit` → ERROR (STRAYLIGHT-009)
- ❌ `unsafe` → ERROR (STRAYLIGHT-009)

### File Size
- ❌ Files >500 lines → ERROR (STRAYLIGHT-010)

### Literate Programming (ℵ-011)
- ❌ Code blocks without @target/@name/@description → ERROR (STRAYLIGHT-011-E001)
- ❌ Invalid @target values → ERROR (STRAYLIGHT-011-E005)
- ❌ Duplicate chunk names → ERROR (STRAYLIGHT-011-E002)
- ❌ Undefined chunk references → ERROR (STRAYLIGHT-011-E003)

### C++23
- ❌ `nullptr` without explicit handling → ERROR (STRAYLIGHT-011-E006)
- ❌ Raw `new` / `delete` → ERROR (STRAYLIGHT-011-E007)

### Bash Files
- ❌ `if`, `case`, `for`, `while` → ERROR (STRAYLIGHT-006)
- ❌ Variable assignments → ERROR (STRAYLIGHT-006)
- ✅ Only `exec "$@"` allowed

### Haskell Files
- ❌ Missing `import Straylight.Script` in scripts → ERROR (STRAYLIGHT-004)

## Examples

Use `straylight_examples` to find reference implementations:
```
Call: straylight_examples({ type: "package|script|tool-wrapper" })
Result: ["straylight-core/nix/packages/fmt.hs", ...]
```

## Available Skills

Skills are automatically available and activate based on your request:

- **`straylight-script`** - Use when writing scripts, bash replacement, shell automation
- **`deterministic-coder`** - Use for bug fixes, spec implementations, refactoring (STRAYLIGHT-CORE CONFORMANT)
- **`expert-researcher`** - Use when investigating, verifying claims, or confidence is low
- **`thorough-reading`** - Use when reading files, analyzing code, or tracing dependencies
- **`verification`** - Use when verifying, validating, or checking code
- **`testing-methodology`** - Use when writing tests or test suites
- **`safe-refactoring`** - Use when refactoring code safely
- **`type-cleanup`** - Use when working with types or type systems
- **`exploratory-architect`** - Use for architecture, design, or planning
- **`council`** - Use by prefixing message with "Council:" for expert panel analysis

Skills activate automatically when keywords match your request. For explicit activation, mention the skill name.

## Enforcement

This workflow is ENFORCED by:
- CI pipeline (validates all PRs)
- Pre-commit hook (validates staged files)
- Cursor rules (guides AI generation)
- MCP tools (provides validation)
- Skills (provide specialized methodologies)

**You cannot skip validation. It is mandatory.**
