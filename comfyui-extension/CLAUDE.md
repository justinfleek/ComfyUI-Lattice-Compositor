# STRAYLIGHT PROTOCOL - MANDATORY ENFORCEMENT

**🚨 CRITICAL: This protocol is ENFORCED. You MUST follow the workflow below for EVERY code generation. No exceptions.**

## MANDATORY WORKFLOW - ENFORCED ON EVERY MESSAGE

**You are REQUIRED to follow these steps in order. Skipping any step is a violation.**

### Step 1: Plan
```
Call: straylight_plan({ task: "what you're building" })
Read: ALL documentation files returned
```

### Step 2: Locate
```
Call: straylight_locate({ type: "package|script|...", name: "my-name" })
Verify: File location is correct per CONTRIBUTING.md
```

### Step 3: Template
```
Call: straylight_template({ type: "package|script|...", name: "my-name" })
Use: Template as starting point for your code
```

### Step 4: VALIDATE (MANDATORY - CANNOT BE SKIPPED)
```
Call: straylight_validate({ code: yourGeneratedCode, type: "nix|bash|haskell" })

IF valid === false:
  - STOP. Do not write code.
  - Read ALL error messages
  - Fix EVERY error
  - Call straylight_validate again
  - Repeat until valid === true

IF valid === true:
  - Proceed to write code
  - Include validation result in your response
```

### Step 5: Write
```
Only write code after validation passes.
Show validation result: "✅ Code validated: valid: true"
```

## NEVER SKIP VALIDATION - THIS IS ENFORCED

**You are REQUIRED to call `straylight_validate` for EVERY piece of code you generate.**

**Consequences of skipping:**
- Your response is incomplete
- Code will be rejected by CI
- Code will be rejected by pre-commit hook
- You are violating protocol

**Validation is MANDATORY, not optional.**

## Example Workflow

```
1. User asks: "Create a new package called my-tool"
2. You call: straylight_plan({ task: "create package my-tool" })
3. You read: docs returned by straylight_plan
4. You call: straylight_template({ type: "package", name: "my-tool" })
5. You modify: Template to match requirements
6. You call: straylight_validate({ code: modifiedCode, type: "nix" })
7. If valid: false → Fix errors → Call straylight_validate again
8. If valid: true → Write code with message "✅ Validated"
```

## Quick Reference

### Before Writing Nix Code
- Read: `straylight-protocol/docs/rfc/straylight-001-standard-nix.md` OR `straylight-core/docs/rfc/straylight-001-standard-nix.md`
- Rules: lisp-case naming, no `with lib;`, use `finalAttrs:`, packages need `meta`

### Before Writing Bash
- Read: `straylight-protocol/docs/rfc/straylight-006-safe-bash.md` OR `straylight-core/docs/rfc/straylight-006-safe-bash.md`
- Rule: ONLY `exec "$@"` allowed. No logic, no variables, no conditionals.

### Before Writing Scripts
- Read: `skills/straylight-script/SKILL.md` OR `straylight-core/docs/skills/straylight-script/SKILL.md`
- Rule: Must `import Straylight.Script`, use typed tool wrappers
- Skill: `straylight-script` activates automatically when writing scripts or bash replacement

## Available Skills

Skills provide specialized methodologies and activate based on your request:

- **`straylight-script`** - Activates for: script writing, bash replacement, shell automation, command-line tools
- **`deterministic-coder`** - Activates for: bug fixes, implementations, refactoring (enforces Straylight Protocol)
- **`expert-researcher`** - Activates for: research, investigation, verification, fact-checking
- **`thorough-reading`** - Activates for: reading files, code analysis, dependency tracing
- **`verification`** - Activates for: verification, validation, checking code
- **`testing-methodology`** - Activates for: test writing, test suites, testing strategies
- **`safe-refactoring`** - Activates for: refactoring, code restructuring
- **`type-cleanup`** - Activates for: type work, type systems, typing
- **`exploratory-architect`** - Activates for: architecture, design, planning
- **`council`** - Manual trigger: Prefix message with "Council:" for expert panel analysis

**Note:** Skills in Claude Code require explicit mention or the "Council:" prefix for reliable activation.

### File Locations
**Note:** Project structure may vary. Use `straylight_locate` to verify correct location.

Common patterns:
- Packages: `straylight-core/nix/packages/{name}.hs` OR `nix/packages/{name}.hs`
- Scripts: `straylight-core/nix/scripts/{name}.hs` OR `nix/scripts/{name}.hs`
- Tool wrappers: `straylight-core/nix/scripts/Straylight/Script/Tools/{Name}.hs` OR `nix/scripts/Straylight/Script/Tools/{Name}.hs`
- Modules: `straylight-core/nix/modules/flake/{name}.nix` OR `nix/modules/flake/{name}.nix`

**Always use `straylight_locate` to verify correct location for your project structure.**

## Validation Rules

### Nix Forbidden Patterns
- `with lib;` → use `inherit (lib) x y;` (WSN-E001)
- `rec {` in derivations → use `finalAttrs:` (WSN-E002)
- camelCase → use lisp-case (WSN-E003)
- camelCase in `straylight.*` → use lisp-case (WSN-E003)
- `default.nix` in packages → use `{name}.nix` (WSN-E005)
- Heredocs (`''...''`) → use `writeText` or file imports (WSN-E006)
- `if/then/else` in module config → use `mkIf` (WSN-E007)
- Import from derivation (IFD) → restructure (WSN-E008)
- Per-flake nixpkgs config → use centralized config (WSN-E010)
- Missing `meta` → add with description, license (WSN-W004)
- Missing `_class` in modules → add `_class = "flake"` or `"nixos"` (WSN-E004)

### Bash Forbidden Patterns
- `if`, `case`, `for`, `while` → rewrite in Haskell
- Variable assignments → rewrite in Haskell
- Command substitution → rewrite in Haskell
- Only safe pattern: `exec "$@"`

### Haskell/PureScript Required Patterns
- Scripts must `import Straylight.Script` (STRAYLIGHT-004)
- Tool wrappers must be in `Straylight.Script.Tools.*`

### PureScript Forbidden Patterns
- `undefined` → use Maybe/Option (STRAYLIGHT-007)
- `null` → use Maybe/Option (STRAYLIGHT-007)
- `unsafeCoerce` → use proper type conversions (STRAYLIGHT-007)
- `unsafePartial` → handle all cases explicitly (STRAYLIGHT-007)
- `unsafePerformEffect` → use Effect/Either properly (STRAYLIGHT-007)

## Examples

Use `straylight_examples` to find reference implementations for your project structure:
- Tool wrappers: Check `straylight-core/nix/scripts/Straylight/Script/Tools/` OR `nix/scripts/Straylight/Script/Tools/`
- Scripts: Check `straylight-core/nix/scripts/` OR `nix/scripts/`
- Packages: Check `straylight-core/nix/packages/` OR `nix/packages/`

**Note:** Paths may vary based on project structure. Use `straylight_examples` tool to find actual examples in your project.
