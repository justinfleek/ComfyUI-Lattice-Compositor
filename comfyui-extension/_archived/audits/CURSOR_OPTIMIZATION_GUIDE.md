# Cursor IDE Optimization Guide

> **Last Updated:** January 2026
> **Purpose:** Best practices and configurations for optimal Cursor AI output

---

## How Cursor Rules Work

### Rules File Format

**Location:** `.cursor/rules/*.mdc` files

**Key Properties:**
- `alwaysApply: true` - Applies to **ALL models** (not just Composer)
- Works with: Composer, Chat, Inline Edit, Background Agent
- Multiple rule files can exist (they're combined)

**Current Setup:**
- `.cursor/rules/core.mdc` - Core development rules (always applies)

---

## Current Optimizations

### ✅ Already Configured

1. **Auto-Formatting Hook**
   - **File:** `.cursor/hooks.json`
   - **Behavior:** Auto-runs `biome check --write` after file edits
   - **Benefit:** Code is always formatted correctly

2. **Evidence-Based Analysis Rules**
   - **File:** `.cursor/rules/core.mdc`
   - **Behavior:** Enforces trace-backed analysis with file:line references
   - **Benefit:** Consistent, verifiable outputs

3. **Project-Specific Guidelines**
   - Master Refactor Plan references
   - Type safety principles
   - Pattern-based fixes

---

## Recommended Additional Optimizations

### 1. Create Domain-Specific Rule Files

**Why:** Different domains (export, stores, engine) have different patterns.

**Example:** `.cursor/rules/export-schemas.mdc`
```markdown
---
description: Export schema validation rules
alwaysApply: false
tags: [export, schemas]
---

## EXPORT SCHEMA RULES

### PROPERTY NAME VERIFICATION
- Always verify tensor input property names match ComfyUI node expectations
- Use exact file:line references when checking workflow templates
- Validate schemas match actual export function outputs

### TRANSFORMATION FUNCTIONS
- Create transformation functions for format mismatches
- Validate outputs before returning
- Document format conversions explicitly
```

**Usage:** Reference with `@export-schemas` in chat

---

### 2. Create Context Files (Notepads)

**Why:** Store reusable context that AI can reference.

**Example:** `.cursor/notepads/master-plan.md`
```markdown
# Master Refactor Plan Quick Reference

## Current Phase: Phase 1 (Weeks 3-10)
- **Status:** In progress - layerStore migration
- **Exit Criteria:** All 60 consumer files updated, tests pass
- **Next:** Phase 2 - Keyframes, Animation & Expressions

## Key Files:
- `docs/MASTER_REFACTOR_PLAN.md` - Full plan
- `docs/STORE_MIGRATION_CONSUMERS.md` - Consumer list
```

**Usage:** Reference with `@master-plan` in chat

---

### 3. Add More Hooks

**File:** `.cursor/hooks.json` (extend existing)

```json
{
  "version": 1,
  "hooks": {
    "afterFileEdit": [
      {
        "command": "npx biome check --write \"$CURSOR_FILE_PATH\"",
        "workingDirectory": "ui"
      }
    ],
    "beforeCommit": [
      {
        "command": "npm test",
        "workingDirectory": "ui",
        "failOnError": false
      }
    ],
    "afterFileCreate": [
      {
        "command": "echo 'New file created: $CURSOR_FILE_PATH'",
        "workingDirectory": "."
      }
    ]
  }
}
```

---

### 4. MCP Server Configuration (PRIVATE ONLY)

**File:** `.cursor/mcp.json` (NEW, if needed)

**Note:** MCP servers are **PRIVATE to your workspace only**. They do NOT share with team/community unless explicitly configured for that purpose. This is for local project context management.

**Current Status:** Not configured (optional)

**If Needed:**
```json
{
  "mcpServers": {
    "lattice-compositor": {
      "command": "node",
      "args": ["./scripts/mcp-server.js"],
      "env": {
        "PROJECT_ROOT": "${workspaceFolder}"
      }
    }
  }
}
```

**Benefit:** Local project context management (private to your workspace)

---

### 5. Use @ Commands Effectively

**Best Practices:**

- `@folders` - Load entire project context
- `@docs` - Load documentation folder
- `@tests` - Load test files
- `@schemas` - Load schema files
- `@master-plan` - Load master refactor plan

**Pro Tip:** Create aliases in rule files:
```markdown
## CONTEXT ALIASES
- `@project` = @folders ui/src
- `@exports` = @folders ui/src/services/export
- `@stores` = @folders ui/src/stores
```

---

### 6. Leverage Composer for Multi-File Changes

**When to Use:**
- Refactoring across multiple files
- Creating new features with multiple components
- Pattern-based fixes (fix ALL instances)

**Example Prompt:**
```
Refactor all export functions to use new schema validation.
Files affected: ui/src/services/export/*.ts
Pattern: Add validateExportResult() call before returning
```

---

### 7. Use Inline Edit with Background Awareness

**Workflow:**
1. Highlight code to change
2. Press `Ctrl/Cmd + I`
3. Review "Background Agent" suggestions in sidebar
4. Apply comprehensive edits

**Benefit:** AI sees related files automatically

---

### 8. Configure Bug Finder

**Enable:** Settings → Features → Bug Finder (Beta)

**Use Cases:**
- Before committing: Scan branch for issues
- After refactoring: Verify no regressions
- Code audits: Find unhandled nulls, deprecated APIs

---

### 9. Auto-Generate Commit Messages

**How:**
1. Stage changes
2. Open Composer
3. Ask: "Generate commit message for staged changes"
4. AI analyzes diffs and project history

**Benefit:** Consistent, descriptive commits

---

### 10. Image-to-Code Feature

**Use Cases:**
- UI mockups → React/Vue components
- Design references → Implementation
- Screenshot debugging → Code fixes

**How:** Paste image into chat, describe what you want

---

## Advanced: Model-Specific Rules

### Create Model-Specific Rule Files

**Example:** `.cursor/rules/composer-only.mdc`
```markdown
---
description: Composer-specific optimizations
alwaysApply: false
models: [composer]
---

## COMPOSER-SPECIFIC RULES

### MULTI-FILE REFACTORING
- Always show affected files list before starting
- Group related changes together
- Verify all instances of pattern are fixed
- Run tests after multi-file changes
```

---

## Performance Tips

### 1. Limit Context Size
- Use `@` commands selectively
- Don't load entire codebase unless needed
- Use `.cursorignore` to exclude large files

### 2. Use Incremental Context
- Start with specific files
- Expand context as needed
- Use `@` commands to add context incrementally

### 3. Cache Frequently Used Context
- Create notepads for common references
- Use rule files for patterns
- Reference documentation files directly

---

## Troubleshooting

### Rules Not Applying?
- Check `alwaysApply: true` in frontmatter
- Verify file is in `.cursor/rules/` directory
- Restart Cursor after adding new rules

### Hooks Not Running?
- Check `hooks.json` syntax
- Verify commands are in PATH
- Check working directory is correct

### Context Too Large?
- Use `.cursorignore` to exclude files
- Break rules into smaller files
- Use `@` commands instead of loading everything

---

## Recommended File Structure

```
.cursor/
├── rules/
│   ├── core.mdc              # Always applies
│   ├── export-schemas.mdc    # Export-specific
│   ├── store-migration.mdc   # Store refactor
│   └── testing.mdc           # Test patterns
├── notepads/
│   ├── master-plan.md        # Quick ref
│   ├── export-targets.md     # Export formats
│   └── common-patterns.md    # Code patterns
├── hooks.json                # Auto-formatting
└── mcp.json                  # MCP server config (optional)
```

---

## Quick Reference

**Best Practices:**
1. ✅ Use evidence-based analysis (file:line traces)
2. ✅ Verify before creating files
3. ✅ Connect to master plan
4. ✅ Use @ commands for context
5. ✅ Leverage Composer for multi-file changes
6. ✅ Use hooks for auto-formatting
7. ✅ Create domain-specific rule files
8. ✅ Use notepads for reusable context

**Avoid:**
1. ❌ Creating files without checking existing code
2. ❌ Making changes without traces
3. ❌ Working in isolation from master plan
4. ❌ Loading entire codebase unnecessarily
5. ❌ Ignoring existing tooling

---

## Additional Optimizations Based on Codebase Analysis

### 11. Leverage Existing Documentation

**Key Documents to Reference:**
- `docs/BULLETPROOF_CODEBASE_GUIDE.md` - Complete methodology guide
- `docs/MASTER_REFACTOR_PLAN.md` - Current phase and strategy
- `docs/STORE_MIGRATION_CONSUMERS.md` - Consumer file mapping
- `WEYL_COMPOSITOR_MASTER_PLAN.md` - Hyper-modern coding axioms
- `docs/EVIDENCE_BASED_ANALYSIS_METHODOLOGY.md` - Analysis methodology

**Usage:** Reference these documents in chat with `@` commands

### 12. Follow Evidence-Based Analysis

**Required Output Format:**
1. Summary with exact traces (file:line references)
2. "Why This Is Not Myopic" section (master plan context)
3. "Next Step" section (single best path forward)
4. "Steps Back to Main Refactor" section (clear return path)

**Example:**
```
## Summary
- **Line 2234:** `tracks: JSON.stringify(params.motionData?.tracks)`
- **Source:** `ui/src/services/comfyui/workflowTemplates.ts:2234`
- **Verification:** Checked against export function output

## Why This Is Not Myopic
This connects to Phase 4 (Export & Import) of the Master Refactor Plan.
Ensuring export formats match model requirements prevents user frustration.

## Next Step
Create transformation function for MotionCtrl tensor input format.

## Steps Back to Main Refactor
1. Complete export format verification
2. Return to Phase 1 verification (layerStore migration)
```

### 13. Verify Before Creating

**Rule:** Never create files without:
1. Searching codebase for existing patterns
2. Reading actual implementation (not just types)
3. Verifying against runtime usage
4. Checking test files for examples

**Checklist:**
- [ ] `grep -r "similarPattern"` - Does it exist?
- [ ] Read actual implementation files
- [ ] Check test files for examples
- [ ] Verify against runtime usage
- [ ] Only then create/update files

### 14. Pattern-Based Fixes

**Rule:** Fix ALL instances of a pattern across codebase

**Never:**
- Fix one file and move on
- Create a new file without checking existing code
- Assume naming conventions

**Always:**
- Search for all instances first
- Fix systematically
- Verify fixes with tests

---

## References

- [Cursor Documentation](https://cursor.sh/docs)
- Evidence-Based Methodology: `docs/EVIDENCE_BASED_ANALYSIS_METHODOLOGY.md`
- Master Refactor Plan: `docs/MASTER_REFACTOR_PLAN.md`
- Bulletproof Guide: `docs/BULLETPROOF_CODEBASE_GUIDE.md`
- Hyper-Modern Axioms: `WEYL_COMPOSITOR_MASTER_PLAN.md`
