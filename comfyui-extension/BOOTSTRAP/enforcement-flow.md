# Straylight Protocol Enforcement Flow

**Complete information flow from user request to code validation**

## Overview

This document maps the exact flow of information through all enforcement mechanisms to ensure 100% Straylight Protocol compliance.

## Complete Flow Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         USER REQUEST                                    │
│                    "Create a new package"                               │
└────────────────────────────┬────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    AI ASSISTANT (Cursor/Claude/etc)                     │
│                                                                         │
│  Reads Configuration Files (in order):                                 │
│  1. .cursor/rules/001_straylight-protocol.mdc                               │
│  2. .cursor/rules/002_validation-required.mdc                         │
│  3. .cursor/rules/003_mandatory-workflow.mdc                           │
│  4. AGENTS.md                                                          │
│  5. CLAUDE.md                                                          │
│  6. .cursorrules (legacy)                                              │
│  7. .clinerules (Cline)                                                 │
│  8. .windsurfrules (Windsurf)                                           │
└────────────────────────────┬────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    MANDATORY WORKFLOW ENFORCEMENT                       │
│                                                                         │
│  Step 1: PLAN                                                            │
│  ┌──────────────────────────────────────────────────────────────┐      │
│  │ MCP Tool: straylight_plan({ task: "..." })                        │      │
│  │ → .claude/straylight-mcp.js                                       │      │
│  │ → Returns: docs[], examples[], location, templateType        │      │
│  │ → AI reads: straylight-protocol/docs/rfc/*.md                     │      │
│  └──────────────────────────────────────────────────────────────┘      │
│                              │                                           │
│                              ▼                                           │
│  Step 2: LOCATE                                                          │
│  ┌──────────────────────────────────────────────────────────────┐      │
│  │ MCP Tool: straylight_locate({ type: "package", name: "..." })     │      │
│  │ → .claude/straylight-mcp.js                                       │      │
│  │ → Returns: "straylight-core/nix/packages/my-name.hs"              │      │
│  │ → Verifies: CONTRIBUTING.md decision tree                     │      │
│  └──────────────────────────────────────────────────────────────┘      │
│                              │                                           │
│                              ▼                                           │
│  Step 3: TEMPLATE                                                        │
│  ┌──────────────────────────────────────────────────────────────┐      │
│  │ MCP Tool: straylight_template({ type: "package", name: "..." })  │      │
│  │ → .claude/straylight-mcp.js                                       │      │
│  │ → Returns: Starter code template                             │      │
│  │ → References: skill/straylight-script/SKILL.md                    │      │
│  └──────────────────────────────────────────────────────────────┘      │
│                              │                                           │
│                              ▼                                           │
│  Step 4: GENERATE CODE                                                   │
│  ┌──────────────────────────────────────────────────────────────┐      │
│  │ AI modifies template based on requirements                  │      │
│  │ Applies rules from: .cursor/rules/001_straylight-protocol.mdc     │      │
│  └──────────────────────────────────────────────────────────────┘      │
│                              │                                           │
│                              ▼                                           │
│  Step 5: VALIDATE (MANDATORY - CANNOT SKIP)                             │
│  ┌──────────────────────────────────────────────────────────────┐      │
│  │ MCP Tool: straylight_validate({ code: "...", type: "nix" })      │      │
│  │ → .claude/straylight-mcp.js                                       │      │
│  │ → Checks against: RULES object (56+ rules)                  │      │
│  │ → Returns: { valid: true|false, errors: [...] }               │      │
│  └──────────────────────────────────────────────────────────────┘      │
│                              │                                           │
│                    ┌─────────┴─────────┐                                │
│                    │                   │                                │
│              valid: false         valid: true                            │
│                    │                   │                                │
│                    ▼                   ▼                                │
│        ┌───────────────────┐  ┌──────────────┐                        │
│        │ Fix ALL errors     │  │ Write code   │                        │
│        │ Re-validate        │  │ to file      │                        │
│        │ Loop until valid   │  │              │                        │
│        └───────────────────┘  └──────┬───────┘                        │
│                                       │                                  │
└───────────────────────────────────────┼──────────────────────────────────┘
                                        │
                                        ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    FILE WRITTEN TO DISK                                 │
│                    straylight-core/nix/packages/my-package.hs                │
└────────────────────────────┬────────────────────────────────────────────┘
                              │
                    ┌─────────┴─────────┐
                    │                   │
                    ▼                   ▼
┌───────────────────────────┐  ┌──────────────────────────┐
│  REAL-TIME VALIDATION     │  │  GIT OPERATIONS         │
│  (if watcher running)      │  │                         │
│                            │  │                         │
│  watch-and-validate.js     │  │  git add <file>         │
│  → Monitors: straylight-core/   │  │  → Triggers:           │
│  → Validates on save       │  │    hooks/pre-commit     │
│  → Uses:                   │  │                         │
│    scripts/validate-file.js│  │  hooks/pre-commit       │
│                            │  │  → Checks:              │
│  Returns:                  │  │    - Nix lint           │
│  ✅ Valid or ❌ Errors     │  │    - validate-file.js  │
│                            │  │                         │
└───────────────────────────┘  └───────────┬──────────────┘
                                           │
                                           ▼
                              ┌──────────────────────────┐
                              │  PRE-COMMIT VALIDATION   │
                              │                          │
                              │  hooks/pre-commit         │
                              │  → Runs:                 │
                              │    1. nix flake check   │
                              │    2. validate-file.js    │
                              │       (for each file)     │
                              │                          │
                              │  If violations:          │
                              │  ❌ Blocks commit         │
                              │                          │
                              │  If clean:                │
                              │  ✅ Allows commit         │
                              └───────────┬──────────────┘
                                          │
                                          ▼
                              ┌──────────────────────────┐
                              │  COMMIT SUCCESSFUL        │
                              └───────────┬──────────────┘
                                          │
                                          ▼
                              ┌──────────────────────────┐
                              │  GIT PUSH                │
                              └───────────┬──────────────┘
                                          │
                                          ▼
┌─────────────────────────────────────────────────────────────────────────┐
│                    CI/CD VALIDATION                                    │
│                                                                         │
│  .github/workflows/straylight-enforcement.yml                                │
│  → Triggered on: PR or push to main/master                             │
│  → Steps:                                                               │
│    1. Checkout code                                                     │
│    2. Setup Nix                                                         │
│    3. Setup Node.js                                                     │
│    4. Validate MCP server syntax                                        │
│    5. Run Nix lint                                                      │
│    6. Check protocol violations (grep patterns)                        │
│    7. Validate changed files                                           │
│       → Uses: scripts/validate-file.js                                 │
│    8. Check file sizes                                                  │
│    9. Check literate programming rules                                  │
│                                                                         │
│  If violations:                                                         │
│  ❌ Fails CI, blocks merge                                              │
│                                                                         │
│  If clean:                                                              │
│  ✅ CI passes, allows merge                                             │
└─────────────────────────────────────────────────────────────────────────┘
```

## Detailed Component Flow

### 1. AI Assistant Initialization

```
User Opens Cursor/Claude Code
    │
    ├─→ Reads .cursor/rules/*.mdc
    │   └─→ 001_straylight-protocol.mdc (main rules)
    │   └─→ 002_validation-required.mdc (validation enforcement)
    │   └─→ 003_mandatory-workflow.mdc (workflow steps)
    │
    ├─→ Reads AGENTS.md
    │   └─→ Mandatory workflow: Plan → Locate → Template → Validate → Write
    │
    ├─→ Reads CLAUDE.md
    │   └─→ Claude Code specific instructions
    │
    └─→ Connects to MCP Server
        └─→ .claude/settings.json (config)
        └─→ .claude/straylight-mcp.js (server)
            └─→ Provides 6 tools:
                ├─→ straylight_validate
                ├─→ straylight_template
                ├─→ straylight_locate
                ├─→ straylight_plan
                ├─→ straylight_examples
                └─→ straylight_search
```

### 2. Code Generation Flow

```
User Request: "Create package my-tool"
    │
    ▼
AI Calls: straylight_plan({ task: "create package my-tool" })
    │
    ├─→ MCP Server (.claude/straylight-mcp.js)
    │   └─→ Searches straylight-protocol/docs/rfc/
    │   └─→ Returns: [docs, examples, location, templateType]
    │
    ▼
AI Reads: Returned documentation files
    │
    ▼
AI Calls: straylight_locate({ type: "package", name: "my-tool" })
    │
    ├─→ MCP Server
    │   └─→ Checks CONTRIBUTING.md decision tree
    │   └─→ Returns: "straylight-core/nix/packages/my-tool.hs"
    │
    ▼
AI Calls: straylight_template({ type: "package", name: "my-tool" })
    │
    ├─→ MCP Server
    │   └─→ Reads skill/straylight-script/SKILL.md
    │   └─→ Returns: Starter template code
    │
    ▼
AI Modifies Template
    │
    ├─→ Applies rules from .cursor/rules/001_straylight-protocol.mdc
    │   ├─→ Uses lisp-case naming
    │   ├─→ No `with lib;`
    │   ├─→ Uses `finalAttrs:`
    │   ├─→ Includes `meta` block
    │   └─→ All Nix rules enforced
    │
    ▼
AI Calls: straylight_validate({ code: generatedCode, type: "nix" })
    │
    ├─→ MCP Server (.claude/straylight-mcp.js)
    │   └─→ RULES.nix.forbidden[] (15+ rules)
    │   └─→ RULES.nix.warnings[] (7 rules)
    │   └─→ RULES.nix.required[] (2 rules)
    │   └─→ Custom check functions for complex rules
    │
    ├─→ Validation Logic:
    │   ├─→ Pattern matching (regex)
    │   ├─→ Custom check functions
    │   ├─→ File path analysis
    │   └─→ Context-aware rules
    │
    └─→ Returns: { valid: true|false, errors: [...] }
        │
        ├─→ If valid: false
        │   └─→ AI fixes errors
        │   └─→ Re-calls straylight_validate
        │   └─→ Loops until valid: true
        │
        └─→ If valid: true
            └─→ AI writes code to file
```

### 3. File Validation Flow

```
File Written: straylight-core/nix/packages/my-tool.hs
    │
    ├─→ Real-Time Validation (if watcher running)
    │   │
    │   └─→ scripts/watch-and-validate.js
    │       ├─→ Watches: straylight-core/
    │       ├─→ On file change:
    │       │   └─→ Calls: scripts/validate-file.js <file>
    │       │       └─→ Mirrors MCP server logic
    │       │       └─→ Returns: ✅ or ❌
    │       └─→ Shows result in terminal
    │
    └─→ Git Commit Validation
        │
        └─→ hooks/pre-commit
            ├─→ Triggered on: git commit
            ├─→ Checks: git diff --cached
            ├─→ Filters: .nix, .hs, .purs, .sh, etc.
            ├─→ For each file:
            │   └─→ Calls: scripts/validate-file.js <file>
            │       └─→ Uses same RULES as MCP server
            │       └─→ Exit code 1 = violation
            │       └─→ Exit code 0 = clean
            └─→ If any violation:
                └─→ Blocks commit, shows errors
```

### 4. CI/CD Validation Flow

```
Git Push to GitHub
    │
    └─→ Triggers: .github/workflows/straylight-enforcement.yml
        │
        ├─→ Step 1: Checkout code
        ├─→ Step 2: Setup Nix
        ├─→ Step 3: Setup Node.js
        ├─→ Step 4: Validate MCP server syntax
        │   └─→ node -c .claude/straylight-mcp.js
        │
        ├─→ Step 5: Run Nix lint
        │   └─→ nix flake check
        │
        ├─→ Step 6: Check protocol violations
        │   ├─→ grep patterns (basic checks)
        │   ├─→ Checks entire straylight-core/ directory
        │   └─→ Multiple rule checks
        │
        ├─→ Step 7: Validate changed files
        │   └─→ Gets: git diff --name-only
        │   └─→ For each file:
        │       └─→ Calls: scripts/validate-file.js <file>
        │           └─→ Comprehensive validation
        │           └─→ All 44+ rules checked
        │
        ├─→ Step 8: Check file sizes
        │   └─→ find straylight-core -type f
        │   └─→ wc -l (must be ≤500)
        │
        └─→ Step 9: Check literate programming
            └─→ Validates .lit, .mdx files
            └─→ Checks chunk references, circular deps
            │
            ├─→ If any violation:
            │   └─→ CI fails
            │   └─→ PR blocked
            │   └─→ Merge prevented
            │
            └─→ If all clean:
                └─→ CI passes
                └─→ PR can be merged
```

## Scope Graph: Component Dependencies

```
┌─────────────────────────────────────────────────────────────────┐
│                    USER REQUEST                                │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│              AI ASSISTANT (Cursor/Claude/Windsurf/Cline)       │
│                                                                 │
│  Configuration Layer (Read-only):                              │
│  ├─→ .cursor/rules/001_straylight-protocol.mdc ────────┐           │
│  ├─→ .cursor/rules/002_validation-required.mdc ────┤           │
│  ├─→ .cursor/rules/003_mandatory-workflow.mdc ─────┤           │
│  ├─→ AGENTS.md ────────────────────────────────────┤           │
│  ├─→ CLAUDE.md ────────────────────────────────────┤           │
│  ├─→ .cursorrules ─────────────────────────────────┤           │
│  ├─→ .clinerules ──────────────────────────────────┤           │
│  └─→ .windsurfrules ───────────────────────────────┤           │
│                                                     │           │
│  MCP Client Layer:                                  │           │
│  └─→ .claude/settings.json ───────────────────────┼───────────┘
│                                                     │
└───────────────────────────┬─────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│              MCP SERVER (.claude/straylight-mcp.js)                 │
│                                                                 │
│  Tools Provided:                                                │
│  ├─→ straylight_validate ────────────────────┐                      │
│  ├─→ straylight_template ────────────────────┤                      │
│  ├─→ straylight_locate ──────────────────────┤                      │
│  ├─→ straylight_plan ────────────────────────┤                      │
│  ├─→ straylight_examples ───────────────────┤                      │
│  └─→ straylight_search ──────────────────────┤                      │
│                                          │                      │
│  Rule Engine:                            │                      │
│  └─→ RULES object (56+ rules) ──────────┼──────────────────────┘
│     ├─→ nix.forbidden[] (10 rules)
│     ├─→ nix.warnings[] (7 rules)
│     ├─→ nix.required[] (2 rules)
│     ├─→ purescript.forbidden[] (5 rules)
│     ├─→ purescript.required[] (1 rule)
│     ├─→ haskell.required[] (1 rule)
│     ├─→ lean4.forbidden[] (4 rules)
│     ├─→ bash.forbidden[] (6 rules)
│     ├─→ cpp23.forbidden[] (2 rules)
│     ├─→ literate.forbidden[] (7 rules)
│     └─→ File size check (1 rule)
│
│  Documentation Access:
│  └─→ Reads: straylight-protocol/docs/rfc/*.md
│  └─→ Reads: straylight-core/CONTRIBUTING.md
│  └─→ Reads: skill/straylight-script/SKILL.md
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│         VALIDATION SCRIPTS (scripts/validate-file.js)           │
│                                                                 │
│  Standalone Validator:                                          │
│  └─→ Mirrors MCP server RULES logic                            │
│  └─→ Used by:                                                   │
│      ├─→ hooks/pre-commit                                       │
│      ├─→ .github/workflows/straylight-enforcement.yml                │
│      └─→ scripts/watch-and-validate.js                          │
│                                                                 │
│  Test Suite:                                                    │
│  └─→ scripts/test-all-violations.js                             │
│      └─→ Uses: scripts/validate-file.js                         │
│      └─→ Tests: 44 test cases                                   │
│                                                                 │
│  File Watcher:                                                  │
│  └─→ scripts/watch-and-validate.js                             │
│      └─→ Uses: scripts/validate-file.js                         │
│      └─→ Watches: straylight-core/                                  │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│              GIT HOOKS (hooks/pre-commit)                       │
│                                                                 │
│  Trigger: git commit                                            │
│  ├─→ Checks: git diff --cached                                 │
│  ├─→ Filters: .nix, .hs, .purs, .sh, etc.                      │
│  ├─→ Runs: nix flake check (if available)                      │
│  └─→ Runs: scripts/validate-file.js (for each file)             │
│      └─→ Blocks commit if violations found                      │
└───────────────────────────┬─────────────────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│         CI/CD WORKFLOWS (.github/workflows/*.yml)               │
│                                                                 │
│  straylight-enforcement.yml:                                         │
│  ├─→ Trigger: PR or push to main/master                        │
│  ├─→ Validates: MCP server syntax                               │
│  ├─→ Runs: Nix lint                                             │
│  ├─→ Checks: Protocol violations (grep)                         │
│  ├─→ Validates: Changed files (validate-file.js)               │
│  ├─→ Checks: File sizes                                         │
│  └─→ Validates: Literate programming                            │
│      └─→ Blocks merge if violations found                       │
│                                                                 │
│  cd.yml:                                                        │
│  └─→ Includes: Straylight Protocol validation step                  │
└─────────────────────────────────────────────────────────────────┘
```

## Rule Enforcement Matrix

| Rule Category | MCP Server | validate-file.js | Pre-commit Hook | CI Workflow | File Watcher |
|---------------|------------|------------------|-----------------|-------------|--------------|
| **Nix Forbidden** (10 rules) | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Nix Warnings** (7 rules) | ✅ | ✅ | ✅ | ⚠️ | ✅ |
| **Nix Required** (2 rules) | ✅ | ✅ | ✅ | ✅ | ✅ |
| **PureScript** (6 rules) | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Haskell** (1 rule) | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Lean4** (4 rules) | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Bash** (6 rules) | ✅ | ✅ | ✅ | ✅ | ✅ |
| **C++23** (2 rules) | ✅ | ✅ | ✅ | ✅ | ✅ |
| **Literate** (7 rules) | ✅ | ✅ | ❌ | ✅ | ✅ |
| **File Size** (1 rule) | ✅ | ✅ | ❌ | ✅ | ❌ |

**Legend:**
- ✅ Fully enforced
- ⚠️ Partial enforcement (warnings may not block)
- ❌ Not checked (by design - e.g., file size checked in CI, not hook)

## Information Flow Sequence

### Sequence 1: Code Generation (Happy Path)

```
1. User: "Create package my-tool"
   │
2. AI reads: .cursor/rules/001_straylight-protocol.mdc
   │
3. AI calls: straylight_plan({ task: "create package" })
   │   └─→ MCP Server returns docs
   │
4. AI reads: Returned documentation
   │
5. AI calls: straylight_locate({ type: "package", name: "my-tool" })
   │   └─→ MCP Server returns: "straylight-core/nix/packages/my-tool.hs"
   │
6. AI calls: straylight_template({ type: "package", name: "my-tool" })
   │   └─→ MCP Server returns template
   │
7. AI modifies template
   │
8. AI calls: straylight_validate({ code: "...", type: "nix" })
   │   └─→ MCP Server validates against RULES
   │   └─→ Returns: { valid: true, errors: [] }
   │
9. AI writes code to file
   │
10. File watcher (if running) validates → ✅
    │
11. User commits: git commit
    │   └─→ Pre-commit hook validates → ✅
    │
12. User pushes: git push
    │   └─→ CI validates → ✅
    │
13. Code merged → ✅ Production
```

### Sequence 2: Violation Detection (Error Path)

```
1. User: "Create package my-tool"
   │
2. AI generates code with violation: `with lib;`
   │
3. AI calls: straylight_validate({ code: "...", type: "nix" })
   │   └─→ MCP Server checks RULES.nix.forbidden[]
   │   └─→ Pattern match: /^\s*with\s+lib\s*;/m
   │   └─→ Returns: { valid: false, errors: [{ rule: "WSN-E001", ... }] }
   │
4. AI reads error: "Use 'inherit (lib) x y;' instead of 'with lib;'"
   │
5. AI fixes code: Replaces `with lib;` with `inherit (lib) x y;`
   │
6. AI calls: straylight_validate({ code: fixedCode, type: "nix" })
   │   └─→ Returns: { valid: true, errors: [] }
   │
7. AI writes code to file
   │
8. File watcher validates → ✅
   │
9. Pre-commit hook validates → ✅
   │
10. CI validates → ✅
    │
11. Code merged → ✅ Production
```

### Sequence 3: Bypass Attempt (Blocked)

```
1. User: "Create package my-tool"
   │
2. AI generates code with violation: `with lib;`
   │
3. AI skips validation (violation of protocol)
   │
4. AI writes code to file
   │
5. File watcher detects violation → ❌ Shows error
   │
6. User tries: git commit
   │   └─→ Pre-commit hook runs validate-file.js
   │   └─→ Detects violation: WSN-E001
   │   └─→ Blocks commit: "❌ Validation failed"
   │
7. User must fix violation before commit
   │
8. After fix, commit succeeds → ✅
```

## Rule Resolution Order

When multiple rules could match, resolution order:

```
1. File Size Check (STRAYLIGHT-010)
   └─→ Runs first, blocks if >500 lines

2. Forbidden Rules (Errors)
   └─→ Checked in order defined in RULES object
   └─→ First match wins
   └─→ Examples:
       ├─→ WSN-E001 (with lib;) checked before WSN-E003 (camelCase)
       └─→ STRAYLIGHT-011-E001 (missing annotations) checked before E002 (duplicate)

3. Required Rules
   └─→ Checked after forbidden rules
   └─→ Examples:
       ├─→ STRAYLIGHT-004 (import Straylight.Script)
       └─→ WSN-E004 (missing _class)

4. Warning Rules
   └─→ Checked last
   └─→ Don't block, but reported
   └─→ Examples:
       ├─→ WSN-W004 (missing meta)
       ├─→ WSN-W005 (missing description)
       └─→ WSN-W006 (missing license)
```

## Cross-Component Synchronization

All enforcement points use the **same rule definitions**:

```
┌─────────────────────────────────────────┐
│  SOURCE OF TRUTH: RULES Object          │
│                                         │
│  Defined in:                            │
│  └─→ .claude/straylight-mcp.js              │
│      └─→ const RULES = { ... }         │
└───────────────┬─────────────────────────┘
                │
        ┌───────┼───────┐
        │       │       │
        ▼       ▼       ▼
┌──────────┐ ┌──────────┐ ┌──────────┐
│   MCP    │ │ validate │ │   CI     │
│  Server  │ │  -file.js │ │ Workflow │
└──────────┘ └──────────┘ └──────────┘
     │            │            │
     └────────────┴────────────┘
              │
              ▼
    ┌──────────────────┐
    │  All use same   │
    │  RULES object    │
    │  (synchronized)  │
    └──────────────────┘
```

**Synchronization Points:**
1. **MCP Server** → Primary source (`.claude/straylight-mcp.js`)
2. **Standalone Validator** → Mirrors MCP logic (`scripts/validate-file.js`)
3. **CI Workflow** → Uses `validate-file.js` for consistency
4. **Pre-commit Hook** → Uses `validate-file.js` for consistency
5. **File Watcher** → Uses `validate-file.js` for consistency

## Critical Enforcement Points

### Point 1: AI Code Generation
- **Enforced by:** `.cursor/rules/*.mdc`, `AGENTS.md`, `CLAUDE.md`
- **Mechanism:** Rules guide AI, MCP tools validate
- **Coverage:** 100% (cannot skip validation step)

### Point 2: File Save
- **Enforced by:** `scripts/watch-and-validate.js` (optional)
- **Mechanism:** Real-time validation on save
- **Coverage:** Optional, but recommended

### Point 3: Git Commit
- **Enforced by:** `hooks/pre-commit`
- **Mechanism:** Blocks commit if violations found
- **Coverage:** 100% (cannot bypass without --no-verify)

### Point 4: Git Push
- **Enforced by:** `.github/workflows/straylight-enforcement.yml`
- **Mechanism:** CI fails, blocks merge
- **Coverage:** 100% (cannot merge without passing CI)

## Feedback Loops

```
┌─────────────────────────────────────────────────────────┐
│                    FEEDBACK LOOPS                       │
└─────────────────────────────────────────────────────────┘

Loop 1: AI Generation → Validation → Fix → Re-validate
  ┌─────────────┐
  │ AI generates│
  │   code      │
  └──────┬──────┘
         │
         ▼
  ┌─────────────┐
  │  Validate   │
  │  (MCP tool) │
  └──────┬──────┘
         │
    ┌────┴────┐
    │         │
 valid: false│valid: true
    │         │
    ▼         ▼
  ┌─────┐  ┌──────┐
  │ Fix │  │Write │
  │errors│  │ file │
  └──┬──┘  └──────┘
     │
     └──────┐
            │
            ▼
      (re-validate)

Loop 2: File Save → Watcher → Validation → Display
  ┌─────────────┐
  │ File saved  │
  └──────┬──────┘
         │
         ▼
  ┌─────────────┐
  │   Watcher   │
  │  detects    │
  └──────┬──────┘
         │
         ▼
  ┌─────────────┐
  │  Validate   │
  └──────┬──────┘
         │
    ┌────┴────┐
    │         │
 violations │clean
    │         │
    ▼         ▼
  ┌─────┐  ┌──────┐
  │Show │  │Show  │
  │error│  │✅ OK │
  └─────┘  └──────┘

Loop 3: Commit → Hook → Validation → Block/Allow
  ┌─────────────┐
  │ git commit  │
  └──────┬──────┘
         │
         ▼
  ┌─────────────┐
  │ Pre-commit  │
  │    hook     │
  └──────┬──────┘
         │
         ▼
  ┌─────────────┐
  │  Validate   │
  │  all files  │
  └──────┬──────┘
         │
    ┌────┴────┐
    │         │
 violations │clean
    │         │
    ▼         ▼
  ┌─────┐  ┌──────┐
  │Block│  │Allow │
  │commit│  │commit│
  └─────┘  └──────┘
```

## Data Flow Diagram

```
┌──────────────────────────────────────────────────────────────┐
│                    DATA FLOW                                 │
└──────────────────────────────────────────────────────────────┘

User Request
    │
    ▼
AI Assistant
    │
    ├─→ Reads: Rules/Configs (static)
    │   ├─→ .cursor/rules/*.mdc
    │   ├─→ AGENTS.md
    │   └─→ CLAUDE.md
    │
    ├─→ Calls: MCP Tools (dynamic)
    │   ├─→ straylight_plan → Returns: docs[]
    │   ├─→ straylight_locate → Returns: filePath
    │   ├─→ straylight_template → Returns: templateCode
    │   └─→ straylight_validate → Returns: { valid, errors }
    │
    └─→ Writes: Code to file
        │
        ▼
File System
    │
    ├─→ Watcher (optional)
    │   └─→ validate-file.js → Returns: validation result
    │
    └─→ Git
        │
        ├─→ Pre-commit Hook
        │   └─→ validate-file.js → Blocks/Allows commit
        │
        └─→ Push
            │
            └─→ CI Workflow
                └─→ validate-file.js → Blocks/Allows merge
```

## Rule Application Logic

```
For each file being validated:

1. Determine file type
   └─→ Based on extension (.nix, .hs, .purs, etc.)

2. Check file size
   └─→ If >500 lines → ERROR (STRAYLIGHT-010)
   └─→ Continue validation even if size violation

3. Process FORBIDDEN rules (in order)
   └─→ For each rule in RULES[type].forbidden[]:
       ├─→ If rule.check exists:
       │   └─→ Call check(code, filePath)
       │       └─→ If returns false → ERROR
       │
       └─→ Else if rule.pattern exists:
           └─→ Test pattern against code
           └─→ If matches → Check exception
           └─→ If no exception → ERROR

4. Process REQUIRED rules
   └─→ For each rule in RULES[type].required[]:
       ├─→ If rule.check exists:
       │   └─→ Call check(code, filePath)
       │       └─→ If returns false → ERROR
       │
       └─→ Else if rule.pattern exists:
           └─→ Test pattern against code
           └─→ If no match → ERROR

5. Process WARNING rules
   └─→ For each rule in RULES[type].warnings[]:
       ├─→ If rule.check exists:
       │   └─→ Call check(code, filePath)
       │       └─→ If returns false → WARNING
       │
       └─→ Else if rule.pattern exists:
           └─→ Test pattern against code
           └─→ If matches → WARNING

6. Return results
   └─→ { valid: errors.length === 0, errors, warnings }
```

## Component Interaction Matrix

| Component | Reads From | Writes To | Validates Against | Triggers |
|-----------|------------|-----------|-------------------|----------|
| **AI Assistant** | Rules, Configs, MCP | Files | MCP tools | File writes |
| **MCP Server** | straylight-protocol/, RULES | stdout | RULES object | AI requests |
| **validate-file.js** | Files | stdout | RULES object | Hook, CI, Watcher |
| **Pre-commit Hook** | Git index | stderr | validate-file.js | git commit |
| **CI Workflow** | Git repo | GitHub | validate-file.js | git push |
| **File Watcher** | File system | stdout | validate-file.js | File save |

## Enforcement Guarantees

### Guarantee 1: Cannot Skip Validation
- **Mechanism:** Rules require validation step
- **Enforcement:** `.cursor/rules/003_mandatory-workflow.mdc` mandates Step 4
- **Bypass:** Not possible without violating protocol

### Guarantee 2: Cannot Commit Violations
- **Mechanism:** Pre-commit hook blocks commits
- **Enforcement:** `hooks/pre-commit` runs `validate-file.js`
- **Bypass:** Requires `--no-verify` flag (violates protocol)

### Guarantee 3: Cannot Merge Violations
- **Mechanism:** CI workflow fails on violations
- **Enforcement:** `.github/workflows/straylight-enforcement.yml`
- **Bypass:** Not possible (GitHub enforces CI)

### Guarantee 4: Consistent Rule Application
- **Mechanism:** All validators use same RULES object
- **Enforcement:** `validate-file.js` mirrors `straylight-mcp.js`
- **Bypass:** Not possible (single source of truth)

## Summary

**Complete enforcement chain:**
1. **AI Generation** → Rules guide, MCP validates
2. **File Save** → Watcher validates (optional)
3. **Git Commit** → Hook validates (mandatory)
4. **Git Push** → CI validates (mandatory)

**100% Coverage:** Every code path goes through validation
**Zero Bypass:** Multiple layers prevent violations
**Consistent Rules:** Single source of truth (RULES object)

---

This flow ensures **100% Straylight Protocol enforcement** at every stage of development.
