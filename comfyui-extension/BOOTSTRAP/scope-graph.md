# Straylight Protocol Scope Graph

**Complete dependency and interaction graph**

## Component Scope Graph

```
┌─────────────────────────────────────────────────────────────────────┐
│                        USER REQUEST                                  │
└────────────────────────────┬────────────────────────────────────────┘
                             │
                             ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    AI ASSISTANT LAYER                               │
│                                                                     │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │ Configuration Files (Read-only)                              │  │
│  │                                                              │  │
│  │  .cursor/rules/001_straylight-protocol.mdc ────────┐            │  │
│  │  .cursor/rules/002_validation-required.mdc ────┤            │  │
│  │  .cursor/rules/003_mandatory-workflow.mdc ─────┤            │  │
│  │  AGENTS.md ────────────────────────────────────┤            │  │
│  │  CLAUDE.md ────────────────────────────────────┤            │  │
│  │  .cursorrules ─────────────────────────────────┤            │  │
│  │  .clinerules ──────────────────────────────────┤            │  │
│  │  .windsurfrules ───────────────────────────────┤            │  │
│  │                                                  │            │  │
│  └──────────────────────────────────────────────────┼────────────┘  │
│                                                     │               │
│  ┌──────────────────────────────────────────────────┼────────────┐  │
│  │ MCP Client                                        │            │  │
│  │  └─→ .claude/settings.json ─────────────────────┘            │  │
│  └──────────────────────────────────────────────────────────────┘  │
└────────────────────────────┬────────────────────────────────────────┘
                             │
                             ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      MCP SERVER LAYER                               │
│                                                                     │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │ .claude/straylight-mcp.js                                        │  │
│  │                                                              │  │
│  │  Tools Provided:                                            │  │
│  │  ├─→ straylight_validate(code, type)                             │  │
│  │  ├─→ straylight_template(type, name)                              │  │
│  │  ├─→ straylight_locate(type, name)                               │  │
│  │  ├─→ straylight_plan(task)                                       │  │
│  │  ├─→ straylight_examples(type)                                    │  │
│  │  └─→ straylight_search(query)                                     │  │
│  │                                                              │  │
│  │  Rule Engine:                                                │  │
│  │  └─→ RULES Object (56+ rules) ────────────────┐            │  │
│  │      ├─→ nix.forbidden[] (10 rules)            │            │  │
│  │      ├─→ nix.warnings[] (7 rules)              │            │  │
│  │      ├─→ nix.required[] (2 rules)              │            │  │
│  │      ├─→ purescript.* (6 rules)                │            │  │
│  │      ├─→ haskell.* (1 rule)                    │            │  │
│  │      ├─→ lean4.* (4 rules)                     │            │  │
│  │      ├─→ bash.* (6 rules)                      │            │  │
│  │      ├─→ cpp23.* (2 rules)                     │            │  │
│  │      ├─→ literate.* (7 rules)                  │            │  │
│  │      └─→ File size (1 rule)                    │            │  │
│  │                                                  │            │  │
│  │  Documentation Access:                          │            │  │
│  │  ├─→ straylight-protocol/docs/rfc/*.md ─────────────┤            │  │
│  │  ├─→ straylight-core/CONTRIBUTING.md ───────────────┤            │  │
│  │  └─→ skill/straylight-script/SKILL.md ──────────────┤            │  │
│  └──────────────────────────────────────────────────┼──────────┘  │
│                                                       │              │
└───────────────────────────────────────────────────────┼──────────────┘
                                                        │
                                                        ▼
┌─────────────────────────────────────────────────────────────────────┐
│                    VALIDATION LAYER                                 │
│                                                                     │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │ scripts/validate-file.js                                     │  │
│  │                                                              │  │
│  │  ┌──────────────────────────────────────────────────────┐  │  │
│  │  │ Mirrors MCP Server RULES Logic                       │  │  │
│  │  │                                                       │  │  │
│  │  │ Used by:                                             │  │  │
│  │  │ ├─→ hooks/pre-commit                                 │  │  │
│  │  │ ├─→ .github/workflows/straylight-enforcement.yml          │  │  │
│  │  │ └─→ scripts/watch-and-validate.js                    │  │  │
│  │  └──────────────────────────────────────────────────────┘  │  │
│  │                                                              │  │
│  │  ┌──────────────────────────────────────────────────────┐  │  │
│  │  │ scripts/test-all-violations.js                      │  │  │
│  │  │                                                      │  │  │
│  │  │ Tests: 44 test cases                                │  │  │
│  │  │ Uses: scripts/validate-file.js                      │  │  │
│  │  └──────────────────────────────────────────────────────┘  │  │
│  │                                                              │  │
│  │  ┌──────────────────────────────────────────────────────┐  │  │
│  │  │ scripts/watch-and-validate.js                       │  │  │
│  │  │                                                      │  │  │
│  │  │ Watches: straylight-core/                                │  │  │
│  │  │ Uses: scripts/validate-file.js                      │  │  │
│  │  └──────────────────────────────────────────────────────┘  │  │
│  └──────────────────────────────────────────────────────────────┘  │
└────────────────────────────┬────────────────────────────────────────┘
                             │
                             ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      GIT LAYER                                       │
│                                                                     │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │ hooks/pre-commit                                            │  │
│  │                                                              │  │
│  │  Trigger: git commit                                        │  │
│  │  ├─→ Checks: git diff --cached                              │  │
│  │  ├─→ Filters: .nix, .hs, .purs, .sh, etc.                   │  │
│  │  ├─→ Runs: nix flake check (if available)                   │  │
│  │  └─→ Runs: scripts/validate-file.js (for each file)         │  │
│  │      └─→ Blocks commit if violations found                   │  │
│  └──────────────────────────────────────────────────────────────┘  │
└────────────────────────────┬────────────────────────────────────────┘
                             │
                             ▼
┌─────────────────────────────────────────────────────────────────────┐
│                      CI/CD LAYER                                    │
│                                                                     │
│  ┌──────────────────────────────────────────────────────────────┐  │
│  │ .github/workflows/straylight-enforcement.yml                       │  │
│  │                                                              │  │
│  │  Trigger: PR or push to main/master                         │  │
│  │  ├─→ Step 1: Checkout code                                  │  │
│  │  ├─→ Step 2: Setup Nix                                       │  │
│  │  ├─→ Step 3: Setup Node.js                                   │  │
│  │  ├─→ Step 4: Validate MCP server syntax                      │  │
│  │  ├─→ Step 5: Run Nix lint                                    │  │
│  │  ├─→ Step 6: Check protocol violations (grep)                │  │
│  │  ├─→ Step 7: Validate changed files                         │  │
│  │  │   └─→ Uses: scripts/validate-file.js                      │  │
│  │  ├─→ Step 8: Check file sizes                               │  │
│  │  └─→ Step 9: Check literate programming                      │  │
│  │      └─→ Blocks merge if violations found                    │  │
│  │                                                              │  │
│  │  .github/workflows/cd.yml                                    │  │
│  │  └─→ Includes: Straylight Protocol validation step               │  │
│  └──────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────┘
```

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────────┐
│                    SOURCE OF TRUTH                               │
│                                                                 │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │ RULES Object                                             │  │
│  │ Location: .claude/straylight-mcp.js                          │  │
│  │                                                           │  │
│  │ Contains: 56+ validation rules                           │  │
│  │                                                           │  │
│  │ Dependencies:                                            │  │
│  │ └─→ None (primary source)                                │  │
│  │                                                           │  │
│  │ Used by:                                                 │  │
│  │ ├─→ MCP Server (straylight-mcp.js)                            │  │
│  │ └─→ Standalone Validator (validate-file.js)              │  │
│  └───────────────────────────────────────────────────────────┘  │
└────────────────────────────┬────────────────────────────────────┘
                             │
        ┌────────────────────┼────────────────────┐
        │                    │                    │
        ▼                    ▼                    ▼
┌───────────────┐  ┌──────────────────┐  ┌──────────────────┐
│   MCP Server  │  │ Standalone       │  │   Test Suite     │
│               │  │ Validator        │  │                   │
│ straylight-mcp.js  │  │                  │  │ test-all-        │
│               │  │ validate-file.js  │  │ violations.js     │
│               │  │                  │  │                   │
│ Provides:     │  │ Used by:         │  │ Uses:             │
│ - Tools       │  │ - Pre-commit     │  │ - validate-file.js│
│ - Validation  │  │ - CI Workflow    │  │                   │
│               │  │ - File Watcher   │  │ Tests:            │
│               │  │                  │  │ - 44 test cases   │
└───────────────┘  └────────┬─────────┘  └───────────────────┘
                            │
        ┌───────────────────┼───────────────────┐
        │                   │                   │
        ▼                   ▼                   ▼
┌──────────────┐  ┌──────────────────┐  ┌──────────────┐
│ Pre-commit   │  │ CI Workflow      │  │ File        │
│ Hook         │  │                  │  │ Watcher      │
│              │  │ straylight-           │  │              │
│ hooks/       │  │ enforcement.yml  │  │ watch-and-   │
│ pre-commit   │  │                  │  │ validate.js  │
│              │  │                  │  │              │
│ Triggered:   │  │ Triggered:      │  │ Triggered:   │
│ git commit   │  │ git push        │  │ File save    │
│              │  │                 │  │              │
│ Blocks:      │  │ Blocks:         │  │ Shows:       │
│ Commit       │  │ Merge           │  │ Errors       │
└──────────────┘  └──────────────────┘  └──────────────┘
```

## Configuration Dependencies

```
┌─────────────────────────────────────────────────────────────────┐
│                    CONFIGURATION FILES                           │
│                                                                 │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │ AI Assistant Rules                                        │  │
│  │                                                           │  │
│  │ .cursor/rules/001_straylight-protocol.mdc                     │  │
│  │   └─→ Defines: Main protocol rules                       │  │
│  │   └─→ Used by: AI Assistant (Cursor)                      │  │
│  │                                                           │  │
│  │ .cursor/rules/002_validation-required.mdc                │  │
│  │   └─→ Defines: Validation enforcement                    │  │
│  │   └─→ Used by: AI Assistant (Cursor)                     │  │
│  │                                                           │  │
│  │ .cursor/rules/003_mandatory-workflow.mdc                 │  │
│  │   └─→ Defines: Plan → Locate → Template → Validate       │  │
│  │   └─→ Used by: AI Assistant (Cursor)                     │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                 │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │ Agent Configuration                                        │  │
│  │                                                           │  │
│  │ AGENTS.md                                                 │  │
│  │   └─→ Defines: Mandatory workflow steps                   │  │
│  │   └─→ Used by: AI Assistant (all platforms)              │  │
│  │                                                           │  │
│  │ CLAUDE.md                                                 │  │
│  │   └─→ Defines: Claude Code specific instructions         │  │
│  │   └─→ Used by: AI Assistant (Claude Code)               │  │
│  │                                                           │  │
│  │ .cursorrules                                              │  │
│  │   └─→ Defines: Legacy Cursor rules                       │  │
│  │   └─→ Used by: AI Assistant (Cursor)                    │  │
│  │                                                           │  │
│  │ .clinerules                                               │  │
│  │   └─→ Defines: Cline rules                               │  │
│  │   └─→ Used by: AI Assistant (Cline)                      │  │
│  │                                                           │  │
│  │ .windsurfrules                                            │  │
│  │   └─→ Defines: Windsurf rules                            │  │
│  │   └─→ Used by: AI Assistant (Windsurf)                   │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                 │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │ MCP Configuration                                          │  │
│  │                                                           │  │
│  │ .claude/settings.json                                     │  │
│  │   └─→ Defines: MCP server connection                      │  │
│  │   └─→ Used by: AI Assistant (Claude Code)                │  │
│  │                                                           │  │
│  │ .claude/straylight-mcp.js                                      │  │
│  │   └─→ Defines: MCP server implementation                 │  │
│  │   └─→ Used by: MCP Protocol                              │  │
│  └───────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

## Documentation Dependencies

```
┌─────────────────────────────────────────────────────────────────┐
│                    DOCUMENTATION SOURCES                         │
│                                                                 │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │ Protocol Documentation                                     │  │
│  │                                                           │  │
│  │ straylight-protocol/docs/rfc/*.md                             │  │
│  │   ├─→ RFC ℵ-001: Standard Nix                            │  │
│  │   ├─→ RFC ℵ-002: Safe Bash                               │  │
│  │   ├─→ RFC ℵ-003: PureScript Standards                   │  │
│  │   ├─→ RFC ℵ-004: Script Imports                          │  │
│  │   ├─→ RFC ℵ-005: Lean4 Proofs                            │  │
│  │   ├─→ RFC ℵ-006: C++23 Standards                         │  │
│  │   ├─→ RFC ℵ-007: File Size Limits                        │  │
│  │   ├─→ RFC ℵ-008: Module Structure                        │  │
│  │   ├─→ RFC ℵ-009: Documentation Standards                 │  │
│  │   ├─→ RFC ℵ-010: File Size Enforcement                   │  │
│  │   └─→ RFC ℵ-011: Literate Programming                    │  │
│  │                                                           │  │
│  │ Used by:                                                  │  │
│  │ └─→ MCP Server (straylight_plan, straylight_search tools)           │  │
│  └───────────────────────────────────────────────────────────┘  │
│                                                                 │
│  ┌───────────────────────────────────────────────────────────┐  │
│  │ Project Documentation                                      │  │
│  │                                                           │  │
│  │ straylight-core/CONTRIBUTING.md                                │  │
│  │   └─→ Defines: Decision tree for file placement           │  │
│  │   └─→ Used by: MCP Server (straylight_locate tool)            │  │
│  │                                                           │  │
│  │ skill/straylight-script/SKILL.md                               │  │
│  │   └─→ Defines: Script creation guidelines                │  │
│  │   └─→ Used by: MCP Server (straylight_template tool)          │  │
│  └───────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

## Data Flow Scope

```
┌─────────────────────────────────────────────────────────────────┐
│                    DATA FLOW SCOPE                              │
│                                                                 │
│  Input Sources:                                                 │
│  ├─→ User Request (text)                                       │
│  ├─→ Code Files (straylight-core/**)                                │
│  ├─→ Configuration Files (.cursor/rules/*, AGENTS.md, etc.)    │
│  └─→ Documentation (straylight-protocol/docs/rfc/*.md)               │
│                                                                 │
│  Processing:                                                    │
│  ├─→ AI Assistant (interprets request, applies rules)           │
│  ├─→ MCP Server (validates, templates, locates)                 │
│  ├─→ Validation Scripts (check rules)                           │
│  └─→ Git Hooks (pre-commit validation)                          │
│                                                                 │
│  Output Destinations:                                           │
│  ├─→ File System (generated code)                              │
│  ├─→ Git Repository (committed code)                           │
│  ├─→ CI/CD System (validation results)                          │
│  └─→ User Interface (validation feedback)                      │
│                                                                 │
│  Validation Points:                                             │
│  ├─→ AI Generation (MCP tool)                                   │
│  ├─→ File Save (Watcher - optional)                             │
│  ├─→ Git Commit (Pre-commit hook)                               │
│  └─→ Git Push (CI workflow)                                     │
└─────────────────────────────────────────────────────────────────┘
```

## Rule Application Scope

```
┌─────────────────────────────────────────────────────────────────┐
│                    RULE APPLICATION SCOPE                       │
│                                                                 │
│  Language-Specific Rules:                                       │
│  ├─→ Nix (19 rules: 10 forbidden, 7 warnings, 2 required)       │
│  ├─→ PureScript (6 rules: 5 forbidden, 1 required)              │
│  ├─→ Haskell (1 rule: 1 required)                               │
│  ├─→ Lean4 (4 rules: 4 forbidden)                              │
│  ├─→ Bash (6 rules: 6 forbidden)                                │
│  └─→ C++23 (2 rules: 2 forbidden)                              │
│                                                                 │
│  Cross-Language Rules:                                          │
│  ├─→ File Size (1 rule: STRAYLIGHT-010)                              │
│  └─→ Literate Programming (7 rules: STRAYLIGHT-011-E001 to E007)     │
│                                                                 │
│  Rule Types:                                                    │
│  ├─→ Pattern Matching (regex)                                    │
│  ├─→ Custom Check Functions (complex logic)                     │
│  ├─→ File Path Analysis (context-aware)                          │
│  └─→ Exception Handling (specific cases)                         │
│                                                                 │
│  Application Points:                                            │
│  ├─→ MCP Server (straylight_validate tool)                            │
│  ├─→ Standalone Validator (validate-file.js)                    │
│  ├─→ Pre-commit Hook (via validate-file.js)                      │
│  ├─→ CI Workflow (via validate-file.js)                         │
│  └─→ File Watcher (via validate-file.js)                        │
└─────────────────────────────────────────────────────────────────┘
```

## Summary

**Complete Scope:**
- **4 Enforcement Layers:** AI Generation, File System, Git, CI/CD
- **56+ Validation Rules:** Covering 7 languages + cross-language rules
- **6 MCP Tools:** plan, locate, template, validate, examples, search
- **3 Validation Scripts:** validate-file.js, test-all-violations.js, watch-and-validate.js
- **2 Git Hooks:** pre-commit (primary), others optional
- **2 CI/CD Workflows:** straylight-enforcement.yml, cd.yml
- **8 Configuration Files:** Rules, agents, configs for all platforms
- **11+ RFC Documents:** Complete protocol specification

**100% Coverage:** Every code path validated at multiple points
**Zero Bypass:** Multiple layers prevent violations
**Single Source of Truth:** RULES object synchronized across all validators
