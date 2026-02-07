# Bootstrap Checklist

Use this checklist to verify everything is set up correctly.

## Files Included (27 files)

### Core Infrastructure
- [x] `.claude/straylight-mcp.js` - MCP server (1523 lines, all 56+ rules)
- [x] `.claude/settings.json` - Claude Code MCP configuration
- [x] `.claude/README.md` - MCP server documentation

### Cursor IDE Rules
- [x] `.cursor/rules/001_straylight-protocol.mdc` - Main protocol rules
- [x] `.cursor/rules/002_validation-required.mdc` - Validation requirements
- [x] `.cursor/rules/003_mandatory-workflow.mdc` - Mandatory workflow

### Git Hooks
- [x] `hooks/pre-commit` - Pre-commit validation hook

### Validation Scripts
- [x] `scripts/validate-file.js` - Standalone file validator
- [x] `scripts/test-all-violations.js` - Comprehensive test suite
- [x] `scripts/watch-and-validate.js` - Real-time file watcher
- [x] `scripts/setup-claude-mcp.js` - Cross-platform MCP setup
- [x] `scripts/setup-claude-mcp.sh` - Linux/Mac MCP setup
- [x] `scripts/setup-claude-mcp.ps1` - Windows MCP setup

### CI/CD Workflows
- [x] `.github/workflows/straylight-enforcement.yml` - CI enforcement
- [x] `.github/workflows/cd.yml` - Continuous deployment

### Agent Configurations
- [x] `AGENTS.md` - Complete agent instructions
- [x] `CLAUDE.md` - Claude Code instructions
- [x] `opencode.json` - OpenCode configuration
- [x] `.cursorrules` - Cursor rules (legacy)
- [x] `.clinerules` - Cline rules
- [x] `.windsurfrules` - Windsurf rules

### Skills & Documentation
- [x] `skill/straylight-script/SKILL.md` - Straylight.Script skill guide

### Documentation
- [x] `README.md` - Complete documentation
- [x] `START_HERE.md` - Quick start guide
- [x] `CHECKLIST.md` - This file
- [x] `ENFORCEMENT_FLOW.md` - Information flow documentation
- [x] `ENFORCEMENT_FLOWCHART.md` - Visual flowcharts
- [x] `SCOPE_GRAPH.md` - Dependency graph
- [x] `PROJECT_STRUCTURE.md` - Project structure assumptions

### Git Configuration
- [x] `.gitignore` - Git ignore patterns

### Dependencies
- [x] `package.json` - Node.js dependencies

## Setup Steps

### 1. Copy Files
- [ ] Copy all files from `BOOTSTRAP/` to project root
- [ ] Verify all 25 files are present

### 2. Install Dependencies
- [ ] Run `npm install`
- [ ] Verify `node_modules/@modelcontextprotocol/sdk` exists

### 3. Set Up Git Hook
- [ ] Make `hooks/pre-commit` executable (Linux/Mac)
- [ ] Link hook: `ln -sf ../../hooks/pre-commit .git/hooks/pre-commit`
- [ ] Verify: `ls -l .git/hooks/pre-commit` shows link

### 4. Configure AI Assistants (Optional)

**Claude Code:**
- [ ] Run `npm run straylight:setup-claude` or `node scripts/setup-claude-mcp.js`
- [ ] Restart Claude Code
- [ ] Verify MCP tools are available

**OpenCode:**
- [ ] Copy `opencode.json` to `~/.config/opencode/opencode.json`
- [ ] Restart OpenCode
- [ ] Verify MCP server is configured

**Cursor:**
- [ ] Rules are automatically loaded from `.cursor/rules/`
- [ ] No additional setup needed

### 5. Test Everything
- [ ] Test validation: `node scripts/validate-file.js scripts/validate-file.js`
- [ ] Test hook: Create violation, try to commit (should fail)
- [ ] Test MCP: Check Claude Code MCP panel (if configured)
- [ ] Test CI: Push branch, check GitHub Actions (if using GitHub)

## Verification Commands

```bash
# Check all files exist
find . -name "*.js" -o -name "*.mdc" -o -name "*.md" -o -name "*.yml" | grep -E "(claude|cursor|hooks|scripts|github|skill)" | sort

# Test validation script
node scripts/validate-file.js scripts/validate-file.js

# Test hook (should fail)
echo 'with lib;' > /tmp/test.nix
git add /tmp/test.nix
git commit -m "test"  # Should be blocked

# Check hook is linked
ls -l .git/hooks/pre-commit

# Check dependencies
npm list @modelcontextprotocol/sdk
```

## What Gets Enforced

### Nix (15+ rules)
- ❌ `with lib;` (WSN-E001)
- ❌ `rec {` in derivations (WSN-E002)
- ❌ camelCase (WSN-E003)
- ❌ Missing `_class` in modules (WSN-E004)
- ❌ `default.nix` in packages (WSN-E005)
- ❌ Heredocs (WSN-E006)
- ❌ `if/then/else` in module config (WSN-E007)
- ❌ Import from derivation (WSN-E008)
- ❌ Per-flake nixpkgs config (WSN-E010)
- ❌ `nixpkgs.config.*` in NixOS (WSN-E011)
- ⚠️ Missing `meta` (WSN-W004)
- ⚠️ Missing `meta.description` (WSN-W005)
- ⚠️ Missing `meta.license` (WSN-W006)
- ⚠️ Missing `mainProgram` (WSN-W007)
- ⚠️ `rec` anywhere (WSN-W001)
- ⚠️ `if/then/else` in modules (WSN-W002)
- ⚠️ Long inline strings (WSN-W003)

### PureScript (5 rules)
- ❌ `undefined` (STRAYLIGHT-007)
- ❌ `null` (STRAYLIGHT-007)
- ❌ `unsafeCoerce` (STRAYLIGHT-007)
- ❌ `unsafePartial` (STRAYLIGHT-007)
- ❌ `unsafePerformEffect` (STRAYLIGHT-007)
- ✅ Scripts must import (STRAYLIGHT-004)

### Haskell (1 rule)
- ✅ Scripts must import (STRAYLIGHT-004)

### Lean4 (4 rules)
- ❌ `sorry` (STRAYLIGHT-009)
- ❌ `axiom` (STRAYLIGHT-009)
- ❌ `admit` (STRAYLIGHT-009)
- ❌ `unsafe` (STRAYLIGHT-009)

### Bash (6 rules)
- ❌ `if` statements (STRAYLIGHT-006)
- ❌ `case` statements (STRAYLIGHT-006)
- ❌ `for` loops (STRAYLIGHT-006)
- ❌ `while` loops (STRAYLIGHT-006)
- ❌ Variable assignments (STRAYLIGHT-006)
- ❌ Command substitution (STRAYLIGHT-006)

### C++23 (2 rules)
- ❌ `nullptr` without handling (STRAYLIGHT-011-E006)
- ❌ Raw `new`/`delete` (STRAYLIGHT-011-E007)

### Literate Programming (7 rules)
- ❌ Code blocks without annotations (STRAYLIGHT-011-E001)
- ❌ Duplicate chunk names (STRAYLIGHT-011-E002)
- ❌ Undefined chunk references (STRAYLIGHT-011-E003)
- ❌ Circular dependencies (STRAYLIGHT-011-E004)
- ❌ Invalid `@target` values (STRAYLIGHT-011-E005)
- ❌ Code blocks >500 lines (STRAYLIGHT-010-BLOCK)

### File Size (1 rule)
- ❌ Files >500 lines (STRAYLIGHT-010)

### CMake (1 rule)
- ❌ CMake usage (STRAYLIGHT-003)

**Total: 44+ rules enforced**

## Enforcement Mechanisms

1. ✅ **Pre-commit Hook** - Blocks commits with violations
2. ✅ **CI Pipeline** - Validates on PR/push
3. ✅ **MCP Server** - AI assistant integration
4. ✅ **Cursor Rules** - IDE guidance
5. ✅ **Standalone Validator** - Manual validation
6. ✅ **File Watcher** - Real-time validation
7. ✅ **Agent Configs** - AI instructions

## Success Criteria

✅ All 24 files copied  
✅ `npm install` completed  
✅ Git hook linked and executable  
✅ Validation script works  
✅ Hook blocks violations  
✅ MCP server configured (if using Claude Code)  
✅ CI workflow enabled (if using GitHub)  

---

**🎉 If all checkboxes are checked, you're ready to code with full Straylight Protocol enforcement!**
