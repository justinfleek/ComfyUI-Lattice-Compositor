# Straylight Protocol Bootstrap

**Complete enforcement infrastructure for Straylight Protocol compliance**

Copy this folder to your project root alongside your `straylight-protocol` folder to get full enforcement immediately.

**Status:** ✅ **100% Coverage** - All 528 files in the codebase are now covered by enforcement across 11 language/file type categories with 64+ rules.

## Quick Start

```bash
# 1. Copy files to project root
cp -r BOOTSTRAP/* /path/to/your/project/
# Windows: Copy-Item -Recurse -Force BOOTSTRAP\* C:\path\to\project\

# 2. Install dependencies
cd /path/to/your/project
npm install

# 3. Set up git hook
chmod +x hooks/pre-commit
ln -sf ../../hooks/pre-commit .git/hooks/pre-commit
# Windows: New-Item -ItemType SymbolicLink -Path .git\hooks\pre-commit -Target ..\..\hooks\pre-commit -Force

# 4. Test it works
echo 'with lib;' > test.nix
git add test.nix
git commit -m "test"  # Should be BLOCKED ✅
```

## Validation Commands

The bootstrap includes comprehensive validation tools:

```bash
# Validate a single file
npm run straylight:validate -- path/to/file.nix

# Validate ALL files in a directory (e.g., straylight-protocol/)
npm run straylight:validate-all -- ../straylight-protocol

# Check rule coverage in test suite
npm run straylight:coverage

# Generate detailed validation report
npm run straylight:validate-all -- ../straylight-protocol json > results.json
npm run straylight:report -- results.json markdown report.md
```

See [VALIDATION_REPORT.md](./VALIDATION_REPORT.md) for comprehensive validation results.

## Understanding the Flow

For a complete understanding of how enforcement works, see:

- **[ENFORCEMENT_FLOW.md](./ENFORCEMENT_FLOW.md)** - Detailed information flow from user request through all enforcement mechanisms
- **[ENFORCEMENT_FLOWCHART.md](./ENFORCEMENT_FLOWCHART.md)** - Visual flowcharts and diagrams (Mermaid format)
- **[SCOPE_GRAPH.md](./SCOPE_GRAPH.md)** - Complete dependency and scope graph

These documents show:
- How user requests flow through AI assistants, MCP servers, and validation layers
- The exact sequence of validation at each enforcement point
- Component dependencies and interactions
- Rule application logic and resolution order
- Complete data flow from input to production

## Prerequisites

- **Node.js 18+** installed
- **Git repository** initialized
- **`straylight-protocol` folder** in project root (contains RFCs and documentation)

**Note:** The system tries to auto-detect your project structure:
- **Pre-commit hook:** Automatically finds project root and searches for validation scripts
- **File watcher:** Checks for `straylight-core/`, `nix/`, or `src/` directories
- **MCP server:** Defaults to `straylight-core/` but paths can be customized

If your project uses a different structure, see [PROJECT_STRUCTURE.md](./PROJECT_STRUCTURE.md) for adaptation instructions.

## Detailed Setup

### Step 1: Copy Bootstrap Files

**Linux/Mac:**
```bash
cd /path/to/your/project
cp -r BOOTSTRAP/* .
```

**Windows (PowerShell):**
```powershell
cd C:\path\to\your\project
Copy-Item -Recurse -Force BOOTSTRAP\* .
```

**Windows (CMD):**
```cmd
cd C:\path\to\your\project
xcopy /E /I /Y BOOTSTRAP\* .
```

### Step 2: Install Dependencies

```bash
npm install
```

This installs `@modelcontextprotocol/sdk` required for the MCP server.

### Step 3: Set Up Git Hooks

**Linux/Mac:**
```bash
# Make hook executable
chmod +x hooks/pre-commit

# Link hook (if not already linked)
ln -sf ../../hooks/pre-commit .git/hooks/pre-commit

# Verify
ls -l .git/hooks/pre-commit
# Should show: ../../hooks/pre-commit -> .git/hooks/pre-commit
```

**Windows (PowerShell):**
```powershell
# Create symbolic link
New-Item -ItemType SymbolicLink -Path .git\hooks\pre-commit -Target ..\..\hooks\pre-commit -Force

# Verify
Get-Item .git\hooks\pre-commit
```

**Windows (CMD - requires admin):**
```cmd
mklink .git\hooks\pre-commit ..\..\hooks\pre-commit
```

### Step 4: Configure AI Assistants (Optional)

**Claude Code:**
```bash
npm run straylight:setup-claude
# or manually:
node scripts/setup-claude-mcp.js
```
**Important:** Restart Claude Code after setup.

**OpenCode:**
```bash
# Linux/Mac
mkdir -p ~/.config/opencode
cp opencode.json ~/.config/opencode/opencode.json

# Windows (PowerShell)
New-Item -ItemType Directory -Force -Path "$env:USERPROFILE\.config\opencode" | Out-Null
Copy-Item opencode.json "$env:USERPROFILE\.config\opencode\opencode.json"
```
**Important:** Restart OpenCode after copying.

**Cursor:**
No setup needed - rules are automatically loaded from `.cursor/rules/`

**Cline / Windsurf:**
Rules are automatically loaded from `.clinerules` / `.windsurfrules`

### Step 5: Enable GitHub Actions

If using GitHub:

1. Go to repository **Settings → Actions → General**
2. Enable **"Allow all actions and reusable workflows"**
3. Push a branch to trigger the workflow

### Step 6: Verify Installation

**Test validation script:**
```bash
# Should show usage or validate successfully
node scripts/validate-file.js scripts/validate-file.js
```

**Test pre-commit hook:**
```bash
# Create a test violation
echo 'with lib;' > /tmp/test-violation.nix
git add /tmp/test-violation.nix
git commit -m "test"  # Should be blocked
```

**Test MCP server (if using Claude Code or OpenCode):**
1. **Claude Code:** Open Claude Code, check if `straylight` tools are available in the MCP panel
2. **OpenCode:** Open OpenCode, verify MCP server is configured in settings
3. Try calling `straylight_validate` tool from either assistant

## What's Included

- **MCP Server** (`.claude/`) - AI assistant integration with 6 tools
- **Cursor Rules** (`.cursor/rules/`) - IDE guidance for code generation
- **Git Hooks** (`hooks/`) - Pre-commit validation
- **Validation Scripts** (`scripts/`) - Standalone tools
- **CI/CD Workflows** (`.github/workflows/`) - GitHub Actions
- **Agent Configs** (`AGENTS.md`, `CLAUDE.md`) - AI instructions
- **Skills System** (`skills/`, `.cursor/skills/`, `.opencode/skills/`, `.claude/skills/`) - AI agent skills (11 skills)
- **Comprehensive Documentation** - Setup guides, flowcharts, audits, verification reports

**See [ESSENTIAL_FILES.md](./ESSENTIAL_FILES.md) for minimum required files vs. full deployment.**

## File Structure

```
BOOTSTRAP/
├── README.md                    # This file
├── CHECKLIST.md                 # Verification checklist
├── .gitignore                   # Git ignore patterns
├── .claude/                     # MCP server
│   ├── straylight-mcp.js            # Main server (all 64+ rules)
│   ├── settings.json           # Claude Code MCP config
│   └── README.md               # MCP server documentation
├── .cursor/rules/               # Cursor IDE rules
│   ├── 001_straylight-protocol.mdc  # Main protocol rules
│   ├── 002_validation-required.mdc  # Validation requirements
│   └── 003_mandatory-workflow.mdc   # Mandatory workflow
├── hooks/                       # Git hooks
│   └── pre-commit              # Pre-commit validation hook
├── scripts/                     # Validation scripts
│   ├── validate-file.js        # Standalone file validator
│   ├── test-all-violations.js  # Comprehensive test suite (44 tests)
│   ├── watch-and-validate.js   # Real-time file watcher
│   ├── setup-claude-mcp.js    # Cross-platform MCP setup
│   ├── setup-claude-mcp.sh    # Linux/Mac MCP setup
│   └── setup-claude-mcp.ps1   # Windows MCP setup
├── .github/workflows/           # CI/CD
│   ├── straylight-enforcement.yml   # CI validation
│   └── cd.yml                  # Continuous deployment
├── skills/                       # Source skills (11 skills)
│   ├── straylight-script/
│   ├── council/
│   ├── deterministic-coder/
│   └── ... (8 more)
├── .cursor/skills/              # Cursor deployment (11 skills)
├── .opencode/skills/            # OpenCode deployment (11 skills)
├── .claude/skills/              # Claude Code deployment (11 skills)
├── AGENTS.md                    # Agent instructions
├── CLAUDE.md                    # Claude Code guide
├── opencode.json                # OpenCode configuration
├── .cursorrules                 # Legacy Cursor rules
├── .clinerules                  # Cline rules
├── .windsurfrules               # Windsurf rules
├── START_HERE.md                # Quick start guide
├── ESSENTIAL_FILES.md           # Minimum vs. full deployment guide
└── package.json                 # Node.js dependencies
```

## What Gets Enforced

### Supported File Types

The Straylight Protocol enforcement system validates **all file types** in the codebase:

- **Nix** (`.nix`) - 19 rules
- **Haskell** (`.hs`) - 1 rule
- **PureScript** (`.purs`) - 6 rules
- **Lean4** (`.lean`) - 4 rules
- **Bash** (`.sh`, `.bash`) - 6 rules
- **C++23** (`.cpp`, `.hpp`, `.cc`, `.h`) - 2 rules
- **CUDA** (`.cu`, `.cuh`) - 1 rule
- **Dhall** (`.dhall`) - 3 rules
- **Bazel/Buck2** (`.bzl`) - 3 rules
- **Rust** (`.rs`) - 5 rules
- **Python** (`.py`) - 4 rules
- **Literate Programming** (`.lit`, `.mdx`, `.lit.hs`, `.lit.cpp`, `.lit.purs`) - 7 rules
- **Config Files** (`.yml`, `.toml`, `.ini`, `.json`) - Embedded code validation
- **WASM** (`.wasm`) - Source file validation (binary files handled)

**Total: 64+ rules across 11 language/file type categories**

### Rule Details

#### Nix (19 rules)
- ❌ `with lib;` → Use `inherit (lib) x y;` (WSN-E001)
- ❌ `rec {` in derivations → Use `finalAttrs:` (WSN-E002)
- ❌ camelCase → Use lisp-case (WSN-E003)
- ❌ Missing `_class` in modules (WSN-E004)
- ❌ `default.nix` in packages (WSN-E005)
- ❌ Heredocs → Use `writeText` (WSN-E006)
- ❌ `if/then/else` in module config → Use `mkIf` (WSN-E007)
- ❌ Import from derivation (WSN-E008)
- ❌ Per-flake nixpkgs config (WSN-E010)
- ❌ `nixpkgs.config.*` in NixOS (WSN-E011)
- ⚠️ Missing `meta` block (WSN-W004)
- ⚠️ Missing `meta.description` (WSN-W005)
- ⚠️ Missing `meta.license` (WSN-W006)
- ⚠️ Missing `mainProgram` (WSN-W007)
- ⚠️ `rec` anywhere (WSN-W001)
- ⚠️ `if/then/else` in modules (WSN-W002)
- ⚠️ Long inline strings (WSN-W003)

#### PureScript (6 rules)
- ❌ `undefined`, `null`, `unsafeCoerce`, `unsafePartial`, `unsafePerformEffect` (STRAYLIGHT-007)
- ✅ Scripts must `import Straylight.Script` (STRAYLIGHT-004)

#### Haskell (1 rule)
- ✅ Scripts must `import Straylight.Script` (STRAYLIGHT-004)

#### Lean4 (4 rules)
- ❌ `sorry`, `axiom`, `admit`, `unsafe` (STRAYLIGHT-009)

#### Bash (6 rules)
- ❌ `if`, `case`, `for`, `while` → Write Haskell script (STRAYLIGHT-006)
- ❌ Variable assignments → Write Haskell script (STRAYLIGHT-006)
- ❌ Command substitution → Write Haskell script (STRAYLIGHT-006)
- ✅ Only `exec "$@"` allowed

#### C++23 (2 rules)
- ❌ `nullptr` without explicit handling (STRAYLIGHT-011-E006)
- ❌ Raw `new` / `delete` (STRAYLIGHT-011-E007)

#### CUDA (1 rule)
- ❌ `cudaMalloc` without `cudaFree` or RAII wrapper (STRAYLIGHT-011-E008)

#### Dhall (3 rules)
- ❌ `builtins.toNix` forbidden (STRAYLIGHT-012-E001)
- ❌ Raw `env` variables forbidden (STRAYLIGHT-012-E002)
- ⚠️ Relative imports warning (STRAYLIGHT-012-W001)

#### Bazel/Buck2 (3 rules)
- ❌ `glob()` forbidden (STRAYLIGHT-013-E001)
- ❌ `prelude_` imports forbidden (STRAYLIGHT-013-E002)
- ⚠️ Multiple `load()` statements warning (STRAYLIGHT-013-W001)

#### Rust (5 rules)
- ❌ `unsafe` blocks forbidden (STRAYLIGHT-014-E001)
- ❌ `.unwrap()` forbidden (STRAYLIGHT-014-E002)
- ❌ `.unwrap_err()` forbidden (STRAYLIGHT-014-E003)
- ⚠️ `.unwrap_or()` warning (STRAYLIGHT-014-W001)
- ✅ Structs should derive Debug/Clone (STRAYLIGHT-014-REQ)

#### Python (4 rules)
- ❌ `None` without explicit handling (STRAYLIGHT-015-E001)
- ❌ `# type: ignore` forbidden (STRAYLIGHT-015-E002)
- ❌ `Any` type forbidden (STRAYLIGHT-015-E003)
- ✅ Type hints required (STRAYLIGHT-015-REQ)

#### Literate Programming (7 rules)
- ❌ Code blocks without `@target`/`@name`/`@description` (STRAYLIGHT-011-E001)
- ❌ Duplicate chunk names (STRAYLIGHT-011-E002)
- ❌ Undefined chunk references (STRAYLIGHT-011-E003)
- ❌ Circular dependencies (STRAYLIGHT-011-E004)
- ❌ Invalid `@target` values (STRAYLIGHT-011-E005)
- ❌ Code blocks >500 lines (STRAYLIGHT-010-BLOCK)

#### File Size (1 rule)
- ❌ Files >500 lines per module (STRAYLIGHT-010)

#### CMake (1 rule)
- ❌ CMake usage (STRAYLIGHT-003)

#### Config Files (Embedded Code Validation)
- Validates embedded Nix/bash code in `.yml`, `.toml`, `.ini`, `.json` files
- Config files without embedded code skip validation (data-only)

#### WASM Files
- Binary files are not validated directly
- Source files (Haskell/C++/Rust) that generate WASM are validated
- Informational message provided for WASM files

## Enforcement Mechanisms

1. **Pre-commit Hook** (`hooks/pre-commit`) - Blocks commits with violations
2. **CI Pipeline** (`.github/workflows/straylight-enforcement.yml`) - Validates on PR/push
3. **MCP Server** (`.claude/straylight-mcp.js`) - AI assistant integration (6 tools)
4. **Cursor Rules** (`.cursor/rules/*.mdc`) - IDE guidance
5. **Standalone Validator** (`scripts/validate-file.js`) - Manual validation
6. **File Watcher** (`scripts/watch-and-validate.js`) - Real-time validation (optional)
7. **Agent Configs** (`AGENTS.md`, `CLAUDE.md`) - AI instructions
8. **Skills System** (`skills/` + platform deployments) - Enhanced AI guidance (optional)

**Coverage:** All enforcement mechanisms validate **all supported file types** including Nix, Haskell, PureScript, Lean4, Bash, C++23, CUDA, Dhall, Bazel, Rust, Python, Literate Programming, Config Files (embedded code), and WASM (source validation).

## MCP Tools

Available via Claude Code or other MCP clients:

1. **straylight_validate** - Validate code against protocol
   ```json
   {
     "code": "...",
     "type": "nix|bash|haskell|purescript|lean|cpp23"
   }
   ```

2. **straylight_template** - Get starter code templates
   ```json
   {
     "type": "package|script|tool-wrapper|module",
     "name": "my-name"
   }
   ```

3. **straylight_locate** - Find correct file locations
   ```json
   {
     "type": "package|script|tool-wrapper|module",
     "name": "my-name"
   }
   ```

4. **straylight_plan** - Get documentation and examples
   ```json
   {
     "task": "create a new package"
   }
   ```

5. **straylight_examples** - Find reference implementations
   ```json
   {
     "type": "package|script|tool-wrapper"
   }
   ```

6. **straylight_search** - Search codebase
   ```json
   {
     "query": "mkDerivation",
     "type": "nix"
   }
   ```

## CLI Tools

```bash
# Validate single file
node scripts/validate-file.js <file>

# Watch for changes and validate
node scripts/watch-and-validate.js

# Run comprehensive test suite
node scripts/test-all-violations.js
```

## Configuration Files Explained

### `.claude/straylight-mcp.js`
The MCP server that provides validation tools to AI assistants. Contains all 64+ Straylight Protocol rules with pattern matching and custom check functions. Supports all file types: Nix, Haskell, PureScript, Lean4, Bash, C++23, CUDA, Dhall, Bazel, Rust, Python, Literate Programming, and Config Files.

### `.claude/settings.json`
Claude Code configuration that tells it where to find the MCP server. Automatically updated by setup scripts.

### `.cursor/rules/*.mdc`
Cursor IDE rules that guide AI code generation. These are loaded automatically by Cursor and enforce the mandatory workflow.

### `hooks/pre-commit`
Git hook that validates files before commit. Blocks commits with violations. Must be executable and linked to `.git/hooks/pre-commit`.

### `scripts/validate-file.js`
Standalone validator that can be run manually or by hooks/CI. Mirrors MCP server logic for consistency.

### `scripts/test-all-violations.js`
Comprehensive test suite with 44 test cases that verifies all rules are being caught correctly.

### `scripts/watch-and-validate.js`
File watcher that validates files on save. Can run as background process for real-time feedback.

### `.github/workflows/straylight-enforcement.yml`
GitHub Actions workflow that validates code on PRs and pushes. Uses `validate-file.js` for comprehensive checks.

### `AGENTS.md` / `CLAUDE.md`
Instructions for AI assistants. Documents the mandatory workflow: Plan → Locate → Template → Validate → Write.

### `.cursorrules` / `.clinerules` / `.windsurfrules`
Legacy rule files for various AI coding assistants. Deprecated in favor of `.cursor/rules/` but kept for compatibility.

## Troubleshooting

### Hook Not Running

**Check hook is executable:**
```bash
ls -l hooks/pre-commit
# Should show -rwxr-xr-x or similar
```

**Check git hook link:**
```bash
ls -l .git/hooks/pre-commit
# Should point to ../../hooks/pre-commit
```

**Re-link if needed:**
```bash
rm .git/hooks/pre-commit
ln -sf ../../hooks/pre-commit .git/hooks/pre-commit
```

**Windows PowerShell:**
```powershell
Remove-Item .git\hooks\pre-commit -ErrorAction SilentlyContinue
New-Item -ItemType SymbolicLink -Path .git\hooks\pre-commit -Target ..\..\hooks\pre-commit -Force
```

### MCP Server Not Working

**Check Node.js version:**
```bash
node --version  # Should be 18.0.0 or higher
```

**Check dependencies:**
```bash
npm list @modelcontextprotocol/sdk
```

**Re-install if needed:**
```bash
rm -rf node_modules package-lock.json
npm install
```

**Re-run setup:**
```bash
node scripts/setup-claude-mcp.js
# Restart Claude Code
```

**Check MCP server syntax:**
```bash
node -c .claude/straylight-mcp.js
```

### Validation Script Errors

**Check script syntax:**
```bash
node -c scripts/validate-file.js
```

**Check file paths:**
```bash
# Ensure paths are relative to project root
node scripts/validate-file.js <relative-path>
```

**Run test suite:**
```bash
node scripts/test-all-violations.js
# Should show all 44 tests passing
```

**Check for path issues (Windows):**
```powershell
# Paths should use forward slashes or be normalized
# Check if file exists
Test-Path scripts\validate-file.js
```

### CI Workflow Not Running

1. Check GitHub Actions is enabled in repository settings
2. Verify workflow file is in `.github/workflows/`
3. Check workflow syntax: GitHub → Actions → Workflows → Check syntax
4. Ensure paths in workflow match your file structure
5. Check workflow logs for specific errors

### Windows-Specific Issues

**Symbolic links require admin (CMD):**
```cmd
# Run CMD as administrator
mklink .git\hooks\pre-commit ..\..\hooks\pre-commit
```

**PowerShell execution policy:**
```powershell
# If scripts won't run
Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser
```

**Path separators:**
- Scripts normalize paths automatically
- If issues persist, check file paths use forward slashes or are normalized

## Verification

After setup, verify everything works:

```bash
# 1. Test validation
node scripts/validate-file.js scripts/validate-file.js  # Should pass

# 2. Test hook (should fail)
echo 'with lib;' > /tmp/test.nix
git add /tmp/test.nix
git commit -m "test"  # Should be blocked ✅

# 3. Test MCP (if using Claude Code)
# Open Claude Code, check if straylight tools are available

# 4. Test CI (push a branch)
# Create a test branch, make a change, push
# Check GitHub Actions tab
```

## Customization

### Adjusting File Paths

If your project structure differs, update paths in:

- **`hooks/pre-commit`** (line 25) - File pattern matching
- **`scripts/validate-file.js`** (line 32) - Default watch directory  
- **`.github/workflows/straylight-enforcement.yml`** (line 10) - Path filters

### Adding Custom Rules

1. Edit `.claude/straylight-mcp.js` - Add rule to `RULES` object
2. Sync to `scripts/validate-file.js` - Copy rule logic
3. Update `.cursor/rules/001_straylight-protocol.mdc` - Document rule
4. Add test case to `scripts/test-all-violations.js` (if you have test files)

### Disabling Specific Rules

Edit `.claude/straylight-mcp.js` and `scripts/validate-file.js`:

```javascript
// Comment out or remove rule from RULES object
// {
//   pattern: /some-pattern/,
//   rule: "RULE-CODE",
//   message: "Some message",
// },
```

## Maintenance

### Updating Rules

When Straylight Protocol rules change:

1. Update `.claude/straylight-mcp.js`
2. Sync changes to `scripts/validate-file.js`
3. Update documentation in `.cursor/rules/`
4. Update `AGENTS.md` / `CLAUDE.md` if workflow changes
5. Test with `node scripts/test-all-violations.js`

### Updating Dependencies

```bash
npm update @modelcontextprotocol/sdk
```

### Verifying Everything Works

Run the verification checklist:

```bash
# 1. Validation script works
node scripts/validate-file.js scripts/validate-file.js

# 2. Hook blocks violations
echo 'with lib;' > /tmp/test.nix
git add /tmp/test.nix
git commit -m "test"  # Should fail

# 3. MCP server works (if using Claude Code)
# Check Claude Code MCP panel

# 4. CI works (push a branch)
# Check GitHub Actions tab
```

## Documentation

- **AGENTS.md** - Complete agent instructions and workflow
- **CLAUDE.md** - Claude Code specific instructions
- **.claude/README.md** - MCP server documentation
- **skill/straylight-script/SKILL.md** - Writing Haskell scripts guide
- **.cursor/rules/*** - Cursor IDE rule files
- **CHECKLIST.md** - Verification checklist

## Next Steps

1. **Read Documentation**: Review files in `straylight-protocol` folder
2. **Test Workflow**: Make a small change, commit, verify hook runs
3. **Configure CI**: Push a branch, verify workflow runs
4. **Set Up Watcher**: Run `node scripts/watch-and-validate.js` for real-time validation
5. **Train Team**: Share `AGENTS.md` and `CLAUDE.md` with team members

---

**🎉 You're ready! Copy the files and start coding with bulletproof enforcement.**
