# Project Structure Assumptions

The Straylight Protocol enforcement system assumes a specific project structure. This document explains what's expected and how to adapt if your structure differs.

## Expected Structure

```
your-project/
├── straylight-core/          # Main codebase (required for some hooks/watchers)
│   ├── nix/
│   ├── docs/
│   └── ...
├── straylight-protocol/      # Protocol documentation (required)
│   └── docs/rfc/
├── scripts/             # Validation scripts (from BOOTSTRAP)
├── hooks/               # Git hooks (from BOOTSTRAP)
├── .claude/             # MCP server (from BOOTSTRAP)
├── .cursor/             # Cursor rules (from BOOTSTRAP)
└── .github/workflows/   # CI workflows (from BOOTSTRAP)
```

## Files That Reference `straylight-core/`

### 1. `hooks/pre-commit` (lines 10-12)
```bash
if [ -d "straylight-core" ]; then
    cd straylight-core
fi
```
**Purpose:** Changes to `straylight-core` directory before running Nix lint  
**If you don't have `straylight-core`:** This check gracefully skips if directory doesn't exist

### 2. `scripts/watch-and-validate.js` (line 33)
```javascript
const WATCH_DIRS = [
  'straylight-core',
];
```
**Purpose:** Watches `straylight-core` directory for file changes  
**If you don't have `straylight-core`:** Update this array to watch your main code directory

### 3. `.github/workflows/straylight-enforcement.yml` (multiple lines)
**Purpose:** Scans `straylight-core/` for violations  
**If you don't have `straylight-core`:** Update path filters and `find` commands to match your structure

### 4. `.claude/straylight-mcp.js` (line 776)
```javascript
const basePath = "straylight-core";
```
**Purpose:** Base path for MCP tools to locate files  
**If you don't have `straylight-core`:** Update to your main code directory

### 5. Documentation files (`.cursor/rules/*`, `AGENTS.md`, `CLAUDE.md`)
**Purpose:** Reference `straylight-core/docs/rfc/` for protocol documentation  
**If you don't have `straylight-core`:** Update paths to point to your `straylight-protocol` folder

## Adapting to Different Structures

### Option 1: Rename Your Directory
If you have a different name (e.g., `src/`, `lib/`, `code/`):

```bash
# Rename to match expected structure
mv src straylight-core
```

### Option 2: Update Paths

**Update `hooks/pre-commit`:**
```bash
# Change line 10
if [ -d "your-code-dir" ]; then
    cd your-code-dir
fi
```

**Update `scripts/watch-and-validate.js`:**
```javascript
// Change line 33
const WATCH_DIRS = [
  'your-code-dir',
];
```

**Update `.github/workflows/straylight-enforcement.yml`:**
- Change path filters (lines 10, 20)
- Update `find` commands to use your directory name
- Update `grep` commands to scan your directory

**Update `.claude/straylight-mcp.js`:**
```javascript
// Change line 776
const basePath = "your-code-dir";
```

**Update documentation files:**
- `.cursor/rules/001_straylight-protocol.mdc` - Update globs and doc paths
- `AGENTS.md` - Update file location examples
- `CLAUDE.md` - Update file location examples
- `.cursorrules`, `.clinerules`, `.windsurfrules` - Update paths

### Option 3: Use Symlinks

```bash
# Create symlink to match expected structure
ln -s your-code-dir straylight-core
```

## Required vs Optional

### Required
- `straylight-protocol/` folder - Contains RFCs and documentation that MCP tools reference
- `scripts/validate-file.js` - Used by hooks, CI, and watchers

### Optional
- `straylight-core/` directory - Only needed if you want:
  - Nix lint in pre-commit hook
  - File watcher to monitor changes
  - CI workflow to scan entire directory
- `test-violations/` directory - Only needed if you want to run test suite

## Verification

After adapting paths, verify everything works:

```bash
# Test validation (should work regardless of structure)
node scripts/validate-file.js <some-file>

# Test hook (should work if paths updated)
echo 'with lib;' > test.nix
git add test.nix
git commit -m "test"  # Should be blocked

# Test watcher (only works if WATCH_DIRS updated)
node scripts/watch-and-validate.js
```

---

**Note:** The enforcement system is designed to be flexible. The `straylight-core` references are primarily for convenience and can be adapted to your project structure.
