# OOM (Out-Of-Memory) Error Fix Summary

**Last Updated:** 2026-01-18  
**Status:** 🔴 **AGGRESSIVE OPTIMIZATIONS APPLIED** - Restart Cursor required

## Problem
Cursor IDE was experiencing OOM errors (`reason: 'oom', code: '-536870904'`) due to excessive memory usage by language servers analyzing a large codebase (~539,000 lines, 73 files still importing `useCompositorStore`).

## Changes Applied (AGGRESSIVE)

### 1. TypeScript Language Server Memory Limits (`.vscode/settings.json`) - REDUCED
- **`typescript.tsserver.maxTsServerMemory: 2048`** - ⚠️ **REDUCED from 4GB to 2GB** to prevent OOM
- **`typescript.tsserver.watchOptions.excludeDirectories`** - Excludes large directories + test files + docs
- **`typescript.tsserver.useSyntaxServer: "always"`** - ⚠️ **FORCED** to always use lighter syntax server
- **`typescript.tsserver.useSeparateSyntaxServer: true`** - Uses separate syntax server process
- **`typescript.disableAutomaticTypeAcquisition: true`** - Disables automatic type acquisition
- **`typescript.suggest.enabled: false`** - ⚠️ **DISABLED** all TypeScript suggestions
- **`typescript.preferences.includePackageJsonAutoImports: "off"`** - Reduces auto-import analysis overhead
- **`typescript.suggest.autoImports: false`** - Disables expensive auto-import suggestions
- **`typescript.tsserver.experimental.enableProjectDiagnostics: false`** - Disables project-wide diagnostics (uses file-by-file instead)

### 2. File Watching Optimizations (`.vscode/settings.json`) - AGGRESSIVE
- **`files.watcherExclude`** - Excludes `node_modules`, `dist`, `build`, `web/js`, Python caches, Nix files, **test files**, **docs**, and **leancomfy** from file watching
- Reduces overhead from watching thousands of files
- **Test files excluded:** `**/*.test.ts`, `**/*.spec.ts`, `**/__tests__/**`

### 3. Search Indexing Optimizations (`.vscode/settings.json`) - AGGRESSIVE
- **`search.exclude`** - Excludes large directories + test files + docs from search indexing
- Prevents Cursor from indexing unnecessary files
- **Test files excluded:** `**/*.test.ts`, `**/*.spec.ts`, `**/__tests__/**`

### 4. Python/Pyright Optimizations (`.vscode/settings.json`)
- **`python.analysis.diagnosticMode: "openFilesOnly"`** - Only analyzes open files, not entire workspace
- **`python.analysis.indexing: false`** - Disables expensive indexing
- **`python.analysis.packageIndexDepths`** - Limits package analysis depth

### 5. Cursor-Specific Optimizations (`.vscode/settings.json`) - AGGRESSIVE
- **`cursor.chat.maxContextLength: 30000`** - ⚠️ **REDUCED from 50k to 30k** to reduce memory usage
- **`cursor.general.maxOpenFiles: 10`** - ⚠️ **REDUCED from 20 to 10** to limit open files
- **`cursor.general.enableCodeActions: false`** - ⚠️ **DISABLED** code actions
- **`cursor.general.enableHover: false`** - ⚠️ **DISABLED** hover tooltips
- **Editor visual features disabled:** minimap, semantic highlighting, bracket colorization, whitespace rendering

### 6. TypeScript Config Optimizations (`ui/tsconfig.json`) - AGGRESSIVE
- Added exclusions for `node_modules`, `dist`, `build`, `web/js` directories
- **Added exclusions:** `**/__tests__/**`, `**/test/**`, `**/tests/**`, `docs`, `leancomfy`
- Reduces TypeScript compiler analysis scope significantly

## ⚠️ CRITICAL: IMMEDIATE ACTIONS REQUIRED

### 1. **RESTART CURSOR NOW** 🔴
**Settings will NOT take effect until Cursor is fully restarted:**
1. Close all Cursor windows
2. Wait 10 seconds
3. Reopen Cursor
4. Verify settings applied (check TypeScript server memory limit in status bar)

### 2. **Close Unused Files**
- Keep **maximum 10 files open** (enforced by `cursor.general.maxOpenFiles: 10`)
- Close all test files, docs, and unused tabs
- Close unused terminal tabs (each consumes memory)

### 3. **Monitor Memory Usage**
- Check Task Manager → Cursor process memory
- If still >2GB, further reductions may be needed

## If OOM Persists After Restart

#### Option 1: Further Reduce TypeScript Memory (EXTREME)
Edit `.vscode/settings.json`:
```json
"typescript.tsserver.maxTsServerMemory": 1536  // Reduce to 1.5GB
```

#### Option 2: Increase System Memory
- Close other applications
- Increase virtual memory/page file size
- Consider upgrading RAM if consistently hitting limits

### Monitoring Memory Usage
- Check Task Manager (Windows) for Cursor process memory usage
- Monitor TypeScript server process (`tsserver`) memory
- **Target:** <2GB for TypeScript server (enforced limit)
- If consistently >2GB, reduce `maxTsServerMemory` further

## Verification
After restarting Cursor:
1. ✅ Open a TypeScript file - should load without OOM
2. ✅ Check TypeScript server status (bottom-right status bar) - should show <2GB memory
3. ✅ Verify file watching excludes large directories (check output panel)
4. ✅ Monitor memory usage over time - should stay stable

## ⚠️ Trade-offs (What's Disabled)

**Disabled Features:**
- ❌ TypeScript auto-imports and suggestions
- ❌ Code actions (quick fixes)
- ❌ Hover tooltips
- ❌ Semantic highlighting
- ❌ Minimap
- ❌ Bracket colorization
- ❌ Project-wide diagnostics (file-by-file only)

**Still Working:**
- ✅ Type checking on open files
- ✅ Syntax highlighting
- ✅ Basic IntelliSense
- ✅ Error diagnostics
- ✅ File navigation

## Notes
- **These optimizations are AGGRESSIVE** - many IDE features are disabled to prevent OOM
- Type checking still works on open files (file-by-file analysis)
- Settings can be adjusted based on your system's available memory
- **If OOM persists:** Consider reducing `maxTsServerMemory` to 1536 (1.5GB) or 1024 (1GB)
