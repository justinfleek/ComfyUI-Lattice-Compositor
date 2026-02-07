# Terminal Size Fix for Playwright E2E Tests

## Why This Matters

The "bogus screen size" warning can affect:
1. **Test output formatting** - Playwright reporter output may be garbled
2. **CI/CD environments** - Terminal size detection failures in CI
3. **Debug output readability** - Hard to read test failures with wrong terminal size
4. **Screenshot comparisons** - If terminal affects viewport calculations (rare but possible)

## What We Fixed

### 1. Nix Dev Shell (Automatic)
The `shellHook` in `nix/flake-module.nix` now:
- Detects bogus terminal sizes (>1000 columns or <2 rows)
- Sets reasonable defaults (120x30)
- Configures `stty` for proper terminal detection

**Result**: Fixed automatically when you enter `nix develop`

### 2. Playwright Config (Runtime Fix)
`ui/playwright.config.ts` now:
- Checks `COLUMNS`/`LINES` environment variables
- Fixes bogus values before Playwright starts
- Ensures test output is properly formatted

### 3. Test Scripts (Pre-run Fix)
`ui/scripts/setup-test-env.sh`:
- Runs before Playwright tests
- Sets terminal size explicitly
- Exports variables for Playwright

**Result**: `npm run test:playwright` automatically fixes terminal size

## How It Works

### Browser Viewport (Not Affected)
- Playwright controls browser viewport via `devices['Desktop Chrome']`
- Terminal size doesn't affect browser window size
- ✅ Your tests will run correctly regardless

### Test Output (Now Fixed)
- Terminal size affects **reporter output formatting**
- Fixed terminal size = readable test output
- ✅ Test failures will be easier to debug

## Verification

Run this to check terminal size:
```bash
echo "Terminal: ${COLUMNS}x${LINES}"
tput cols && tput lines
```

Should show reasonable values like `120x30` or `80x24`, not `131072x1`.

## Manual Fix (If Needed)

If you still see warnings:
```bash
export COLUMNS=120
export LINES=30
stty cols 120 rows 30
```

Or use the helper script:
```bash
./fix-terminal-size.sh
```

## Bottom Line

✅ **Fixed proactively** - Won't affect Playwright tests
✅ **Automatic** - Fixed when entering Nix shell
✅ **Test scripts protected** - `npm run test:playwright` fixes it automatically
✅ **Browser unaffected** - Playwright controls viewport independently

Your E2E tests will run perfectly! 🎭
