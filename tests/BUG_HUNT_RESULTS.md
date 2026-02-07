# Bug Hunt Test Results

These tests are designed to **FIND BUGS** in the enforcement mechanisms, not just verify they exist.

## How to Run Bug Hunt Tests

```bash
# Run all bug hunt tests
npm test

# Run specific bug hunt test
node tests/rules/rule-bug-hunt.test.js
node tests/enforcement/hook-functional.test.js
node tests/enforcement/validator-bug-hunt.test.js
node tests/enforcement/mcp-server-functional.test.js
node tests/config/config-bug-hunt.test.js
```

## Bugs Found

### Rule Enforcement Bugs

1. **WSN-E001 Exception Handling**: Exception for `with lib;` in list context may not be working correctly
2. **WSN-E003 False Positives**: Rule may be flagging valid code (needs investigation)
3. **WSN-E006 Exception Handling**: Heredoc exception for writeText context needs verification
4. **WSN-E007 String Handling**: Rule correctly ignores violations in strings ✅
5. **STRAYLIGHT-003 Exception Handling**: cmakeFlags exception needs verification

### Pre-commit Hook Bugs

1. **Valid File Blocking**: Hook is blocking commits with valid files (Test 2 failed)
   - **Impact**: Developers cannot commit valid code
   - **Priority**: HIGH - Blocks normal workflow

### Validator Bugs

Tests are running and checking:
- Empty file handling
- Comment-only files
- Very long lines
- Unicode characters
- Special characters in strings
- Multiple violations
- Line number accuracy

## Test Philosophy

These tests are **NOT** designed to pass. They are designed to:
1. **Find bugs** in rule enforcement
2. **Test edge cases** that might break the system
3. **Verify exceptions** work correctly
4. **Ensure hooks** actually block violations
5. **Validate** that enforcement mechanisms function properly

## Fixing Bugs

When a bug is found:
1. Investigate the root cause
2. Fix the enforcement code
3. Verify the bug hunt test now passes
4. Add regression test to prevent recurrence

## Running Tests

The test suite runs automatically with `npm test` and will:
- Report all bugs found
- Exit with code 1 if bugs are found (so CI fails)
- Exit with code 0 only if no bugs found

This ensures bugs are caught and fixed, not ignored.
