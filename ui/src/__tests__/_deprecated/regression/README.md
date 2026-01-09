# Regression Test Suite

Tests that verify fixed bugs do not return.

## Purpose

Every bug that is fixed MUST have a corresponding regression test that:
1. Reproduces the original failure condition
2. Verifies the fix works
3. Runs on every CI build

## Naming Convention

```
BUG-XXX-short-description.regression.test.ts
```

## Test Template

```typescript
/**
 * Regression test for BUG-XXX: Short Description
 * 
 * @fixed 2026-01-XX
 * @file services/path/to/file.ts
 * @rootCause Brief description of what caused the bug
 * @fix Brief description of how it was fixed
 */
import { describe, test, expect } from 'vitest';

describe('BUG-XXX Regression', () => {
  test('original failure case now passes', () => {
    // Reproduce the EXACT counterexample from the bug report
    const input = { /* counterexample values */ };
    
    // Call the function that was broken
    const result = functionUnderTest(input);
    
    // Assert the correct behavior
    expect(result).toSatisfyCondition();
  });

  test('edge case that triggered the bug', () => {
    // Test the specific edge case
  });
});
```

## Running

```bash
# All regression tests
npm run test -- regression/

# Specific bug
npm run test -- regression/BUG-001
```

## Current Status

| Bug ID | Description | File | Regression Test |
|--------|-------------|------|-----------------|
| BUG-001 | Depth exceeds clip range | depthRenderer.ts | ⬜ |
| BUG-002 | minDepth > maxDepth | depthRenderer.ts | ⬜ |
| ... | ... | ... | ... |
| BUG-069 | Silent effect failure | effectProcessor.ts | ⬜ |

Total: 63 bugs needing regression tests
