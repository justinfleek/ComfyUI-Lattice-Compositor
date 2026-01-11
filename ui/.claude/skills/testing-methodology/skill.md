# Testing Methodology Skill

## Test Types and When to Use

### Property Tests (fast-check)
**Location:** `src/__tests__/property/`
**Use for:** Pure functions, math, validation, transformations
**Pattern:**
```typescript
import { fc } from "@fast-check/vitest";

describe("functionName", () => {
  it.prop([fc.float(), fc.float()])("property description", (a, b) => {
    const result = functionName(a, b);
    expect(Number.isFinite(result)).toBe(true);
  });
});
```

### Unit Tests (vitest)
**Location:** `src/__tests__/unit/`
**Use for:** Specific behavior, edge cases, error handling

### Integration Tests
**Location:** `src/__tests__/integration/`
**Use for:** Store interactions, service coordination

### Browser Tests (playwright)
**Location:** `ui/e2e/`
**Use for:** Canvas, WebGL, DOM interactions

### Regression Tests
**Location:** `src/__tests__/regression/`
**Use for:** Bug fixes (named after bug ID)

## Test Naming Convention
- `{feature}.test.ts` - Unit tests
- `{feature}.property.test.ts` - Property tests
- `{feature}.integration.test.ts` - Integration tests
- `{bugId}.regression.test.ts` - Regression tests

## What to Test
1. **Happy path** - Normal inputs work
2. **Edge cases** - 0, null, undefined, empty, max values
3. **Invalid inputs** - NaN, Infinity, wrong types
4. **Invariants** - Things that must always be true

## Running Tests
```bash
npm test                     # All tests
npm test -- {pattern}        # Filtered
npm run test:browser         # Playwright tests
npx vitest --reporter=verbose  # Detailed output
```
