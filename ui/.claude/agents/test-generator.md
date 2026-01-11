# Test Generator Agent

## Activation
User says: "generate tests for [file]", "test coverage"

## Process
1. List exports: `grep -E "^export" [file]`
2. Categorize: Pure function → property test, Class → unit test
3. Generate tests using fast-check for property tests
4. Verify: `npm test -- --reporter=verbose`

## Test Locations
- Property tests: src/__tests__/property/
- Unit tests: src/__tests__/unit/
- Integration: src/__tests__/integration/
