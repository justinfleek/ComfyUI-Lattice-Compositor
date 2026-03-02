# Straylight Protocol Testing Suite

**BUG HUNTING TEST SUITE** - These tests are designed to **FIND BUGS** in enforcement mechanisms, not just verify they exist.

## Purpose

These tests hunt for bugs in:
- Rule enforcement logic
- Pre-commit hooks
- Validator edge cases
- MCP server functionality
- Configuration validation
- Integration workflows

**Tests are NOT supposed to pass** - they're supposed to find bugs that need fixing.

## Test Structure

```
tests/
├── rules/              # Rule validation tests
├── enforcement/        # Enforcement mechanism tests
├── config/             # Configuration validation tests
├── integration/        # Integration tests
├── e2e/                # End-to-end tests
├── fixtures/           # Test fixtures
│   ├── violations/    # Violation test cases
│   ├── valid/         # Valid code examples
│   └── config/        # Configuration fixtures
└── helpers/           # Test helper utilities
```

## Running Tests

```bash
# Run all tests
npm test

# Run tests in watch mode
npm run test:watch

# Run tests with coverage
npm run test:coverage

# Run specific test suite
npm test -- tests/rules
npm test -- tests/enforcement
npm test -- tests/config
npm test -- tests/integration
npm test -- tests/e2e
```

## Test Coverage

### Layer 1: Rule Validation Tests (`tests/rules/`)
- Tests all 64+ rules in `scripts/rules.js`
- Verifies pattern matching, custom check functions, exceptions
- Tests edge cases (comments, strings, multi-line patterns)
- Coverage: All file types (Nix, Haskell, PureScript, Lean4, Bash, C++23, Literate Programming, etc.)

### Layer 2: Enforcement Mechanism Tests (`tests/enforcement/`)
- **MCP Server Tests**: All 6 MCP tools (straylight_validate, straylight_template, straylight_locate, straylight_plan, straylight_examples, straylight_search)
- **Pre-commit Hook Tests**: Verifies hook blocks violations, allows clean commits
- **CI Workflow Tests**: GitHub Actions workflow validation steps
- **File Watcher Tests**: Real-time validation on file changes
- **Standalone Validator Tests**: `validate-file.js` script in isolation

### Layer 3: Configuration Tests (`tests/config/`)
- **Cursor Rules Tests**: Validates `.cursor/rules/*.mdc` files
- **Skills Tests**: Validates all 11 skills in all locations
- **Agent Config Tests**: Tests `AGENTS.md`, `CLAUDE.md`, `opencode.json`
- **MCP Config Tests**: Validates `.claude/settings.json` and MCP server configuration

### Layer 4: Integration Tests (`tests/integration/`)
- **Workflow Integration**: Tests Plan → Locate → Template → Validate → Write workflow
- **Rule Synchronization**: Verifies rules stay synchronized between components
- **Multi-File Validation**: Tests validation across multiple files in a commit
- **Skill Activation**: Tests skill activation triggers and keyword matching

### Layer 5: End-to-End Tests (`tests/e2e/`)
- **Full Workflow**: Simulates complete code generation → validation → commit → CI pipeline
- **Violation Detection**: Tests violations caught at every enforcement point
- **Bypass Prevention**: Verifies violations cannot be bypassed
- **Cross-Platform**: Tests on Windows, Linux, macOS

## Test Fixtures

### Violation Fixtures (`tests/fixtures/violations/`)
One file per rule violation type, organized by file type:
- `nix-wsn-e001.nix` - with lib; violation
- `nix-wsn-e002.nix` - mkDerivation rec violation
- `bash-straylight-006.sh` - Bash logic violation
- `haskell-straylight-007.hs` - undefined violation
- And more...

### Valid Fixtures (`tests/fixtures/valid/`)
Valid code examples for each file type that should pass all validation rules:
- `nix-valid.nix` - Valid Nix code
- `bash-valid.sh` - Valid bash (exec "$@")
- `haskell-valid.hs` - Valid Haskell script
- And more...

## Success Criteria

1. ✅ **100% Rule Coverage**: Every rule has test cases
2. ✅ **100% Enforcement Coverage**: Every mechanism tested
3. ✅ **100% Configuration Coverage**: Every config validated
4. ✅ **Zero False Positives**: No valid code flagged as violation
5. ✅ **Zero False Negatives**: No violations missed
6. ✅ **Cross-Platform Compatibility**: Tests pass on Windows, Linux, macOS
7. ✅ **Performance**: Unit tests complete in <30 seconds
8. ✅ **CI Integration**: Tests run automatically on PR/commit

## Maintenance

- **Rule Changes**: Update tests when rules change
- **New Enforcement Points**: Add tests for new mechanisms
- **Bug Fixes**: Add regression tests for fixed bugs
- **Coverage Monitoring**: Track coverage metrics over time
- **Test Review**: Review tests alongside code reviews
