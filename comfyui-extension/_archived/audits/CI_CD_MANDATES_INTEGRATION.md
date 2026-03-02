# CI/CD Code Mandates Integration

## Summary

The 7 core code mandates are now **enforced in CI/CD** via automated checks that run on every push and pull request.

---

## Implementation

### Script: `scripts/check-code-mandates.sh`

Comprehensive validation script that checks all 7 mandates:

1. **Literate Programming** - Verifies JSDoc documentation on functions
2. **Total Functions** - Detects partial functions (`!`, `?.`, `head`, `tail`, `fromJust`)
3. **Bounded Polymorphism** - Checks for unconstrained generics (`<T>` without `extends`)
4. **Named Constants** - Detects magic numbers (excluding 0, 1, -1 and common patterns)
5. **Split Functions** - Validates function length (max 50 lines)
6. **Typed Dicts** - Detects bare dictionaries (`Record<string, any>`, untyped `object`)
7. **Security Wired** - Checks for unsanitized input/output (`innerHTML`, `eval`, user input)

### CI/CD Integration

Added to `.github/workflows/ci.yml` in the `code-quality` job:

```yaml
- name: Check code mandates (7 core mandates)
  run: bash scripts/check-code-mandates.sh
  continue-on-error: false
```

**Location:** Runs after lazy pattern checks and before Haskell Maybe/Nothing checks.

---

## Enforcement Levels

### Blocking Violations (CI Fails)

- **Mandate 2:** Partial functions (`!`, `?.` without handling, `head`/`tail`/`fromJust`)
- **Mandate 6:** Bare/untyped dictionaries (`Record<string, any>`, untyped `object`)
- **Mandate 7:** Security violations (`innerHTML` without sanitization, `eval()`, unsanitized user input)

### Warnings (Non-Blocking)

- **Mandate 1:** Missing JSDoc documentation
- **Mandate 3:** Unbounded generics
- **Mandate 4:** Magic numbers
- **Mandate 5:** Functions exceeding 50 lines

---

## Usage

### Local Testing

```bash
# Run the check locally before committing
bash scripts/check-code-mandates.sh

# Exit code 0 = all checks pass
# Exit code 1 = violations found (CI will fail)
```

### CI/CD Behavior

- **On Push/PR:** Automatically runs as part of `code-quality` job
- **On Failure:** CI job fails, merge is blocked
- **Output:** Detailed report showing violations with file:line references

---

## Example CI Output

```
==========================================
CODE MANDATE VERIFICATION
==========================================

MANDATE 1: Checking literate programming style...
  ⚠️  ui/src/utils/helpers.ts:42 - Function missing JSDoc documentation
  ⚠️  Found 1 undocumented function(s)

MANDATE 2: Checking for total functions (no partial functions)...
  ❌ ui/src/stores/userStore.ts:156 - Non-null assertion (!) detected
  ❌ Found 1 partial function violation(s)

MANDATE 3: Checking bounded polymorphism...
  ✅ All generics have explicit bounds

MANDATE 4: Checking for magic numbers...
  ✅ No magic numbers detected

MANDATE 5: Checking function length (max 50 lines)...
  ✅ All functions under 50 lines

MANDATE 6: Checking typed dictionaries...
  ❌ ui/src/api/client.ts:89 - Bare/untyped dictionary detected
  ❌ Found 1 bare/untyped dictionary violation(s)

MANDATE 7: Checking security (input sanitization + output filtering)...
  ✅ Security checks passed

==========================================
SUMMARY
==========================================
Violations (blocking): 2
Warnings (non-blocking): 1

❌ Code mandate violations found - CI will fail
```

---

## Integration with Existing Checks

The code mandates check complements existing CI/CD checks:

| Check | Purpose | Relationship |
|-------|---------|--------------|
| `check-banned-patterns.sh` | Banned language constructs | Overlaps with Mandate 2 (partial functions) |
| `check-lazy-patterns.js` | Lazy code patterns (`??`, `?.`) | Overlaps with Mandate 2 |
| `check-code-mandates.sh` | **7 core mandates** | **Comprehensive code quality** |
| `check-error-messages.sh` | Error message format | Separate concern |
| `haskell-no-maybe-check` | Haskell Maybe ban | Separate concern |

**Note:** Some overlap exists (e.g., partial functions), but the mandates check provides comprehensive coverage of all 7 requirements.

---

## Documentation

- **[CODE_MANDATES.md](./CODE_MANDATES.md)** - Complete mandate specifications with examples
- **[AGENTS.md](../AGENTS.md)** - References mandates in Core Principles (§1)
- **[CI_CD_SETUP.md](./CI_CD_SETUP.md)** - General CI/CD documentation

---

## Future Enhancements

Potential improvements:

1. **AST-based analysis** - Replace regex-based checks with proper AST parsing for more accurate detection
2. **Language-specific checks** - Add PureScript/Haskell-specific mandate validation
3. **Auto-fix suggestions** - Generate suggested fixes for violations
4. **Pre-commit hook** - Run checks before commit (in addition to CI/CD)
5. **PR comments** - Automatically comment on PRs with violation details

---

## Maintenance

**When updating mandates:**
1. Update `scripts/check-code-mandates.sh` with new checks
2. Update `docs/CODE_MANDATES.md` with new requirements
3. Update this document if enforcement levels change
4. Test locally: `bash scripts/check-code-mandates.sh`

**When adding new languages:**
1. Add language-specific checks to the script
2. Document language-specific patterns in `CODE_MANDATES.md`
3. Update CI/CD if additional setup is needed
