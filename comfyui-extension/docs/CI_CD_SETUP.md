# CI/CD Pipeline Setup Guide

## Overview

This project uses an improved CI/CD pipeline that prevents common errors by catching them early through:

1. **Pre-commit hooks** - Run checks before code is committed
2. **Pre-push hooks** - Run comprehensive checks before code is pushed
3. **GitHub Actions CI** - Automated checks on every push/PR
4. **Lazy pattern detection** - Custom script to catch System F/Omega violations

## Setup Instructions

### 1. Install Husky (Pre-commit Hooks)

```bash
# Install Husky
npm install --save-dev husky

# Initialize Husky
npx husky install

# Make hooks executable (Unix/Mac)
chmod +x .husky/pre-commit
chmod +x .husky/pre-push
```

### 2. Available Scripts

#### Code Quality Checks

```bash
# Format code
npm run format              # Format all files
npm run format:check        # Check formatting without modifying

# Lint code
npm run lint                # Check for linting issues
npm run lint:fix            # Fix linting issues automatically

# Type check
npm run typecheck           # Run TypeScript type checking

# Lazy pattern detection
npm run check:lazy          # Check for lazy patterns (errors only)
npm run check:lazy:strict   # Check for lazy patterns (errors + warnings)

# Run all checks
npm run check:all           # Format check + lint + typecheck + lazy patterns
```

#### Pre-commit Hook

The pre-commit hook automatically runs:
- Code formatting
- Lint fixes
- Type checking
- Lazy pattern detection

#### Pre-push Hook

The pre-push hook runs all checks (`check:all`) before allowing a push.

## CI/CD Pipeline Jobs

### 1. Code Quality Job

Runs on every push/PR:
- ✅ Formatting check
- ✅ Linting
- ✅ Type checking
- ✅ Lazy pattern detection (strict mode)

**Fails if:** Any check fails

### 2. Test Job

Runs on every push/PR:
- ✅ Unit tests
- ✅ Browser tests
- ✅ Uploads coverage reports

**Fails if:** Tests fail

### 3. Build Job

Runs after code-quality and test jobs pass:
- ✅ Production build
- ✅ Uploads build artifacts

**Fails if:** Build fails

### 4. Security Audit Job

Runs on PRs only:
- ✅ Security tests
- ✅ npm audit

**Warns but doesn't fail** on audit issues (for visibility)

### 5. TypeScript Strict Mode Check

Runs on PRs only:
- ✅ Type checking with `--strict` flag
- ✅ Comments PR with type errors if found

**Warns but doesn't fail** (for visibility)

## What Gets Caught

### Lazy Code Patterns (Errors)

These will **fail** the CI:

- `??` (nullish coalescing) - Use explicit pattern matching
- `?.` (optional chaining) - Use explicit nested if conditions
- `|| []` (lazy array defaults) - Use `Array.isArray()` checks
- `|| {}` (lazy object defaults) - Use explicit object type checks
- `return null` / `return undefined` - Throw errors or document exceptions

### Type Safety Issues (Warnings)

These will **warn** in strict mode:

- `as any` / `: any` (type escapes) - Use proper type narrowing
- `!` (non-null assertions) - Use explicit type guards

### Exception Handling

Patterns are allowed if they have exception comments:

```typescript
// Vue template compatibility - valid exception
return null;

// System F/Omega: valid exception
const value = data?.property ?? defaultValue;
```

## Troubleshooting

### Pre-commit Hook Not Running

```bash
# Reinstall Husky
npx husky install

# Check if hooks are executable
ls -la .husky/
```

### CI Failing on Formatting

```bash
# Fix formatting locally
npm run format

# Commit the changes
git add .
git commit -m "chore: fix formatting"
```

### CI Failing on Lazy Patterns

```bash
# Check what patterns are detected
npm run check:lazy:strict

# Fix patterns manually or document exceptions
```

### Type Errors in CI

```bash
# Check types locally
npm run typecheck

# Fix type errors
# Or add proper type guards/assertions
```

## Benefits

1. **Early Detection** - Catch errors before they reach the repository
2. **Consistent Code** - Automated formatting ensures consistency
3. **Type Safety** - Type checking prevents runtime errors
4. **System F/Omega Compliance** - Lazy pattern detection enforces principles
5. **Faster Feedback** - Pre-commit hooks catch issues immediately
6. **Better PRs** - CI provides clear feedback on what needs fixing

## Migration Notes

If you're migrating from the old CI:

1. The old `lint-and-typecheck` job is now `code-quality`
2. Added lazy pattern detection
3. Added pre-commit/pre-push hooks
4. Added TypeScript strict mode check (PRs only)
5. Better error reporting and artifact uploads

## Next Steps

1. Install Husky: `npm install --save-dev husky && npx husky install`
2. Test pre-commit hook: Make a small change and try to commit
3. Review CI results: Check GitHub Actions for any failures
4. Fix any detected issues: Use the scripts above to fix problems
