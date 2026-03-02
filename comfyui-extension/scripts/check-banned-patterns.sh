#!/usr/bin/env bash
# check-banned-patterns.sh
#
# Check for banned patterns across the codebase
# BANNED: undefined, error, head/tail, unsafeCoerce, ??/|| defaults, ! assertions
#
# Exit code: 0 if no violations, 1 if violations found

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

VIOLATIONS=0

echo "Checking for banned patterns..."

# ============================================================================
# HASKELL BANNED PATTERNS
# ============================================================================

echo "Checking Haskell files..."

# Check for undefined
if grep -r --include="*.hs" "\bundefined\b" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"; then
  echo "❌ ERROR: Found 'undefined' in Haskell code"
  grep -rn --include="*.hs" "\bundefined\b" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for error
if grep -r --include="*.hs" "\berror\s" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"; then
  echo "❌ ERROR: Found 'error' in Haskell code"
  grep -rn --include="*.hs" "\berror\s" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for head/tail (partial functions)
if grep -r --include="*.hs" "\bhead\b\|\btail\b" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "import.*head\|import.*tail"; then
  echo "❌ ERROR: Found 'head' or 'tail' (partial functions) in Haskell code"
  grep -rn --include="*.hs" "\bhead\b\|\btail\b" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "import.*head\|import.*tail"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# ============================================================================
# PURESCRIPT BANNED PATTERNS
# ============================================================================

echo "Checking PureScript files..."

# Check for unsafeCoerce
if grep -r --include="*.purs" "unsafeCoerce" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"; then
  echo "❌ ERROR: Found 'unsafeCoerce' in PureScript code"
  grep -rn --include="*.purs" "unsafeCoerce" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# ============================================================================
# TYPESCRIPT BANNED PATTERNS
# ============================================================================

echo "Checking TypeScript files..."

# Check for ?? (nullish coalescing as default)
if grep -r --include="*.ts" --include="*.tsx" "\?\?" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "//.*??" | grep -v "test.*??"; then
  echo "❌ ERROR: Found '??' (nullish coalescing) in TypeScript code"
  grep -rn --include="*.ts" --include="*.tsx" "\?\?" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "//.*??" | grep -v "test.*??"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for || as default value
if grep -r --include="*.ts" --include="*.tsx" "\|\|" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "//.*||" | grep -v "test.*||" | grep -v "if.*||"; then
  echo "⚠️  WARNING: Found '||' (may be used as default) in TypeScript code"
  # This is a warning, not an error - || can be legitimate
fi

# Check for ! (non-null assertions)
if grep -r --include="*.ts" --include="*.tsx" "!\s*[a-zA-Z]" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "//.*!" | grep -v "test.*!" | grep -v "if.*!"; then
  echo "❌ ERROR: Found '!' (non-null assertion) in TypeScript code"
  grep -rn --include="*.ts" --include="*.tsx" "!\s*[a-zA-Z]" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "//.*!" | grep -v "test.*!" | grep -v "if.*!"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# ============================================================================
# SUMMARY
# ============================================================================

if [ $VIOLATIONS -eq 0 ]; then
  echo "✅ No banned patterns found"
  exit 0
else
  echo "❌ Found $VIOLATIONS violation(s)"
  exit 1
fi
