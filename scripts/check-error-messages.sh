#!/usr/bin/env bash
# Check that all error messages follow the explicit error pattern:
# 1. What went wrong
# 2. Where it happened
# 3. How to fix it

set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$PROJECT_ROOT"

ERRORS=0

echo "🔍 Checking error messages for explicit format (What/Where/How to fix)..."

# ============================================================================
# Lean 4 Error Message Check
# ============================================================================
echo ""
echo "📋 Checking Lean 4 error messages..."

LEAN_ERRORS=0

# Check for throwError without "Fix:" or "fix:"
if grep -rn --include="*.lean" "throwError" "$PROJECT_ROOT/standalone/lattice-core/lean" 2>/dev/null | grep -v "Fix:" | grep -v "fix:" | grep -v "\.lake" | grep -v "^Binary" > /tmp/lean_errors.txt; then
  echo "❌ ERROR: Found Lean error messages without 'Fix:' or 'fix:' directive"
  echo ""
  echo "PROTOCOL VIOLATION: All error messages must include:"
  echo "  1. What went wrong"
  echo "  2. Where it happened"
  echo "  3. How to fix it (must include 'Fix:' or 'fix:')"
  echo ""
  echo "Examples:"
  echo "  throwError \"Function failed: Variable '{n}' not found. Fix: Add '{n}' to context\""
  echo "  throwError \"Type mismatch at '{loc}'. Expected X, got Y. Fix: Change type to X\""
  echo ""
  echo "Found violations:"
  head -20 /tmp/lean_errors.txt
  LEAN_ERRORS=$(wc -l < /tmp/lean_errors.txt | tr -d ' ')
  ERRORS=$((ERRORS + LEAN_ERRORS))
fi

# Check for error messages that are too short (likely missing context)
if grep -rn --include="*.lean" "throwError.*\"" "$PROJECT_ROOT/standalone/lattice-core/lean" 2>/dev/null | grep -v "\.lake" | grep -v "^Binary" | awk -F'"' '{print length($2)}' | awk '$1 < 50' > /tmp/short_errors.txt && [ -s /tmp/short_errors.txt ]; then
  echo "⚠️  WARNING: Found potentially too-short error messages (< 50 chars)"
  echo "   Error messages should be descriptive. Consider adding more context."
fi

# ============================================================================
# TypeScript Error Message Check
# ============================================================================
echo ""
echo "📋 Checking TypeScript error messages..."

TS_ERRORS=0

# Check for throw new Error without "Fix:" or "fix:" or "How to fix"
if grep -rn --include="*.ts" --include="*.tsx" "throw new Error" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "Fix:" | grep -v "fix:" | grep -v "How to fix" | grep -v "how to fix" | grep -v "^Binary" > /tmp/ts_errors.txt; then
  echo "❌ ERROR: Found TypeScript error messages without 'Fix:' directive"
  echo ""
  echo "PROTOCOL VIOLATION: All error messages must include:"
  echo "  1. What went wrong"
  echo "  2. Where it happened"
  echo "  3. How to fix it (must include 'Fix:' or 'fix:')"
  echo ""
  echo "Examples:"
  echo "  throw new Error(\`[Context] Action failed: Reason. Fix: Solution\`)"
  echo "  throw new Error(\`[Service] Validation failed at field '{field}'. Fix: Provide valid value\`)"
  echo ""
  echo "Found violations:"
  head -20 /tmp/ts_errors.txt
  TS_ERRORS=$(wc -l < /tmp/ts_errors.txt | tr -d ' ')
  ERRORS=$((ERRORS + TS_ERRORS))
fi

# Check for console.error without explicit error format
if grep -rn --include="*.ts" --include="*.tsx" "console\.error" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "Fix:" | grep -v "fix:" | grep -v "^Binary" > /tmp/console_errors.txt && [ -s /tmp/console_errors.txt ]; then
  echo "⚠️  WARNING: Found console.error without 'Fix:' directive"
  echo "   Consider using throw new Error() with explicit format instead"
  head -10 /tmp/console_errors.txt
fi

# ============================================================================
# Haskell Error Message Check
# ============================================================================
echo ""
echo "📋 Checking Haskell error messages..."

HS_ERRORS=0

# Check for error calls without "Fix:" or "fix:"
if grep -rn --include="*.hs" "error \"" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "Fix:" | grep -v "fix:" | grep -v "^Binary" > /tmp/hs_errors.txt; then
  echo "❌ ERROR: Found Haskell error messages without 'Fix:' directive"
  echo ""
  echo "PROTOCOL VIOLATION: All error messages must include:"
  echo "  1. What went wrong"
  echo "  2. Where it happened"
  echo "  3. How to fix it (must include 'Fix:' or 'fix:')"
  echo ""
  echo "Examples:"
  echo "  error \"[Module] Function failed: Reason. Fix: Solution\""
  echo "  error \"[Service] Validation failed at field '{field}'. Fix: Provide valid value\""
  echo ""
  echo "Found violations:"
  head -20 /tmp/hs_errors.txt
  HS_ERRORS=$(wc -l < /tmp/hs_errors.txt | tr -d ' ')
  ERRORS=$((ERRORS + HS_ERRORS))
fi

# ============================================================================
# Summary
# ============================================================================
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

if [ $ERRORS -eq 0 ]; then
  echo "✅ All error messages follow explicit format (What/Where/How to fix)"
  echo ""
  echo "Summary:"
  echo "  - Lean 4: ✅ All error messages include 'Fix:' directive"
  echo "  - TypeScript: ✅ All error messages include 'Fix:' directive"
  echo "  - Haskell: ✅ All error messages include 'Fix:' directive"
  exit 0
else
  echo "❌ BANNED PATTERN DETECTED: Error messages without explicit format"
  echo ""
  echo "PROTOCOL VIOLATION: All error messages must include:"
  echo "  1. What went wrong (clear description)"
  echo "  2. Where it happened (location/context)"
  echo "  3. How to fix it (must include 'Fix:' or 'fix:' directive)"
  echo ""
  echo "Total violations found: $ERRORS"
  echo "  - Lean 4: $LEAN_ERRORS violations"
  echo "  - TypeScript: $TS_ERRORS violations"
  echo "  - Haskell: $HS_ERRORS violations"
  echo ""
  echo "Fix: Update all error messages to include explicit 'Fix:' directive"
  echo "     with clear instructions on how to resolve the issue."
  exit 1
fi
