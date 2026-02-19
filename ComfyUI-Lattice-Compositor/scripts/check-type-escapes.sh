#!/usr/bin/env bash
# check-type-escapes.sh
#
# Check for type escapes across the codebase
# BANNED: any, unknown without guards, unsafeCoerce, as any, as unknown as
#
# Exit code: 0 if no violations, 1 if violations found

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

VIOLATIONS=0

echo "Checking for type escapes..."

# ============================================================================
# TYPESCRIPT TYPE ESCAPES
# ============================================================================

echo "Checking TypeScript files..."

# Check for 'any' type
if grep -r --include="*.ts" --include="*.tsx" ":\s*any\b\|:\s*any\[\]\|:\s*any\s*\|<any>" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "//.*any" | grep -v "test.*any"; then
  echo "❌ ERROR: Found 'any' type in TypeScript code"
  grep -rn --include="*.ts" --include="*.tsx" ":\s*any\b\|:\s*any\[\]\|:\s*any\s*\|<any>" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "//.*any" | grep -v "test.*any"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for 'unknown' without guards (this is a heuristic - may need refinement)
if grep -r --include="*.ts" --include="*.tsx" ":\s*unknown\b" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "//.*unknown" | grep -v "test.*unknown" | grep -v "if.*unknown\|case.*unknown\|typeof.*unknown"; then
  echo "⚠️  WARNING: Found 'unknown' type without obvious guards in TypeScript code"
  # This is a warning - unknown can be legitimate with proper guards
fi

# Check for 'as any' or 'as unknown as'
if grep -r --include="*.ts" --include="*.tsx" "as\s+any\|as\s+unknown\s+as" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "//.*as.*any\|//.*as.*unknown"; then
  echo "❌ ERROR: Found 'as any' or 'as unknown as' (type assertions) in TypeScript code"
  grep -rn --include="*.ts" --include="*.tsx" "as\s+any\|as\s+unknown\s+as" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./" | grep -v "//.*as.*any\|//.*as.*unknown"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for @ts-ignore or @ts-expect-error
if grep -r --include="*.ts" --include="*.tsx" "@ts-ignore\|@ts-expect-error" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"; then
  echo "❌ ERROR: Found '@ts-ignore' or '@ts-expect-error' in TypeScript code"
  grep -rn --include="*.ts" --include="*.tsx" "@ts-ignore\|@ts-expect-error" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# ============================================================================
# PURESCRIPT TYPE ESCAPES
# ============================================================================

echo "Checking PureScript files..."

# Check for unsafeCoerce
if grep -r --include="*.purs" "unsafeCoerce" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"; then
  echo "❌ ERROR: Found 'unsafeCoerce' in PureScript code"
  grep -rn --include="*.purs" "unsafeCoerce" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# ============================================================================
# HASKELL TYPE ESCAPES
# ============================================================================

echo "Checking Haskell files..."

# Check for unsafeCoerce
if grep -r --include="*.hs" "unsafeCoerce" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"; then
  echo "❌ ERROR: Found 'unsafeCoerce' in Haskell code"
  grep -rn --include="*.hs" "unsafeCoerce" "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" 2>/dev/null | grep -v "^Binary" | grep -v "^\./"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# ============================================================================
# SUMMARY
# ============================================================================

if [ $VIOLATIONS -eq 0 ]; then
  echo "✅ No type escapes found"
  exit 0
else
  echo "❌ Found $VIOLATIONS violation(s)"
  exit 1
fi
