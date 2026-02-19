#!/usr/bin/env bash
# check-file-size.sh
#
# Check that all files are under 500 lines
# REQUIRED: All files <500 lines (enforced by architecture)
#
# Exit code: 0 if no violations, 1 if violations found

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

MAX_LINES=500
VIOLATIONS=0

echo "Checking file sizes (max $MAX_LINES lines)..."

# ============================================================================
# FILE SIZE CHECKS
# ============================================================================

# Check Haskell files
echo "Checking Haskell files..."
while IFS= read -r -d '' file; do
  lines=$(wc -l < "$file" 2>/dev/null || echo "0")
  if [ "$lines" -gt "$MAX_LINES" ]; then
    echo "❌ ERROR: $file exceeds $MAX_LINES lines ($lines lines)"
    VIOLATIONS=$((VIOLATIONS + 1))
  fi
done < <(find "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" -name "*.hs" -type f -print0 2>/dev/null)

# Check PureScript files
echo "Checking PureScript files..."
while IFS= read -r -d '' file; do
  lines=$(wc -l < "$file" 2>/dev/null || echo "0")
  if [ "$lines" -gt "$MAX_LINES" ]; then
    echo "❌ ERROR: $file exceeds $MAX_LINES lines ($lines lines)"
    VIOLATIONS=$((VIOLATIONS + 1))
  fi
done < <(find "$PROJECT_ROOT/src" "$PROJECT_ROOT/test" -name "*.purs" -type f -print0 2>/dev/null)

# Check TypeScript files
echo "Checking TypeScript files..."
while IFS= read -r -d '' file; do
  lines=$(wc -l < "$file" 2>/dev/null || echo "0")
  if [ "$lines" -gt "$MAX_LINES" ]; then
    echo "❌ ERROR: $file exceeds $MAX_LINES lines ($lines lines)"
    VIOLATIONS=$((VIOLATIONS + 1))
  fi
done < <(find "$PROJECT_ROOT/ui/src" -name "*.ts" -o -name "*.tsx" -type f -print0 2>/dev/null)

# Check Lean4 files
echo "Checking Lean4 files..."
while IFS= read -r -d '' file; do
  lines=$(wc -l < "$file" 2>/dev/null || echo "0")
  if [ "$lines" -gt "$MAX_LINES" ]; then
    echo "❌ ERROR: $file exceeds $MAX_LINES lines ($lines lines)"
    VIOLATIONS=$((VIOLATIONS + 1))
  fi
done < <(find "$PROJECT_ROOT/lattice-core/lean" -name "*.lean" -type f -print0 2>/dev/null | grep -v "\.lake" || true)

# ============================================================================
# SUMMARY
# ============================================================================

if [ $VIOLATIONS -eq 0 ]; then
  echo "✅ All files are under $MAX_LINES lines"
  exit 0
else
  echo "❌ Found $VIOLATIONS file(s) exceeding $MAX_LINES lines"
  echo ""
  echo "Suggestions:"
  echo "  - Split large files into smaller modules"
  echo "  - Extract helper functions to separate files"
  echo "  - Use type classes/protocols to reduce duplication"
  exit 1
fi
