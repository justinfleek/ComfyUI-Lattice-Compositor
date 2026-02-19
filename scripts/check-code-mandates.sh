#!/usr/bin/env bash
# check-code-mandates.sh
#
# Enforces the 7 core code mandates:
# 1. Literate programming style - Extensive documentation for LLM/dev comprehension
# 2. Total functions - No partial functions, all cases handled
# 3. Bounded polymorphism - All generics have explicit bounds
# 4. Named constants - No magic numbers
# 5. Split functions - Under 50 lines each
# 6. Typed dicts - Full parameterization, no bare dict
# 7. Security wired - Input sanitization + output filtering
#
# Exit code: 0 if all mandates pass, 1 if violations found

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

VIOLATIONS=0
WARNINGS=0

echo "=========================================="
echo "CODE MANDATE VERIFICATION"
echo "=========================================="
echo ""

# ============================================================================
# MANDATE 1: Literate Programming Style
# ============================================================================
echo "MANDATE 1: Checking literate programming style..."

UNDOCUMENTED_FUNCTIONS=0

# TypeScript/PureScript: Check for JSDoc comments
TS_FILES=$(find "$PROJECT_ROOT/ui/src" -name "*.ts" -o -name "*.tsx" 2>/dev/null | head -30)
for file in $TS_FILES; do
  if [ -f "$file" ]; then
    FUNCTIONS=$(grep -n "^[[:space:]]*\(export[[:space:]]\+\)\?\(async[[:space:]]\+\)\?function\|^[[:space:]]*\(export[[:space:]]\+\)\?const[[:space:]]\+[a-zA-Z_][a-zA-Z0-9_]*[[:space:]]*[:=][[:space:]]*\(async[[:space:]]\+\)\?(" "$file" 2>/dev/null || true)
    while IFS= read -r func_line; do
      if [ -n "$func_line" ]; then
        LINE_NUM=$(echo "$func_line" | cut -d: -f1)
        PREV_LINES=$(sed -n "$((LINE_NUM - 3)),$((LINE_NUM - 1))p" "$file" 2>/dev/null || echo "")
        if ! echo "$PREV_LINES" | grep -q "/\*\*\|/\*"; then
          UNDOCUMENTED_FUNCTIONS=$((UNDOCUMENTED_FUNCTIONS + 1))
          if [ $UNDOCUMENTED_FUNCTIONS -le 10 ]; then
            echo "  ⚠️  $file:$LINE_NUM - Function missing JSDoc documentation"
          fi
        fi
      fi
    done <<< "$FUNCTIONS"
  fi
done

# Haskell: Check for Haddock comments (-- | or -- ^)
HS_FILES=$(find "$PROJECT_ROOT/src" -name "*.hs" 2>/dev/null | grep -v ".stack-work\|dist\|cabal" | head -20)
for file in $HS_FILES; do
  if [ -f "$file" ]; then
    # Check for exported functions without Haddock comments
    EXPORTED=$(grep -n "^[[:space:]]*[a-zA-Z_][a-zA-Z0-9_']*[[:space:]]*::" "$file" 2>/dev/null || true)
    while IFS= read -r func_line; do
      if [ -n "$func_line" ]; then
        LINE_NUM=$(echo "$func_line" | cut -d: -f1)
        PREV_LINES=$(sed -n "$((LINE_NUM - 5)),$((LINE_NUM - 1))p" "$file" 2>/dev/null || echo "")
        if ! echo "$PREV_LINES" | grep -q "^[[:space:]]*--\s*|\|^[[:space:]]*--\s*\^"; then
          UNDOCUMENTED_FUNCTIONS=$((UNDOCUMENTED_FUNCTIONS + 1))
          if [ $UNDOCUMENTED_FUNCTIONS -le 10 ]; then
            echo "  ⚠️  $file:$LINE_NUM - Function missing Haddock documentation"
          fi
        fi
      fi
    done <<< "$EXPORTED"
  fi
done

# Lean4: Check for docstrings (/-- ... --/)
LEAN_FILES=$(find "$PROJECT_ROOT/standalone/lattice-core/lean" -name "*.lean" 2>/dev/null | grep -v ".lake\|build" | head -20)
for file in $LEAN_FILES; do
  if [ -f "$file" ]; then
    # Check for def/theorem without docstring
    DEFS=$(grep -n "^[[:space:]]*\(def\|theorem\|structure\|class\|instance\)[[:space:]]\+[a-zA-Z_]" "$file" 2>/dev/null || true)
    while IFS= read -r def_line; do
      if [ -n "$def_line" ]; then
        LINE_NUM=$(echo "$def_line" | cut -d: -f1)
        PREV_LINES=$(sed -n "$((LINE_NUM - 5)),$((LINE_NUM - 1))p" "$file" 2>/dev/null || echo "")
        if ! echo "$PREV_LINES" | grep -q "^[[:space:]]*/--"; then
          UNDOCUMENTED_FUNCTIONS=$((UNDOCUMENTED_FUNCTIONS + 1))
          if [ $UNDOCUMENTED_FUNCTIONS -le 10 ]; then
            echo "  ⚠️  $file:$LINE_NUM - Definition missing docstring (/-- ... --/)"
          fi
        fi
      fi
    done <<< "$DEFS"
  fi
done

if [ $UNDOCUMENTED_FUNCTIONS -gt 0 ]; then
  echo "  ❌ Found $UNDOCUMENTED_FUNCTIONS undocumented function(s)"
  echo "     Fix: Add documentation (JSDoc for TS, Haddock for HS, /-- --/ for Lean)"
  WARNINGS=$((WARNINGS + 1))
else
  echo "  ✅ All functions documented"
fi

echo ""

# ============================================================================
# MANDATE 2: Total Functions - No Partial Functions
# ============================================================================
echo "MANDATE 2: Checking for total functions (no partial functions)..."

# Check for banned partial patterns
PARTIAL_VIOLATIONS=0

# TypeScript: Check for non-null assertions (!), optional chaining without explicit handling
if grep -rn --include="*.ts" --include="*.tsx" "!\s*[a-zA-Z_]" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "//.*!" | grep -v "test.*!" | head -20 | while read -r line; do
  echo "  ❌ $line - Non-null assertion (!) detected"
  PARTIAL_VIOLATIONS=$((PARTIAL_VIOLATIONS + 1))
done; then
  true
fi

# Check for optional chaining without explicit null handling
if grep -rn --include="*.ts" --include="*.tsx" "?\.\w\+" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "//.*?" | grep -v "test.*?" | head -20 | while read -r line; do
  echo "  ⚠️  $line - Optional chaining without explicit null handling"
  PARTIAL_VIOLATIONS=$((PARTIAL_VIOLATIONS + 1))
done; then
  true
fi

# Haskell: Check for head/tail/fromJust/undefined/error
if grep -rn --include="*.hs" "\bhead\b\|\btail\b\|\bfromJust\b\|\bundefined\b\|\berror\s" "$PROJECT_ROOT/src" 2>/dev/null | grep -v "import.*head\|import.*tail\|import.*fromJust\|import.*undefined\|import.*error" | grep -v "^Binary\|\.stack-work\|dist\|cabal" | head -20 | while read -r line; do
  echo "  ❌ $line - Partial function detected (head/tail/fromJust/undefined/error)"
  PARTIAL_VIOLATIONS=$((PARTIAL_VIOLATIONS + 1))
done; then
  true
fi

# Lean4: Check for sorry (incomplete proofs)
if grep -rn --include="*.lean" "\bsorry\b" "$PROJECT_ROOT/standalone/lattice-core/lean" 2>/dev/null | grep -v ".lake\|build\|test" | head -20 | while read -r line; do
  echo "  ❌ $line - Incomplete proof (sorry) detected"
  PARTIAL_VIOLATIONS=$((PARTIAL_VIOLATIONS + 1))
done; then
  true
fi

# PureScript: Check for unsafeCoerce/unsafePartial
if grep -rn --include="*.purs" "unsafeCoerce\|unsafePartial" "$PROJECT_ROOT/src" 2>/dev/null | grep -v "import.*unsafe\|test\|spec" | head -20 | while read -r line; do
  echo "  ❌ $line - Unsafe coercion detected (unsafeCoerce/unsafePartial)"
  PARTIAL_VIOLATIONS=$((PARTIAL_VIOLATIONS + 1))
done; then
  true
fi

if [ $PARTIAL_VIOLATIONS -gt 0 ]; then
  echo "  ❌ Found $PARTIAL_VIOLATIONS partial function violation(s)"
  VIOLATIONS=$((VIOLATIONS + 1))
else
  echo "  ✅ No partial functions detected"
fi

echo ""

# ============================================================================
# MANDATE 3: Bounded Polymorphism
# ============================================================================
echo "MANDATE 3: Checking bounded polymorphism..."

UNBOUNDED_GENERICS=0

# TypeScript: Check for unconstrained generics
if grep -rn --include="*.ts" --include="*.tsx" "<T>" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "extends\|//.*<T>\|test\|spec" | head -20 | while read -r line; do
  echo "  ⚠️  $line - Unbounded generic type parameter"
  UNBOUNDED_GENERICS=$((UNBOUNDED_GENERICS + 1))
done; then
  true
fi

# Haskell: Check for unconstrained type variables (simplified check)
if grep -rn --include="*.hs" "::[[:space:]]*[a-z][a-zA-Z0-9']*[[:space:]]*->" "$PROJECT_ROOT/src" 2>/dev/null | grep -v "import\|test\|spec\|\.stack-work\|dist\|cabal" | grep -v "::.*=>" | head -20 | while read -r line; do
  echo "  ⚠️  $line - Unbounded type variable (may need constraints)"
  UNBOUNDED_GENERICS=$((UNBOUNDED_GENERICS + 1))
done; then
  true
fi

# PureScript: Check for unconstrained type variables
if grep -rn --include="*.purs" "::[[:space:]]*forall[[:space:]]*[a-z]" "$PROJECT_ROOT/src" 2>/dev/null | grep -v "import\|test\|spec\|=>" | head -20 | while read -r line; do
  echo "  ⚠️  $line - Unbounded type variable (may need constraints)"
  UNBOUNDED_GENERICS=$((UNBOUNDED_GENERICS + 1))
done; then
  true
fi

if [ $UNBOUNDED_GENERICS -gt 0 ]; then
  echo "  ⚠️  Found $UNBOUNDED_GENERICS unbounded generic(s)"
  echo "     Fix: Add explicit bounds/constraints to type parameters"
  WARNINGS=$((WARNINGS + 1))
else
  echo "  ✅ All generics have explicit bounds"
fi

echo ""

# ============================================================================
# MANDATE 4: Named Constants - No Magic Numbers
# ============================================================================
echo "MANDATE 4: Checking for magic numbers..."

MAGIC_NUMBERS=0

# TypeScript: Check for bare numeric literals (excluding 0, 1, -1)
if grep -rn --include="*.ts" --include="*.tsx" "[^a-zA-Z_0-9]\b[2-9][0-9]\+\b\|[^a-zA-Z_0-9]\b[1-9][0-9][0-9]\+\b" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "test\|spec\|//.*[0-9]" | head -20 | while read -r line; do
  if ! echo "$line" | grep -qE "(test|spec|version|date|timestamp|id|index|offset|const|CONST)" -i; then
    echo "  ⚠️  $line - Magic number detected"
    MAGIC_NUMBERS=$((MAGIC_NUMBERS + 1))
  fi
done; then
  true
fi

# Haskell: Check for numeric literals (excluding 0, 1, -1)
if grep -rn --include="*.hs" "\b[2-9][0-9]\+\b\|\b[1-9][0-9][0-9]\+\b" "$PROJECT_ROOT/src" 2>/dev/null | grep -v "import\|test\|spec\|\.stack-work\|dist\|cabal\|--.*[0-9]" | head -20 | while read -r line; do
  if ! echo "$line" | grep -qE "(test|spec|version|date|timestamp|id|index|offset|const|CONST|where|let)" -i; then
    echo "  ⚠️  $line - Magic number detected"
    MAGIC_NUMBERS=$((MAGIC_NUMBERS + 1))
  fi
done; then
  true
fi

if [ $MAGIC_NUMBERS -gt 0 ]; then
  echo "  ⚠️  Found $MAGIC_NUMBERS magic number(s)"
  echo "     Fix: Extract to named constant with descriptive name"
  WARNINGS=$((WARNINGS + 1))
else
  echo "  ✅ No magic numbers detected"
fi

echo ""

# ============================================================================
# MANDATE 5: Split Functions - Under 50 Lines Each
# ============================================================================
echo "MANDATE 5: Checking function length (max 50 lines)..."

LONG_FUNCTIONS=0

# TypeScript: Check function length
for file in $(find "$PROJECT_ROOT/ui/src" -name "*.ts" -o -name "*.tsx" 2>/dev/null | head -30); do
  if [ -f "$file" ]; then
    awk '
      /^[[:space:]]*(export[[:space:]]+)?(async[[:space:]]+)?function|^[[:space:]]*(export[[:space:]]+)?const[[:space:]]+[a-zA-Z_][a-zA-Z0-9_]*[[:space:]]*[:=][[:space:]]*(async[[:space:]]+)?\(/ {
        func_start = NR
        brace_count = 0
        in_function = 1
      }
      in_function {
        brace_count += gsub(/{/, "")
        brace_count -= gsub(/}/, "")
        if (brace_count == 0 && func_start > 0) {
          func_length = NR - func_start
          if (func_length > 50) {
            print FILENAME ":" func_start " - Function exceeds 50 lines (" func_length " lines)"
          }
          func_start = 0
          in_function = 0
        }
      }
    ' "$file" 2>/dev/null | head -10 | while read -r line; do
      echo "  ⚠️  $line"
      LONG_FUNCTIONS=$((LONG_FUNCTIONS + 1))
    done
  fi
done

# Haskell: Check function length (simplified - counts lines between :: and where/=
for file in $(find "$PROJECT_ROOT/src" -name "*.hs" 2>/dev/null | grep -v ".stack-work\|dist\|cabal" | head -20); do
  if [ -f "$file" ]; then
    awk '
      /^[[:space:]]*[a-zA-Z_][a-zA-Z0-9'\'']*[[:space:]]*::/ {
        func_start = NR
        in_function = 1
      }
      in_function && /^[[:space:]]*[a-zA-Z_][a-zA-Z0-9'\'']*[[:space:]]*[=]|^[[:space:]]*where|^[[:space:]]*$|^[[:space:]]*--/ {
        if (func_start > 0 && NR > func_start) {
          func_length = NR - func_start
          if (func_length > 50) {
            print FILENAME ":" func_start " - Function exceeds 50 lines (" func_length " lines)"
          }
          func_start = 0
          in_function = 0
        }
      }
    ' "$file" 2>/dev/null | head -10 | while read -r line; do
      echo "  ⚠️  $line"
      LONG_FUNCTIONS=$((LONG_FUNCTIONS + 1))
    done
  fi
done

if [ $LONG_FUNCTIONS -gt 0 ]; then
  echo "  ⚠️  Found $LONG_FUNCTIONS function(s) exceeding 50 lines"
  echo "     Fix: Split into smaller, focused functions"
  WARNINGS=$((WARNINGS + 1))
else
  echo "  ✅ All functions under 50 lines"
fi

echo ""

# ============================================================================
# MANDATE 6: Typed Dicts - Full Parameterization
# ============================================================================
echo "MANDATE 6: Checking typed dictionaries..."

BARE_DICTS=0

# TypeScript: Check for Record<string, any> or untyped object literals
if grep -rn --include="*.ts" --include="*.tsx" "Record<string,\s*any>\|:\s*{\s*}\|:\s*object\|:\s*Object" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "test\|spec\|//.*Record" | head -20 | while read -r line; do
  echo "  ❌ $line - Bare/untyped dictionary detected"
  BARE_DICTS=$((BARE_DICTS + 1))
done; then
  true
fi

# Check for untyped object parameters
if grep -rn --include="*.ts" --include="*.tsx" "\(function\|const\|=>\)[^(]*\([a-zA-Z_][a-zA-Z0-9_]*:\s*{\s*}\|:\s*object\)" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "test\|spec\|//.*:" | head -20 | while read -r line; do
  echo "  ⚠️  $line - Untyped object parameter"
  BARE_DICTS=$((BARE_DICTS + 1))
done; then
  true
fi

if [ $BARE_DICTS -gt 0 ]; then
  echo "  ❌ Found $BARE_DICTS bare/untyped dictionary violation(s)"
  echo "     Fix: Use fully parameterized types: Record<string, SpecificType>"
  VIOLATIONS=$((VIOLATIONS + 1))
else
  echo "  ✅ All dictionaries fully typed"
fi

echo ""

# ============================================================================
# MANDATE 7: Security Wired - Input Sanitization + Output Filtering
# ============================================================================
echo "MANDATE 7: Checking security (input sanitization + output filtering)..."

SECURITY_VIOLATIONS=0

# Check for user input handling without sanitization
if grep -rn --include="*.ts" --include="*.tsx" "event\.target\.value\|req\.body\|req\.query\|req\.params" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "sanitize\|validate\|escape\|test\|spec" | head -20 | while read -r line; do
  echo "  ⚠️  $line - User input without explicit sanitization"
  SECURITY_VIOLATIONS=$((SECURITY_VIOLATIONS + 1))
done; then
  true
fi

# Check for innerHTML without sanitization
if grep -rn --include="*.ts" --include="*.tsx" "innerHTML\s*=" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "sanitize\|DOMPurify\|test\|spec" | head -20 | while read -r line; do
  echo "  ❌ $line - innerHTML assignment without sanitization"
  SECURITY_VIOLATIONS=$((SECURITY_VIOLATIONS + 1))
done; then
  true
fi

# Check for eval or Function constructor
if grep -rn --include="*.ts" --include="*.tsx" "\beval\s*(\|\bnew\s+Function\s*(" "$PROJECT_ROOT/ui/src" 2>/dev/null | grep -v "test\|spec\|//.*eval" | head -20 | while read -r line; do
  echo "  ❌ $line - eval() or Function() constructor detected"
  SECURITY_VIOLATIONS=$((SECURITY_VIOLATIONS + 1))
done; then
  true
fi

# Haskell: Check for unsafePerformIO without justification
if grep -rn --include="*.hs" "unsafePerformIO" "$PROJECT_ROOT/src" 2>/dev/null | grep -v "import\|test\|spec\|\.stack-work\|dist\|cabal\|--.*unsafe" | head -20 | while read -r line; do
  echo "  ⚠️  $line - unsafePerformIO detected (ensure proper justification)"
  SECURITY_VIOLATIONS=$((SECURITY_VIOLATIONS + 1))
done; then
  true
fi

# Lean4: Check for unsafe operations
if grep -rn --include="*.lean" "unsafe" "$PROJECT_ROOT/standalone/lattice-core/lean" 2>/dev/null | grep -v "import\|test\|\.lake\|build\|--.*unsafe" | head -20 | while read -r line; do
  echo "  ⚠️  $line - Unsafe operation detected (ensure proper justification)"
  SECURITY_VIOLATIONS=$((SECURITY_VIOLATIONS + 1))
done; then
  true
fi

if [ $SECURITY_VIOLATIONS -gt 0 ]; then
  echo "  ❌ Found $SECURITY_VIOLATIONS security violation(s)"
  echo "     Fix: Add input sanitization and output filtering"
  VIOLATIONS=$((VIOLATIONS + 1))
else
  echo "  ✅ Security checks passed"
fi

echo ""

# ============================================================================
# SUMMARY
# ============================================================================
echo "=========================================="
echo "SUMMARY"
echo "=========================================="
echo "Violations (blocking): $VIOLATIONS"
echo "Warnings (non-blocking): $WARNINGS"
echo ""

if [ $VIOLATIONS -eq 0 ] && [ $WARNINGS -eq 0 ]; then
  echo "✅ All code mandates satisfied"
  exit 0
elif [ $VIOLATIONS -eq 0 ]; then
  echo "⚠️  Some warnings found, but no blocking violations"
  exit 0
else
  echo "❌ Code mandate violations found - CI will fail"
  exit 1
fi
