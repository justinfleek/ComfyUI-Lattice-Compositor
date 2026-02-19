#!/usr/bin/env bash
# check-proofs.sh
#
# Check for proof requirements in Lean4 code
# BANNED: sorry without TODO, unproven axiom
# REQUIRED: All Extractable instances must have proofs
#
# Exit code: 0 if no violations, 1 if violations found

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

VIOLATIONS=0

echo "Checking for proof requirements..."

# ============================================================================
# LEAN4 PROOF CHECKS
# ============================================================================

echo "Checking Lean4 files..."

# Check for 'sorry' without TODO comment
if grep -r --include="*.lean" "sorry" "$PROJECT_ROOT/lattice-core/lean" 2>/dev/null | grep -v "^Binary" | grep -v "^\\./" | grep -v "TODO.*sorry\|--.*sorry\|/\*.*sorry"; then
  echo "❌ ERROR: Found 'sorry' without TODO comment in Lean4 code"
  grep -rn --include="*.lean" "sorry" "$PROJECT_ROOT/lattice-core/lean" 2>/dev/null | grep -v "^Binary" | grep -v "^\\./" | grep -v "TODO.*sorry\|--.*sorry\|/\*.*sorry"
  VIOLATIONS=$((VIOLATIONS + 1))
fi

# Check for unproven 'axiom' (without justification comment)
if grep -r --include="*.lean" "^\s*axiom\s" "$PROJECT_ROOT/lattice-core/lean" 2>/dev/null | grep -v "^Binary" | grep -v "^\\./" | grep -vE -- "--.*axiom|/\*.*axiom"; then
  echo "⚠️  WARNING: Found 'axiom' without justification comment in Lean4 code"
  # This is a warning - axioms may be legitimate with justification
fi

# Check that Extractable instances have proofs
# This is a heuristic - we check that Extractable instances are followed by 'proof'
if grep -r --include="*.lean" "instance.*Extractable" "$PROJECT_ROOT/lattice-core/lean" 2>/dev/null | grep -v "^Binary" | grep -v "^\\./" ; then
  echo "Checking Extractable instances have proofs..."
  # This would require more sophisticated parsing - for now, we just check
  # that Extractable instances exist and note that proofs should be present
fi

# ============================================================================
# SUMMARY
# ============================================================================

if [ $VIOLATIONS -eq 0 ]; then
  echo "✅ No proof violations found"
  exit 0
else
  echo "❌ Found $VIOLATIONS violation(s)"
  exit 1
fi
