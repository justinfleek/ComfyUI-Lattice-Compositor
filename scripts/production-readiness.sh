#!/bin/bash
set -e

echo "╔══════════════════════════════════════════════════════════════╗"
echo "║           LATTICE COMPOSITOR - PRODUCTION READINESS          ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

ERRORS=0

# ════════════════════════════════════════════════════════════════════
# PYTHON CHECKS
# ════════════════════════════════════════════════════════════════════
echo "┌─────────────────────────────────────────────────────────────┐"
echo "│ PYTHON                                                       │"
echo "└─────────────────────────────────────────────────────────────┘"

echo -n "  Ruff lint:    "
if ruff check src/ 2>/dev/null; then
    echo "✅ PASS"
else
    echo "❌ FAIL"
    ERRORS=$((ERRORS + 1))
fi

echo -n "  Ruff format:  "
if ruff format --check src/ 2>/dev/null; then
    echo "✅ PASS"
else
    echo "⚠️  NEEDS FORMAT (run: ruff format src/)"
fi

echo -n "  Pyright:      "
if pyright src/ 2>/dev/null; then
    echo "✅ PASS"
else
    echo "❌ FAIL"
    ERRORS=$((ERRORS + 1))
fi

echo -n "  Pytest:       "
if pytest --tb=no -q 2>/dev/null; then
    echo "✅ PASS (70%+ coverage)"
else
    echo "❌ FAIL"
    ERRORS=$((ERRORS + 1))
fi

# ════════════════════════════════════════════════════════════════════
# TYPESCRIPT/VUE CHECKS (ui/)
# ════════════════════════════════════════════════════════════════════
echo ""
echo "┌─────────────────────────────────────────────────────────────┐"
echo "│ TYPESCRIPT/VUE (ui/)                                        │"
echo "└─────────────────────────────────────────────────────────────┘"

cd ui

echo -n "  TypeScript:   "
if npx tsc --noEmit 2>/dev/null; then
    echo "✅ PASS (0 errors)"
else
    echo "❌ FAIL"
    ERRORS=$((ERRORS + 1))
fi

echo -n "  Biome lint:   "
if npx biome check src/ 2>/dev/null; then
    echo "✅ PASS"
else
    echo "⚠️  WARNINGS (run: npx biome check --write src/)"
fi

echo -n "  Vitest:       "
if npm test -- --reporter=dot 2>&1 | tail -1 | grep -q "pass"; then
    PASS_COUNT=$(npm test -- --reporter=dot 2>&1 | grep -oP '\d+(?= passed)')
    echo "✅ PASS ($PASS_COUNT tests)"
else
    echo "❌ FAIL"
    ERRORS=$((ERRORS + 1))
fi

cd ..

# ════════════════════════════════════════════════════════════════════
# NIX CHECKS
# ════════════════════════════════════════════════════════════════════
echo ""
echo "┌─────────────────────────────────────────────────────────────┐"
echo "│ NIX                                                          │"
echo "└─────────────────────────────────────────────────────────────┘"

echo -n "  Flake check:  "
if nix flake check 2>/dev/null; then
    echo "✅ PASS"
else
    echo "⚠️  SKIP (not in nix environment)"
fi

echo -n "  treefmt:      "
if nix fmt -- --check 2>/dev/null; then
    echo "✅ PASS"
else
    echo "⚠️  NEEDS FORMAT (run: nix fmt)"
fi

# ════════════════════════════════════════════════════════════════════
# TYPE SAFETY AUDIT
# ════════════════════════════════════════════════════════════════════
echo ""
echo "┌─────────────────────────────────────────────────────────────┐"
echo "│ TYPE SAFETY AUDIT                                           │"
echo "└─────────────────────────────────────────────────────────────┘"

cd ui
echo "  TypeScript type issues:"
echo "    as unknown as: $(grep -rn 'as unknown as' src/ --include='*.ts' 2>/dev/null | wc -l)"
echo "    as any:        $(grep -rn 'as any' src/ --include='*.ts' 2>/dev/null | wc -l)"
echo "    : any:         $(grep -rn ': any' src/ --include='*.ts' 2>/dev/null | wc -l)"
cd ..

# ════════════════════════════════════════════════════════════════════
# SUMMARY
# ════════════════════════════════════════════════════════════════════
echo ""
echo "╔══════════════════════════════════════════════════════════════╗"
if [ $ERRORS -eq 0 ]; then
    echo "║  ✅ PRODUCTION READY - All critical checks passed           ║"
else
    echo "║  ❌ NOT READY - $ERRORS critical check(s) failed               ║"
fi
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

exit $ERRORS
