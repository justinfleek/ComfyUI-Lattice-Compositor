#!/bin/bash
# Install Playwright browsers for E2E testing
# Run this once in the Nix dev shell

set -e

echo "=========================================="
echo "Installing Playwright Browsers"
echo "=========================================="
echo ""

cd "$(dirname "$0")/.."

# Check if we're in Nix shell
if [ -z "$NIX_SHELL" ] && [ -z "$IN_NIX_SHELL" ]; then
    echo "⚠️  Not in Nix shell. Enter with: nix develop"
    echo "   Then run: bash scripts/install-playwright-browsers.sh"
    exit 1
fi

echo "Installing Chromium browser for Playwright..."
npx playwright install chromium

echo ""
echo "Installing system dependencies (if needed)..."
npx playwright install-deps chromium || echo "⚠️  Some dependencies may need manual installation"

echo ""
echo "=========================================="
echo "✅ Playwright browsers installed!"
echo "=========================================="
echo ""
echo "You can now run E2E tests with:"
echo "  npm run test:playwright"
echo ""
