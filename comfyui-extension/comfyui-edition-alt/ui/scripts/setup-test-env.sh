#!/bin/bash
# Setup script for E2E test environment
# Ensures terminal size is correct and environment is ready

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"

# Fix terminal size for WSL
if [ -z "$COLUMNS" ] || [ "$COLUMNS" -gt 1000 ] || [ "$COLUMNS" -lt 10 ]; then
    export COLUMNS=120
fi

if [ -z "$LINES" ] || [ "$LINES" -lt 2 ] || [ "$LINES" -gt 1000 ]; then
    export LINES=30
fi

# Set stty if available
if command -v stty >/dev/null 2>&1; then
    stty cols $COLUMNS rows $LINES 2>/dev/null || true
fi

echo "✅ Test environment ready (terminal: ${COLUMNS}x${LINES})"

# Export for Playwright
export COLUMNS
export LINES
