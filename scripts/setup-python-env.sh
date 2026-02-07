#!/usr/bin/env bash
# One-command Python env: create .venv and install package (aiohttp, etc.) so IDE and type checker see real deps.
# Usage: bash scripts/setup-python-env.sh
# Then: Select .venv/bin/python as your Python interpreter in the IDE.

set -e
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
VENV="$PROJECT_ROOT/.venv"

if [ ! -d "$VENV" ]; then
  echo "Creating .venv..."
  python3 -m venv "$VENV"
fi

echo "Installing package (aiohttp, numpy, etc.)..."
"$VENV/bin/pip" install --upgrade pip -q
"$VENV/bin/pip" install -e "$PROJECT_ROOT" -q

echo "Done. Use .venv/bin/python as your IDE interpreter."
