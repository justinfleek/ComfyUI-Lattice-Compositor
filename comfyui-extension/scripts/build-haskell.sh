#!/usr/bin/env bash
# Build entire Lattice Haskell library (src/lattice). Run from repo root.
# Usage: ./scripts/build-haskell.sh
set -e
cd "$(dirname "$0")/.."
cabal build
