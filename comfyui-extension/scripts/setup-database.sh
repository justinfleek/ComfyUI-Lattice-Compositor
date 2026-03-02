#!/bin/bash
# Setup DuckDB Database
# Creates database directory and initializes schema

set -e

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DB_DIR="$PROJECT_ROOT/.lattice"
DB_PATH="$DB_DIR/database.duckdb"

echo "Setting up DuckDB database..."

# Create database directory
mkdir -p "$DB_DIR"

# Check if DuckDB CLI is available
if command -v duckdb &> /dev/null; then
    echo "Using DuckDB CLI..."
    duckdb "$DB_PATH" < "$PROJECT_ROOT/scripts/init-database.sql"
    duckdb "$DB_PATH" < "$PROJECT_ROOT/scripts/init-feature-flags.sql"
    echo "✅ Database initialized successfully"
elif command -v node &> /dev/null && [ -d "$PROJECT_ROOT/node_modules/duckdb" ]; then
    echo "Using Node.js DuckDB package..."
    # Rebuild DuckDB native bindings if needed
    cd "$PROJECT_ROOT"
    npm rebuild duckdb || {
        echo "⚠️  DuckDB native bindings need to be rebuilt"
        echo "Run: npm rebuild duckdb"
        exit 1
    }
    node scripts/init-database.js
else
    echo "❌ DuckDB not found. Install DuckDB CLI or Node.js package:"
    echo "  - CLI: https://duckdb.org/docs/installation/"
    echo "  - Node: npm install duckdb"
    exit 1
fi

echo "Database ready at: $DB_PATH"
