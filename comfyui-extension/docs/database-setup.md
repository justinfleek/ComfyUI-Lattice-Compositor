# Database Setup Guide

> **Purpose:** Step-by-step guide to set up DuckDB database
> **Last Updated:** 2026-01-23

---

## Quick Start

### Option 1: DuckDB CLI (Recommended)

```bash
# Install DuckDB CLI
# Windows: Download from https://duckdb.org/docs/installation/
# Linux/Mac: brew install duckdb or apt install duckdb

# Initialize database
bash scripts/setup-database.sh
```

### Option 2: Node.js DuckDB Package

```bash
# Install dependencies
npm install

# Rebuild native bindings (required for DuckDB)
npm rebuild duckdb

# Initialize database
npm run init-db
```

---

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│              TypeScript UI Layer                            │
│  - chatDatabase.ts (calls HTTP service)                    │
│  - featureFlagsStore.ts (reads from DB)                    │
└─────────────────────────────────────────────────────────────┘
                          │
                          ▼ HTTP
┌─────────────────────────────────────────────────────────────┐
│              Python HTTP Service                            │
│  - http_service.py (exposes FFI functions)                 │
└─────────────────────────────────────────────────────────────┘
                          │
                          ▼ FFI
┌─────────────────────────────────────────────────────────────┐
│              Haskell FFI Layer                              │
│  - DatabaseFFI.hs (C exports)                              │
│  - Database/DuckDB.hs (connection wrapper)                  │
│  - Database/ChatMessages.hs (CRUD operations)              │
└─────────────────────────────────────────────────────────────┘
                          │
                          ▼ Native
┌─────────────────────────────────────────────────────────────┐
│              DuckDB Database                                │
│  - .lattice/database.duckdb                                 │
│  - All tables, indexes, views                               │
└─────────────────────────────────────────────────────────────┘
```

---

## Current Status

✅ **Complete:**
- Database schema defined (`docs/DATABASE_SCHEMA.md`)
- SQL initialization scripts (`scripts/init-database.sql`, `scripts/init-feature-flags.sql`)
- Haskell database modules (`src/lattice/Database/*.hs`)
- FFI wrapper (`src/lattice/FFI/DatabaseFFI.hs`)
- TypeScript interface (`ui/src/services/chatDatabase.ts`)
- MCP server (`scripts/mcp-server.js`)
- Feature flags store (`ui/src/stores/featureFlagsStore.ts`)

⚠️ **Needs Implementation:**
- DuckDB Haskell bindings (currently placeholder)
- Native DuckDB Node.js bindings (need rebuild)
- Wire HTTP service to DatabaseFFI functions
- Migrate IndexedDB → DuckDB

---

## Next Steps

1. **Add DuckDB Haskell Package**
   - Add to `nix/packages/lattice-ffi.nix` dependencies
   - Or use `duckdb-haskell` package

2. **Wire HTTP Service**
   - Add database endpoints to `http_service.py`
   - Map to DatabaseFFI functions

3. **Test Database**
   - Initialize database
   - Test CRUD operations
   - Verify MCP server queries

4. **Migrate Data**
   - Read from IndexedDB
   - Write to DuckDB
   - Verify integrity

---

*Setup Guide Version: 1.0*
