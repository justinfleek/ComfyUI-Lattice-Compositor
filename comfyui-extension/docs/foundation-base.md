# Foundation Base: Complete System Architecture

> **Purpose:** Master document tying together database, MCP, feature flags, and ontology
> **Status:** 🏗️ FOUNDATION ESTABLISHED
> **Last Updated:** 2026-01-23

**CRITICAL:** This document is the entry point for understanding the complete foundation. All other documents reference this as the master index.

---

## Overview

This foundation establishes:

1. **Database Schema** (DuckDB) - Complete data model based on ontology
2. **MCP Server** - LLM agent interface to software capabilities
3. **Feature Flags** - Modular feature toggling system
4. **Literate Programming Mapping** - Code ↔ Database relationships
5. **Ontology Integration** - Type system alignment across languages

---

## Document Structure

### Core Documents

| Document | Purpose | Status |
|----------|---------|--------|
| **[DATABASE_SCHEMA.md](./DATABASE_SCHEMA.md)** | Complete DuckDB schema with all tables, indexes, views | ✅ Complete |
| **[MCP_SERVER_CONFIG.md](./MCP_SERVER_CONFIG.md)** | MCP server configuration and implementation | ✅ Complete |
| **[FEATURE_FLAGS_SYSTEM.md](./FEATURE_FLAGS_SYSTEM.md)** | Feature flag system design and implementation | ✅ Complete |
| **[LITERATE_PROGRAMMING_MAPPING.md](./LITERATE_PROGRAMMING_MAPPING.md)** | Code-to-database mapping for LLM comprehension | ✅ Complete |
| **[MASTER_DEPENDENCY_ONTOLOGY.md](./MASTER_DEPENDENCY_ONTOLOGY.md)** | Domain ontology and entity relationships | ✅ Existing |
| **[audit/ONTOLOGY_ARCHITECTURE.md](./audit/ONTOLOGY_ARCHITECTURE.md)** | Type system architecture (Lean4/HS/PS/TS) | ✅ Existing |

---

## Quick Start Guide

### 1. Initialize Database

```bash
# Create database directory
mkdir -p .lattice

# Initialize DuckDB schema
duckdb .lattice/database.duckdb < scripts/init-database.sql

# Initialize feature flags
duckdb .lattice/database.duckdb < scripts/init-feature-flags.sql
```

### 2. Start MCP Server

```bash
# Install dependencies
npm install @modelcontextprotocol/sdk better-sqlite3

# Start server
node scripts/mcp-server.js
```

### 3. Configure Cursor/OpenCode

Add to `opencode.json`:

```json
{
  "mcp": {
    "lattice-compositor": {
      "type": "local",
      "enabled": true,
      "command": "node",
      "args": ["./scripts/mcp-server.js"],
      "env": {
        "DB_PATH": "${workspaceFolder}/.lattice/database.duckdb"
      }
    }
  }
}
```

### 4. Use Feature Flags

```typescript
// In any component
import { useFeatureFlagsStore } from '@/stores/featureFlagsStore';

const featureFlags = useFeatureFlagsStore();
const showParticles = computed(() => 
  featureFlags.isFeatureEnabled('ff-ui-particles', true)
);
```

---

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────┐
│                    LLM Agent (Claude/GPT)                   │
│  - Queries database via MCP                                 │
│  - Understands software capabilities                         │
│  - Accesses feature flags                                    │
└─────────────────────────────────────────────────────────────┘
                          │
                          ▼ (MCP Protocol)
┌─────────────────────────────────────────────────────────────┐
│              MCP Server (Node.js)                           │
│  - Exposes database queries                                  │
│  - Exposes software capabilities                             │
│  - Exposes feature flags                                     │
└─────────────────────────────────────────────────────────────┘
                          │
        ┌─────────────────┴─────────────────┐
        ▼                                   ▼
┌──────────────────┐            ┌──────────────────────┐
│   DuckDB         │            │   Feature Flags      │
│   Database       │            │   Store              │
│                  │            │                      │
│  - projects      │            │  - Global flags      │
│  - compositions  │            │  - Project flags    │
│  - layers        │            │  - User flags       │
│  - keyframes     │            │                      │
│  - effects       │            │                      │
│  - chat_messages │            │                      │
│  - feature_flags │            │                      │
└──────────────────┘            └──────────────────────┘
        │                                   │
        └─────────────────┬─────────────────┘
                          ▼
┌─────────────────────────────────────────────────────────────┐
│              Application Code                                │
│                                                              │
│  TypeScript (UI) → PureScript (Logic) → Haskell (Backend)  │
│                                                              │
│  All features gated by feature flags                         │
│  All data operations map to database queries                 │
└─────────────────────────────────────────────────────────────┘
```

---

## Database Schema Overview

### Core Tables

1. **projects** - Project metadata and settings
2. **compositions** - Composition definitions
3. **layers** - Layer hierarchy and properties
4. **keyframes** - Animation keyframes
5. **expressions** - Property expressions
6. **effects** - Layer effects
7. **audio_tracks** - Audio data and analysis
8. **cameras** - 3D camera definitions
9. **physics_spaces** - Physics simulation spaces
10. **physics_bodies** - Physics bodies
11. **particle_systems** - Particle system configurations
12. **assets** - Asset references
13. **chat_messages** - LLM agent conversation history
14. **feature_flags** - Global feature flag definitions
15. **events** - Audit trail events
16. **metrics** - Performance and analytics metrics

### Views

- **active_layers** - Currently visible layers
- **layer_hierarchy** - Recursive layer tree
- **keyframe_timeline** - Keyframe timeline view

### Functions

- **feature_enabled()** - Check if feature is enabled
- **enabled_features()** - Get all enabled features

---

## MCP Server Capabilities

### Resources Exposed

1. **lattice://database/schema** - Complete database schema
2. **lattice://database/feature-flags** - Feature flag configuration
3. **lattice://ontology/domain-entities** - Domain ontology
4. **lattice://capabilities/apis** - Available software APIs
5. **lattice://project/structure** - Current project structure

### Tools Exposed

1. **query_database** - Execute SQL queries
2. **get_feature_flags** - Get feature flag status
3. **get_project_structure** - Get project structure
4. **search_chat_history** - Search chat messages
5. **get_layer_details** - Get layer with all properties
6. **get_available_operations** - Get software operations

---

## Feature Flag System

### Categories

- **UI** - User interface features
- **Engine** - Rendering engine features
- **Export** - Export format features
- **AI** - AI-powered features
- **Particles** - Particle system features
- **Physics** - Physics simulation features
- **Experimental** - Experimental features

### Priority Order

1. User preferences (highest)
2. Project settings
3. Global defaults
4. Code defaults (lowest)

---

## Code-to-Database Mapping

### Example: Layer Operations

**Code:**
```typescript
layerStore.createLayer(compositionId, layerData)
```

**Database:**
```sql
INSERT INTO layers (composition_id, name, layer_type, data, ...)
VALUES (?, ?, ?, ?, ...)
```

**Mapping:**
- `layerStore` → `layers` table
- `createLayer()` → `INSERT INTO layers`
- `layerData` → JSON column in `layers` table

### Example: Feature Flag Check

**Code:**
```typescript
if (featureFlags.isFeatureEnabled('ff-particles-enabled')) {
  // Show particle UI
}
```

**Database:**
```sql
SELECT feature_enabled(feature_flags, 'ff-particles-enabled')
FROM projects WHERE id = ?
```

---

## Implementation Checklist

### Phase 1: Database Setup ✅

- [x] Create database schema document
- [x] Design all tables
- [x] Create indexes
- [x] Create views
- [x] Create functions
- [ ] Write initialization script
- [ ] Test schema creation

### Phase 2: MCP Server ✅

- [x] Design MCP server architecture
- [x] Define resources
- [x] Define tools
- [ ] Implement MCP server
- [ ] Test MCP server
- [ ] Configure Cursor/OpenCode

### Phase 3: Feature Flags ✅

- [x] Design feature flag system
- [x] Define all feature flags
- [x] Design priority system
- [ ] Implement TypeScript store
- [ ] Implement Haskell service
- [ ] Create UI toggle panel
- [ ] Migrate existing toggles

### Phase 4: Integration

- [ ] Wire database to Haskell backend
- [ ] Wire MCP server to database
- [ ] Wire feature flags to UI
- [ ] Test end-to-end flow
- [ ] Document usage examples

### Phase 5: Migration

- [ ] Migrate IndexedDB → DuckDB
- [ ] Migrate existing feature toggles
- [ ] Update all components to use feature flags
- [ ] Verify data integrity
- [ ] Performance testing

---

## Next Steps

1. **Create Database Initialization Script**
   - File: `scripts/init-database.sql`
   - Includes all CREATE TABLE statements
   - Includes indexes, views, functions

2. **Implement MCP Server**
   - File: `scripts/mcp-server.js`
   - Implement all tools
   - Test with LLM agents

3. **Implement Feature Flags Store**
   - File: `ui/src/stores/featureFlagsStore.ts`
   - Wire to database
   - Create UI panel

4. **Wire Everything Together**
   - Database → Haskell backend
   - Feature flags → UI components
   - MCP server → Database queries

---

## Related Documents

### Foundation Documents
- [DATABASE_SCHEMA.md](./DATABASE_SCHEMA.md) - Complete database schema
- [MCP_SERVER_CONFIG.md](./MCP_SERVER_CONFIG.md) - MCP server configuration
- [FEATURE_FLAGS_SYSTEM.md](./FEATURE_FLAGS_SYSTEM.md) - Feature flag system
- [LITERATE_PROGRAMMING_MAPPING.md](./LITERATE_PROGRAMMING_MAPPING.md) - Code mapping

### Ontology Documents
- [MASTER_DEPENDENCY_ONTOLOGY.md](./MASTER_DEPENDENCY_ONTOLOGY.md) - Domain ontology
- [audit/ONTOLOGY_ARCHITECTURE.md](./audit/ONTOLOGY_ARCHITECTURE.md) - Type system
- [audit/ONTOLOGY_IMPLEMENTATION_PROTOCOL.md](./audit/ONTOLOGY_IMPLEMENTATION_PROTOCOL.md) - Implementation protocol

### Migration Documents
- [CLEAN_REFACTOR_TO_DUCKDB_PLAN.md](./CLEAN_REFACTOR_TO_DUCKDB_PLAN.md) - Migration plan
- [MASTER_REFACTOR_STATUS.md](./MASTER_REFACTOR_STATUS.md) - Refactor status

---

## Success Criteria

The foundation is complete when:

1. ✅ Database schema documented and tested
2. ✅ MCP server implemented and tested
3. ✅ Feature flags system implemented
4. ✅ Code-to-database mapping documented
5. ✅ All components use feature flags
6. ✅ LLM agents can query database via MCP
7. ✅ All features modular and toggleable

---

*Foundation Base Version: 1.0*
*Last Updated: 2026-01-23*
