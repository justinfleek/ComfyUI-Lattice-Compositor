# Modular Database Architecture

> **Purpose:** Modular database schema loading system
> **Status:** ✅ IMPLEMENTED
> **Languages:** Lean4 → PureScript → Haskell → FFI
> **Last Updated:** 2026-01-23

**CRITICAL:** All database module types are defined in Lean4 and extracted to PureScript/Haskell. The module registry is implemented in Haskell with PureScript types extracted from Lean4.

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    Lean4 Definitions                        │
│  Lattice.Database.ModuleRegistry.lean                       │
│  - ModuleId, FeatureFlagName, SqlFilePath, TableName        │
│  - ModuleConfig, ModuleRegistry, ModuleLoadResult            │
└─────────────────────────────────────────────────────────────┘
                          │
                          ▼ (Extract)
        ┌─────────────────┴─────────────────┐
        ▼                                     ▼
┌──────────────────┐              ┌──────────────────┐
│  PureScript      │              │  Haskell          │
│  Types           │              │  Implementation   │
│  (Extracted)     │              │  (Extracted)      │
└──────────────────┘              └──────────────────┘
        │                                     │
        └─────────────────┬─────────────────┘
                          ▼
              ┌──────────────────────┐
              │  FFI (C Functions)    │
              │  initialize_schema()  │
              └──────────────────────┘
```

---

## Module Registry System

### Lean4 Definitions

**File:** `lattice-core/lean/Lattice/Database/ModuleRegistry.lean`

Defines all types with proofs:
- `ModuleId` - Non-empty string identifier
- `FeatureFlagName` - Feature flag that controls loading
- `SqlFilePath` - Path to SQL file
- `TableName` - Database table name
- `ModuleConfig` - Module configuration
- `ModuleRegistry` - Registry of all modules
- `ModuleLoadResult` - Loading result type

### Haskell Implementation

**File:** `src/lattice/Database/ModuleRegistry.hs`

- `defaultRegistry` - Built-in modules (core, effects, physics, etc.)
- `registerPluginModule` - Register plugin modules
- `resolveLoadOrder` - Topological sort based on dependencies
- `shouldLoadModule` - Check if module should load based on feature flags

**File:** `src/lattice/Database/Schema.hs`

- `initializeSchema` - Load core + enabled modules
- `loadModule` - Load single module
- `loadModules` - Load multiple modules in order

### PureScript Types

**File:** `src/Lattice/Database/ModuleRegistry.purs` (to be extracted from Lean4)

PureScript types extracted from Lean4 definitions. Used by frontend for:
- Type-safe module registration
- Feature flag checking
- Module discovery

---

## Module Structure

### Core Module (Always Loaded)

**File:** `scripts/database/00-core.sql`

Tables:
- `projects`, `compositions`, `layers`, `keyframes`, `expressions`
- `assets`, `chat_messages`, `feature_flags`, `events`, `metrics`, `markers`

### Domain Modules (Feature Flag Controlled)

| Module | SQL File | Feature Flag | Tables |
|--------|----------|--------------|--------|
| `effects` | `modules/01-effects.sql` | `ff-effects-enabled` | `effects`, `layer_styles`, `layer_masks` |
| `animation` | `modules/02-animation.sql` | `ff-animation-enabled` | `text_layers`, `text_animators`, `property_drivers` |
| `physics` | `modules/03-physics.sql` | `ff-physics-enabled` | `physics_spaces`, `physics_bodies`, `physics_joints`, etc. |
| `particles` | `modules/04-particles.sql` | `ff-particles-enabled` | `particle_systems`, `particle_emitters`, `particle_forces` |
| `audio` | `modules/05-audio.sql` | `ff-audio-enabled` | `audio_tracks`, `audio_analysis`, `audio_reactivity` |
| `camera` | `modules/06-camera.sql` | `ff-camera-enabled` | `cameras`, `camera_paths`, `camera_keyframes` |
| `export` | `modules/07-export.sql` | `ff-export-enabled` | `export_jobs`, `export_templates`, `render_settings` |
| `ai` | `modules/08-ai.sql` | `ff-ai-enabled` | `ai_models`, `preprocessors`, `segmentations`, `vectorizations` |
| `templates` | `modules/09-templates.sql` | `ff-templates-enabled` | `templates`, `template_exposed_properties`, `presets` |
| `mesh-warp` | `modules/10-mesh-warp.sql` | `ff-mesh-warp-enabled` | `mesh_warp_pins`, `mesh_warp_meshes` |

---

## Plugin Registration

Plugins register their schema via Haskell/PureScript API:

**Haskell:**
```haskell
import Lattice.Database.ModuleRegistry

let pluginModuleId = ModuleId "my-plugin"
let pluginConfig = ModuleConfig
      { configSqlFile = SqlFilePath "plugins/my-plugin/schema.sql"
      , configFeatureFlag = Just (FeatureFlagName "ff-plugin-my-plugin-enabled")
      , configDependencies = [ModuleId "core"]
      , configTables = [TableName "my_plugin_data"]
      , configIsPlugin = True
      }
let registry' = registerPluginModule pluginModuleId pluginConfig defaultRegistry
```

**PureScript:**
```purescript
import Lattice.Database.ModuleRegistry

let pluginModuleId = ModuleId "my-plugin"
let pluginConfig = ModuleConfig
      { sqlFile: SqlFilePath "plugins/my-plugin/schema.sql"
      , featureFlag: Just (FeatureFlagName "ff-plugin-my-plugin-enabled")
      , dependencies: [ModuleId "core"]
      , tables: [TableName "my_plugin_data"]
      , isPlugin: true
      }
let registry' = registerPluginModule pluginModuleId pluginConfig defaultRegistry
```

---

## Initialization Flow

1. **Read feature flags** from database or config
2. **Resolve enabled modules** based on feature flags
3. **Topological sort** modules by dependencies
4. **Load modules in order** (core first, then dependencies, then dependents)
5. **Execute SQL** for each module

---

## Benefits

✅ **Modular:** Each domain is isolated  
✅ **Type-Safe:** Lean4 types extracted to PS/HS  
✅ **Extensible:** Plugins can add tables easily  
✅ **Fast:** Single transaction, concatenated SQL  
✅ **Maintainable:** Files under 500 lines each  
✅ **Feature-Flag Controlled:** Modules load only when enabled  

---

## Related Documents

- `docs/DATABASE_SCHEMA.md` - Complete schema documentation
- `scripts/database/plugins/README.md` - Plugin registration guide
- `lattice-core/lean/Lattice/Database/ModuleRegistry.lean` - Lean4 type definitions
- `src/lattice/Database/ModuleRegistry.hs` - Haskell implementation
