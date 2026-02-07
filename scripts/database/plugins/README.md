# Plugin Database Schema Registration

Plugins can add their own database tables by registering a schema module.

## Plugin Schema Structure

Create a directory structure:
```
plugins/{plugin-id}/
  ├── schema.sql          # SQL schema file
  └── manifest.json       # Plugin manifest (optional)
```

## Schema SQL File

Your `schema.sql` file should follow this pattern:

```sql
-- Plugin: {plugin-id}
-- Tables: {table1}, {table2}, ...

CREATE TABLE IF NOT EXISTS {plugin_id}_data (
    id TEXT PRIMARY KEY,
    layer_id TEXT REFERENCES layers(id) ON DELETE CASCADE,
    data JSON NOT NULL DEFAULT '{}',
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX IF NOT EXISTS idx_{plugin_id}_data_layer_id ON {plugin_id}_data(layer_id);
```

## Registration

Plugins register their schema via the Haskell/PureScript API:

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

## Feature Flags

Plugins should define a feature flag in `scripts/init-feature-flags.sql`:

```sql
INSERT INTO feature_flags (id, name, description, enabled_by_default, category) VALUES
    ('ff-plugin-my-plugin-enabled', 'Plugin: My Plugin', 'Enable My Plugin features', false, 'plugin');
```

## Dependencies

Plugins can depend on core modules or other plugins:

```haskell
configDependencies = [ModuleId "core", ModuleId "effects"]
```

The module loader will automatically resolve dependencies and load them in the correct order.

## Table Naming

Use `{plugin_id}_` prefix for all table names to avoid conflicts:
- ✅ `my_plugin_data`
- ✅ `my_plugin_settings`
- ❌ `data` (conflicts with core)
- ❌ `settings` (conflicts with core)

## Migration

When updating plugin schemas, create migration files in `scripts/database/migrations/`:

```
migrations/
  └── {plugin-id}/
      ├── 001-add-new-column.sql
      └── 002-add-index.sql
```
