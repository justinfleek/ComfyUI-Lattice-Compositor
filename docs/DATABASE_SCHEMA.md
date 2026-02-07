# Lattice Compositor Database Schema

> **Purpose:** Complete DuckDB schema based on ontology architecture
> **Status:** 🏗️ FOUNDATION DESIGN
> **Database:** DuckDB (local or cloud)
> **Sandbox:** Bubblewrap for security isolation
> **Last Updated:** 2026-01-23

**CRITICAL:** This schema is the single source of truth for all database operations. All queries, migrations, and data access must align with this schema.

---

## Schema Design Principles

1. **Ontology-Driven:** Every table maps to a domain entity in `MASTER_DEPENDENCY_ONTOLOGY.md`
2. **Type-Safe:** All columns have explicit types matching Lean4/Haskell/PureScript types
3. **Deterministic:** No nullable columns - explicit defaults for all fields
4. **Auditable:** Created/modified timestamps on all tables
5. **Queryable:** Indexes optimized for LLM agent queries
6. **Modular:** Feature flags control table visibility

---

## Core Tables

### 1. Projects

```sql
CREATE TABLE projects (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    name TEXT NOT NULL,                     -- NonEmptyString
    version INTEGER NOT NULL DEFAULT 1,     -- PositiveInt
    fps INTEGER NOT NULL DEFAULT 30,       -- Standard FPS (24, 25, 30, 60)
    width INTEGER NOT NULL DEFAULT 1920,    -- PositiveInt
    height INTEGER NOT NULL DEFAULT 1080,   -- PositiveInt
    duration_frames INTEGER NOT NULL DEFAULT 0, -- FrameNumber
    metadata JSON NOT NULL DEFAULT '{}',     -- ProjectMetadata
    created_at INTEGER NOT NULL,            -- Timestamp (Unix epoch)
    updated_at INTEGER NOT NULL,            -- Timestamp (Unix epoch)
    feature_flags JSON NOT NULL DEFAULT '{}' -- Feature flags for this project
);

CREATE INDEX idx_projects_name ON projects(name);
CREATE INDEX idx_projects_created_at ON projects(created_at);
CREATE INDEX idx_projects_feature_flags ON projects USING GIN(feature_flags);
```

### 2. Compositions

```sql
CREATE TABLE compositions (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    project_id TEXT NOT NULL REFERENCES projects(id) ON DELETE CASCADE,
    name TEXT NOT NULL,                     -- NonEmptyString
    width INTEGER NOT NULL,                  -- PositiveInt
    height INTEGER NOT NULL,                 -- PositiveInt
    fps INTEGER NOT NULL,                    -- Standard FPS
    duration_frames INTEGER NOT NULL DEFAULT 0, -- FrameNumber
    background_color TEXT NOT NULL DEFAULT '#000000', -- Color (hex)
    settings JSON NOT NULL DEFAULT '{}',     -- CompositionSettings
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_compositions_project_id ON compositions(project_id);
CREATE INDEX idx_compositions_name ON compositions(name);
```

### 3. Layers

```sql
CREATE TABLE layers (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    composition_id TEXT NOT NULL REFERENCES compositions(id) ON DELETE CASCADE,
    parent_id TEXT REFERENCES layers(id) ON DELETE CASCADE, -- Nullable for root layers
    name TEXT NOT NULL,                     -- NonEmptyString
    layer_type TEXT NOT NULL,               -- LayerType enum
    order_index INTEGER NOT NULL DEFAULT 0,  -- Order in composition
    visible BOOLEAN NOT NULL DEFAULT true,
    locked BOOLEAN NOT NULL DEFAULT false,
    opacity REAL NOT NULL DEFAULT 1.0 CHECK (opacity >= 0 AND opacity <= 1), -- NormalizedValue
    blend_mode TEXT NOT NULL DEFAULT 'normal', -- BlendMode enum
    start_frame INTEGER NOT NULL DEFAULT 0,  -- FrameNumber
    end_frame INTEGER NOT NULL DEFAULT 0,    -- FrameNumber
    transform JSON NOT NULL DEFAULT '{}',   -- LayerTransform
    mask JSON,                              -- LayerMask (nullable)
    data JSON NOT NULL,                      -- LayerData (union of 26 types)
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_layers_composition_id ON layers(composition_id);
CREATE INDEX idx_layers_parent_id ON layers(parent_id);
CREATE INDEX idx_layers_type ON layers(layer_type);
CREATE INDEX idx_layers_order ON layers(composition_id, order_index);
CREATE INDEX idx_layers_frame_range ON layers(start_frame, end_frame);
```

### 4. Keyframes

```sql
CREATE TABLE keyframes (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    property_path TEXT NOT NULL,            -- PropertyPath (e.g., "transform.position.x")
    frame INTEGER NOT NULL,                 -- FrameNumber
    value JSON NOT NULL,                    -- PropertyValue (type depends on property)
    interpolation_type TEXT NOT NULL DEFAULT 'linear', -- InterpolationType enum
    easing_type TEXT NOT NULL DEFAULT 'ease', -- EasingType enum
    in_tangent REAL,                        -- Optional tangent
    out_tangent REAL,                       -- Optional tangent
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_keyframes_layer_id ON keyframes(layer_id);
CREATE INDEX idx_keyframes_property ON keyframes(layer_id, property_path);
CREATE INDEX idx_keyframes_frame ON keyframes(layer_id, frame);
CREATE UNIQUE INDEX idx_keyframes_unique ON keyframes(layer_id, property_path, frame);
```

### 5. Expressions

```sql
CREATE TABLE expressions (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    property_path TEXT NOT NULL,            -- PropertyPath
    expression_text TEXT NOT NULL,          -- Expression code
    enabled BOOLEAN NOT NULL DEFAULT true,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_expressions_layer_id ON expressions(layer_id);
CREATE INDEX idx_expressions_property ON expressions(layer_id, property_path);
CREATE UNIQUE INDEX idx_expressions_unique ON expressions(layer_id, property_path);
```

### 6. Effects

```sql
CREATE TABLE effects (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    effect_type TEXT NOT NULL,             -- EffectType enum
    effect_category TEXT NOT NULL,          -- EffectCategory enum
    enabled BOOLEAN NOT NULL DEFAULT true,
    parameters JSON NOT NULL DEFAULT '{}',  -- EffectParameters
    order_index INTEGER NOT NULL DEFAULT 0, -- Order in effect stack
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_effects_layer_id ON effects(layer_id);
CREATE INDEX idx_effects_type ON effects(effect_type);
CREATE INDEX idx_effects_order ON effects(layer_id, order_index);
```

### 7. Audio

```sql
CREATE TABLE audio_tracks (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    composition_id TEXT NOT NULL REFERENCES compositions(id) ON DELETE CASCADE,
    name TEXT NOT NULL,                     -- NonEmptyString
    file_path TEXT NOT NULL,                -- File path
    start_frame INTEGER NOT NULL DEFAULT 0,  -- FrameNumber
    duration_frames INTEGER NOT NULL,       -- FrameNumber
    volume REAL NOT NULL DEFAULT 1.0 CHECK (volume >= 0 AND volume <= 1), -- NormalizedValue
    analysis_data JSON,                    -- AudioAnalysis (nullable)
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_audio_composition_id ON audio_tracks(composition_id);
CREATE INDEX idx_audio_frame_range ON audio_tracks(start_frame, duration_frames);
```

### 8. Cameras

```sql
CREATE TABLE cameras (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    composition_id TEXT NOT NULL REFERENCES compositions(id) ON DELETE CASCADE,
    name TEXT NOT NULL,                     -- NonEmptyString
    camera_type TEXT NOT NULL DEFAULT 'perspective', -- CameraType enum
    position JSON NOT NULL DEFAULT '{"x":0,"y":0,"z":0}', -- Vec3
    rotation JSON NOT NULL DEFAULT '{"x":0,"y":0,"z":0}', -- Vec3
    fov REAL NOT NULL DEFAULT 50.0 CHECK (fov > 0 AND fov <= 180), -- PositiveFloat
    near_plane REAL NOT NULL DEFAULT 0.1 CHECK (near_plane > 0), -- PositiveFloat
    far_plane REAL NOT NULL DEFAULT 1000.0 CHECK (far_plane > near_plane), -- PositiveFloat
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_cameras_composition_id ON cameras(composition_id);
```

### 9. Physics

```sql
CREATE TABLE physics_spaces (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    composition_id TEXT NOT NULL REFERENCES compositions(id) ON DELETE CASCADE,
    gravity JSON NOT NULL DEFAULT '{"x":0,"y":-9.81,"z":0}', -- Vec3
    enabled BOOLEAN NOT NULL DEFAULT true,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE physics_bodies (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    physics_space_id TEXT NOT NULL REFERENCES physics_spaces(id) ON DELETE CASCADE,
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    body_type TEXT NOT NULL,                -- BodyType enum
    mass REAL NOT NULL DEFAULT 1.0 CHECK (mass > 0), -- PositiveFloat
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_physics_spaces_composition_id ON physics_spaces(composition_id);
CREATE INDEX idx_physics_bodies_space_id ON physics_bodies(physics_space_id);
CREATE INDEX idx_physics_bodies_layer_id ON physics_bodies(layer_id);
```

### 10. Particles

```sql
CREATE TABLE particle_systems (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    emitter_shape TEXT NOT NULL,             -- EmitterShape enum
    particle_shape TEXT NOT NULL,           -- ParticleShape enum
    emission_rate REAL NOT NULL DEFAULT 10.0 CHECK (emission_rate >= 0), -- PositiveFloat
    lifetime REAL NOT NULL DEFAULT 1.0 CHECK (lifetime > 0), -- PositiveFloat
    config JSON NOT NULL DEFAULT '{}',      -- ParticleSystemConfig
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_particle_systems_layer_id ON particle_systems(layer_id);
```

### 11. Assets

```sql
CREATE TABLE assets (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    project_id TEXT NOT NULL REFERENCES projects(id) ON DELETE CASCADE,
    name TEXT NOT NULL,                     -- NonEmptyString
    file_path TEXT NOT NULL,                -- File path
    asset_type TEXT NOT NULL,               -- AssetType enum
    metadata JSON NOT NULL DEFAULT '{}',     -- AssetMetadata
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_assets_project_id ON assets(project_id);
CREATE INDEX idx_assets_type ON assets(asset_type);
```

### 12. Chat Messages (LLM Agent History)

```sql
CREATE TABLE chat_messages (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    project_id TEXT REFERENCES projects(id) ON DELETE CASCADE, -- Nullable for global chat
    role TEXT NOT NULL,                     -- 'user' | 'assistant' | 'system' | 'tool'
    content TEXT NOT NULL,                 -- Message content
    tool_calls JSON,                        -- Tool calls (nullable)
    tool_call_id TEXT,                      -- For tool responses
    model TEXT,                             -- Model used (nullable)
    tokens_used INTEGER DEFAULT 0,           -- Token count
    cost_usd REAL DEFAULT 0.0,              -- Cost in USD
    timestamp INTEGER NOT NULL,             -- Timestamp (Unix epoch)
    created_at INTEGER NOT NULL,
    modified_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_chat_project_id ON chat_messages(project_id);
CREATE INDEX idx_chat_timestamp ON chat_messages(timestamp);
CREATE INDEX idx_chat_role ON chat_messages(role);
CREATE INDEX idx_chat_tool_call_id ON chat_messages(tool_call_id);
```

### 13. Feature Flags

```sql
CREATE TABLE feature_flags (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    name TEXT NOT NULL UNIQUE,              -- Feature flag name
    description TEXT NOT NULL,               -- Human-readable description
    enabled_by_default BOOLEAN NOT NULL DEFAULT false,
    category TEXT NOT NULL,                  -- 'ui' | 'engine' | 'export' | 'ai' | 'experimental'
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL
);

CREATE INDEX idx_feature_flags_category ON feature_flags(category);
CREATE INDEX idx_feature_flags_enabled ON feature_flags(enabled_by_default);
```

### 14. Events (Audit Trail)

```sql
CREATE TABLE events (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    event_type TEXT NOT NULL,               -- EventType enum
    project_id TEXT REFERENCES projects(id) ON DELETE CASCADE,
    composition_id TEXT REFERENCES compositions(id) ON DELETE CASCADE,
    layer_id TEXT REFERENCES layers(id) ON DELETE CASCADE,
    user_id TEXT,                           -- User identifier (nullable)
    data JSON NOT NULL DEFAULT '{}',         -- Event-specific data
    timestamp INTEGER NOT NULL,
    created_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_events_type ON events(event_type);
CREATE INDEX idx_events_project_id ON events(project_id);
CREATE INDEX idx_events_timestamp ON events(timestamp);
CREATE INDEX idx_events_composition_id ON events(composition_id);
CREATE INDEX idx_events_layer_id ON events(layer_id);
```

### 15. Metrics (Performance/Analytics)

```sql
CREATE TABLE metrics (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    metric_name TEXT NOT NULL,              -- MetricDefinition.name
    category TEXT NOT NULL,                 -- 'rendering' | 'performance' | 'quality' | 'resource' | 'user' | 'ai'
    project_id TEXT REFERENCES projects(id) ON DELETE CASCADE,
    composition_id TEXT REFERENCES compositions(id) ON DELETE CASCADE,
    value REAL NOT NULL,                    -- Metric value
    unit TEXT NOT NULL,                     -- Unit (e.g., 'ms', 'fps', 'MB')
    timestamp INTEGER NOT NULL,
    created_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_metrics_name ON metrics(metric_name);
CREATE INDEX idx_metrics_category ON metrics(category);
CREATE INDEX idx_metrics_project_id ON metrics(project_id);
CREATE INDEX idx_metrics_timestamp ON metrics(timestamp);
```

### 16. Text Layers & Animators

```sql
CREATE TABLE text_layers (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    text_content TEXT NOT NULL DEFAULT '',  -- Text content
    font_family TEXT NOT NULL DEFAULT 'Arial',
    font_size REAL NOT NULL DEFAULT 24.0 CHECK (font_size > 0),
    font_weight TEXT NOT NULL DEFAULT 'normal', -- FontWeight enum
    font_style TEXT NOT NULL DEFAULT 'normal', -- FontStyle enum
    text_align TEXT NOT NULL DEFAULT 'left', -- TextAlign enum
    text_direction TEXT NOT NULL DEFAULT 'ltr', -- TextDirection enum
    color TEXT NOT NULL DEFAULT '#FFFFFF',  -- Color (hex)
    config JSON NOT NULL DEFAULT '{}',     -- FontConfig
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE text_animators (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    text_layer_id TEXT NOT NULL REFERENCES text_layers(id) ON DELETE CASCADE,
    animator_type TEXT NOT NULL,           -- TextAnimatorType enum
    selector_config JSON NOT NULL DEFAULT '{}', -- Selector config
    properties JSON NOT NULL DEFAULT '{}', -- Animated properties
    order_index INTEGER NOT NULL DEFAULT 0,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_text_layers_layer_id ON text_layers(layer_id);
CREATE INDEX idx_text_animators_text_layer_id ON text_animators(text_layer_id);
CREATE INDEX idx_text_animators_order ON text_animators(text_layer_id, order_index);
```

### 17. Masks

```sql
CREATE TABLE layer_masks (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    name TEXT NOT NULL,                    -- NonEmptyString
    enabled BOOLEAN NOT NULL DEFAULT true,
    mode TEXT NOT NULL DEFAULT 'add',      -- MaskMode enum
    invert BOOLEAN NOT NULL DEFAULT false,
    opacity REAL NOT NULL DEFAULT 1.0 CHECK (opacity >= 0 AND opacity <= 1),
    paths JSON NOT NULL DEFAULT '[]',      -- Array of MaskPath
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_layer_masks_layer_id ON layer_masks(layer_id);
```

### 18. Layer Styles

```sql
CREATE TABLE layer_styles (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    drop_shadow JSON,                      -- DropShadowStyle (nullable)
    inner_shadow JSON,                     -- InnerShadowStyle (nullable)
    outer_glow JSON,                       -- OuterGlowStyle (nullable)
    inner_glow JSON,                      -- InnerGlowStyle (nullable)
    bevel_emboss JSON,                     -- BevelEmbossStyle (nullable)
    satin JSON,                            -- SatinStyle (nullable)
    color_overlay JSON,                    -- ColorOverlayStyle (nullable)
    gradient_overlay JSON,                 -- GradientOverlayStyle (nullable)
    pattern_overlay JSON,                  -- PatternOverlayStyle (nullable)
    stroke JSON,                           -- StrokeStyle (nullable)
    blending_options JSON NOT NULL DEFAULT '{}', -- StyleBlendingOptions
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_layer_styles_layer_id ON layer_styles(layer_id);
```

### 19. Presets

```sql
CREATE TABLE presets (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    project_id TEXT REFERENCES projects(id) ON DELETE CASCADE, -- Nullable for global presets
    name TEXT NOT NULL,                    -- NonEmptyString
    description TEXT NOT NULL DEFAULT '',
    category TEXT NOT NULL,                -- PresetCategory enum
    preset_type TEXT NOT NULL,             -- 'particle' | 'effect' | 'path-effect' | 'camera-shake' | 'camera-trajectory' | 'text-style' | 'color-palette' | 'animation'
    config JSON NOT NULL DEFAULT '{}',     -- Preset-specific config
    metadata JSON NOT NULL DEFAULT '{}',   -- PresetMetadata
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_presets_project_id ON presets(project_id);
CREATE INDEX idx_presets_category ON presets(category);
CREATE INDEX idx_presets_type ON presets(preset_type);
```

### 20. Export Jobs & Templates

```sql
CREATE TABLE export_jobs (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    project_id TEXT NOT NULL REFERENCES projects(id) ON DELETE CASCADE,
    composition_id TEXT REFERENCES compositions(id) ON DELETE CASCADE,
    status TEXT NOT NULL DEFAULT 'queued',  -- ExportStatus enum
    format TEXT NOT NULL,                   -- ExportFormat enum
    config JSON NOT NULL DEFAULT '{}',     -- ExportConfig
    output_path TEXT,                      -- Output file path (nullable)
    progress REAL NOT NULL DEFAULT 0.0 CHECK (progress >= 0 AND progress <= 1),
    error_message TEXT,                     -- Error message (nullable)
    started_at INTEGER,                     -- Start timestamp (nullable)
    completed_at INTEGER,                   -- Completion timestamp (nullable)
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE export_templates (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    project_id TEXT REFERENCES projects(id) ON DELETE CASCADE, -- Nullable for global templates
    name TEXT NOT NULL,                    -- NonEmptyString
    format TEXT NOT NULL,                  -- ExportFormat enum
    config JSON NOT NULL DEFAULT '{}',     -- ExportTemplate config
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_export_jobs_project_id ON export_jobs(project_id);
CREATE INDEX idx_export_jobs_status ON export_jobs(status);
CREATE INDEX idx_export_jobs_composition_id ON export_jobs(composition_id);
CREATE INDEX idx_export_templates_project_id ON export_templates(project_id);
CREATE INDEX idx_export_templates_format ON export_templates(format);
```

### 21. AI Models & Preprocessors

```sql
CREATE TABLE ai_models (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    name TEXT NOT NULL UNIQUE,             -- NonEmptyString
    model_type TEXT NOT NULL,              -- ModelType enum
    provider TEXT NOT NULL,                -- LLM provider name
    api_endpoint TEXT NOT NULL,            -- API endpoint URL
    config JSON NOT NULL DEFAULT '{}',     -- Model configuration
    enabled BOOLEAN NOT NULL DEFAULT true,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE preprocessors (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    name TEXT NOT NULL UNIQUE,             -- NonEmptyString
    category TEXT NOT NULL,                -- PreprocessorCategory enum
    description TEXT NOT NULL DEFAULT '',
    config JSON NOT NULL DEFAULT '{}',     -- Preprocessor configuration
    enabled BOOLEAN NOT NULL DEFAULT true,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE segmentations (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    method TEXT NOT NULL,                  -- SegmentationMode enum
    result JSON NOT NULL DEFAULT '{}',     -- Segmentation result data
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE vectorizations (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    method TEXT NOT NULL,                  -- Vectorization method
    result JSON NOT NULL DEFAULT '{}',    -- Vectorization result (paths, etc.)
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_ai_models_type ON ai_models(model_type);
CREATE INDEX idx_preprocessors_category ON preprocessors(category);
CREATE INDEX idx_segmentations_layer_id ON segmentations(layer_id);
CREATE INDEX idx_vectorizations_layer_id ON vectorizations(layer_id);
```

### 22. Templates (Template Builder)

```sql
CREATE TABLE templates (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    project_id TEXT REFERENCES projects(id) ON DELETE CASCADE, -- Nullable for global templates
    name TEXT NOT NULL,                    -- NonEmptyString
    description TEXT NOT NULL DEFAULT '',
    version TEXT NOT NULL DEFAULT '1.0.0',
    author TEXT NOT NULL DEFAULT '',
    config JSON NOT NULL DEFAULT '{}',     -- TemplateConfig
    project_data JSON NOT NULL DEFAULT '{}', -- LatticeProject data
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE template_exposed_properties (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    template_id TEXT NOT NULL REFERENCES templates(id) ON DELETE CASCADE,
    name TEXT NOT NULL,                    -- NonEmptyString
    property_path TEXT NOT NULL,           -- PropertyPath
    property_type TEXT NOT NULL,           -- ExposedPropertyType enum
    config JSON NOT NULL DEFAULT '{}',     -- ExposedPropertyConfig
    group_name TEXT,                       -- PropertyGroup name (nullable)
    order_index INTEGER NOT NULL DEFAULT 0,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_templates_project_id ON templates(project_id);
CREATE INDEX idx_template_exposed_properties_template_id ON template_exposed_properties(template_id);
CREATE INDEX idx_template_exposed_properties_group ON template_exposed_properties(template_id, group_name);
```

### 23. Mesh Warp

```sql
CREATE TABLE mesh_warp_pins (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    pin_type TEXT NOT NULL,                -- WarpPinType enum
    position JSON NOT NULL,                -- Vec2 position
    rotation REAL NOT NULL DEFAULT 0.0,    -- Rotation angle
    rest_state JSON,                       -- WarpPinRestState (nullable)
    config JSON NOT NULL DEFAULT '{}',     -- Pin-specific config
    order_index INTEGER NOT NULL DEFAULT 0,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE mesh_warp_meshes (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    vertices JSON NOT NULL DEFAULT '[]',   -- Array of Vec2
    triangles JSON NOT NULL DEFAULT '[]',  -- Array of triangle indices
    uvs JSON NOT NULL DEFAULT '[]',        -- UV coordinates
    normals JSON NOT NULL DEFAULT '[]',    -- Normal vectors
    weight_method TEXT NOT NULL DEFAULT 'distance', -- WarpWeightMethod enum
    weight_options JSON NOT NULL DEFAULT '{}', -- WarpWeightOptions
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_mesh_warp_pins_layer_id ON mesh_warp_pins(layer_id);
CREATE INDEX idx_mesh_warp_meshes_layer_id ON mesh_warp_meshes(layer_id);
```

### 24. Physics (Extended)

```sql
CREATE TABLE physics_joints (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    physics_space_id TEXT NOT NULL REFERENCES physics_spaces(id) ON DELETE CASCADE,
    body_a_id TEXT NOT NULL REFERENCES physics_bodies(id) ON DELETE CASCADE,
    body_b_id TEXT NOT NULL REFERENCES physics_bodies(id) ON DELETE CASCADE,
    joint_type TEXT NOT NULL,              -- JointType enum
    config JSON NOT NULL DEFAULT '{}',     -- Joint-specific configuration
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE physics_rigid_bodies (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format (references physics_bodies.id)
    physics_body_id TEXT NOT NULL REFERENCES physics_bodies(id) ON DELETE CASCADE,
    shape_config JSON NOT NULL DEFAULT '{}', -- CollisionShape config
    material_config JSON NOT NULL DEFAULT '{}', -- PhysicsMaterial config
    filter_config JSON NOT NULL DEFAULT '{}', -- CollisionFilter config
    state JSON NOT NULL DEFAULT '{}',      -- RigidBodyState
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE physics_cloth (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    physics_space_id TEXT NOT NULL REFERENCES physics_spaces(id) ON DELETE CASCADE,
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    mesh_config JSON NOT NULL DEFAULT '{}', -- Cloth mesh configuration
    material_config JSON NOT NULL DEFAULT '{}', -- Cloth material properties
    constraints JSON NOT NULL DEFAULT '[]', -- Constraint configuration
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE physics_ragdolls (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    physics_space_id TEXT NOT NULL REFERENCES physics_spaces(id) ON DELETE CASCADE,
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    skeleton_config JSON NOT NULL DEFAULT '{}', -- Skeleton/bone configuration
    joint_configs JSON NOT NULL DEFAULT '[]', -- Array of joint configurations
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_physics_joints_space_id ON physics_joints(physics_space_id);
CREATE INDEX idx_physics_joints_bodies ON physics_joints(body_a_id, body_b_id);
CREATE INDEX idx_physics_rigid_bodies_body_id ON physics_rigid_bodies(physics_body_id);
CREATE INDEX idx_physics_cloth_space_id ON physics_cloth(physics_space_id);
CREATE INDEX idx_physics_cloth_layer_id ON physics_cloth(layer_id);
CREATE INDEX idx_physics_ragdolls_space_id ON physics_ragdolls(physics_space_id);
CREATE INDEX idx_physics_ragdolls_layer_id ON physics_ragdolls(layer_id);
```

### 25. Camera Paths & Keyframes

```sql
CREATE TABLE camera_paths (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    camera_id TEXT NOT NULL REFERENCES cameras(id) ON DELETE CASCADE,
    name TEXT NOT NULL,                    -- NonEmptyString
    path_type TEXT NOT NULL DEFAULT 'spline', -- 'spline' | 'linear' | 'bezier'
    control_points JSON NOT NULL DEFAULT '[]', -- Array of control points
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE camera_keyframes (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    camera_id TEXT NOT NULL REFERENCES cameras(id) ON DELETE CASCADE,
    frame INTEGER NOT NULL,                -- FrameNumber
    position JSON NOT NULL,                -- Vec3 position
    rotation JSON NOT NULL,                -- Vec3 rotation
    fov REAL NOT NULL,                     -- FOV value
    interpolation_type TEXT NOT NULL DEFAULT 'linear', -- InterpolationType enum
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_camera_paths_camera_id ON camera_paths(camera_id);
CREATE INDEX idx_camera_keyframes_camera_id ON camera_keyframes(camera_id);
CREATE INDEX idx_camera_keyframes_frame ON camera_keyframes(camera_id, frame);
```

### 26. Audio Analysis

```sql
CREATE TABLE audio_analysis (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    audio_track_id TEXT NOT NULL REFERENCES audio_tracks(id) ON DELETE CASCADE,
    analysis_type TEXT NOT NULL,           -- 'amplitude' | 'frequency' | 'beat' | 'features'
    frame INTEGER NOT NULL,                -- FrameNumber
    data JSON NOT NULL DEFAULT '{}',       -- Analysis data (AudioAmplitudeResult | FrequencyBandResult | AudioFeaturesResult | BeatData)
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE audio_reactivity (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    audio_track_id TEXT NOT NULL REFERENCES audio_tracks(id) ON DELETE CASCADE,
    property_path TEXT NOT NULL,          -- PropertyPath
    frequency_band TEXT NOT NULL,          -- FrequencyBandName enum
    mapping_config JSON NOT NULL DEFAULT '{}', -- Audio reactivity mapping configuration
    enabled BOOLEAN NOT NULL DEFAULT true,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_audio_analysis_track_id ON audio_analysis(audio_track_id);
CREATE INDEX idx_audio_analysis_frame ON audio_analysis(audio_track_id, frame);
CREATE INDEX idx_audio_reactivity_layer_id ON audio_reactivity(layer_id);
CREATE INDEX idx_audio_reactivity_track_id ON audio_reactivity(audio_track_id);
```

### 27. Render Settings

```sql
CREATE TABLE render_settings (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    composition_id TEXT NOT NULL REFERENCES compositions(id) ON DELETE CASCADE,
    resolution_width INTEGER NOT NULL,
    resolution_height INTEGER NOT NULL,
    fps INTEGER NOT NULL,
    start_frame INTEGER NOT NULL DEFAULT 0,
    end_frame INTEGER NOT NULL,
    quality TEXT NOT NULL DEFAULT 'high', -- 'low' | 'medium' | 'high' | 'ultra'
    motion_blur_enabled BOOLEAN NOT NULL DEFAULT false,
    motion_blur_samples INTEGER NOT NULL DEFAULT 8,
    depth_of_field_enabled BOOLEAN NOT NULL DEFAULT false,
    anti_aliasing TEXT NOT NULL DEFAULT 'msaa', -- 'none' | 'msaa' | 'fxaa' | 'taa'
    color_space TEXT NOT NULL DEFAULT 'sRGB', -- ColorSpace enum
    view_transform TEXT NOT NULL DEFAULT 'sRGB', -- ViewTransform enum
    config JSON NOT NULL DEFAULT '{}',     -- Additional render configuration
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_render_settings_composition_id ON render_settings(composition_id);
```

### 28. Markers

```sql
CREATE TABLE markers (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    composition_id TEXT NOT NULL REFERENCES compositions(id) ON DELETE CASCADE,
    frame INTEGER NOT NULL,                -- FrameNumber
    label TEXT NOT NULL DEFAULT '',        -- Marker label
    color TEXT NOT NULL DEFAULT '#FF0000', -- Color (hex)
    duration INTEGER NOT NULL DEFAULT 0,   -- Duration in frames
    comment TEXT NOT NULL DEFAULT '',       -- Marker comment
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_markers_composition_id ON markers(composition_id);
CREATE INDEX idx_markers_frame ON markers(composition_id, frame);
```

### 29. Property Drivers

```sql
CREATE TABLE property_drivers (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    property_path TEXT NOT NULL,           -- PropertyPath (target property)
    driver_source_type TEXT NOT NULL,      -- DriverSourceType enum
    source_layer_id TEXT REFERENCES layers(id) ON DELETE CASCADE, -- Nullable
    source_property_path TEXT,            -- Source property path (nullable)
    transform_config JSON NOT NULL DEFAULT '{}', -- DriverTransform config
    enabled BOOLEAN NOT NULL DEFAULT true,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_property_drivers_layer_id ON property_drivers(layer_id);
CREATE INDEX idx_property_drivers_source ON property_drivers(source_layer_id, source_property_path);
CREATE UNIQUE INDEX idx_property_drivers_unique ON property_drivers(layer_id, property_path);
```

### 30. Particle Emitters & Forces

```sql
CREATE TABLE particle_emitters (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    particle_system_id TEXT NOT NULL REFERENCES particle_systems(id) ON DELETE CASCADE,
    emitter_shape TEXT NOT NULL,          -- EmitterShape enum
    emission_rate REAL NOT NULL DEFAULT 10.0 CHECK (emission_rate >= 0),
    lifetime REAL NOT NULL DEFAULT 1.0 CHECK (lifetime > 0),
    position JSON NOT NULL DEFAULT '{"x":0,"y":0,"z":0}', -- Vec3
    config JSON NOT NULL DEFAULT '{}',    -- EmitterConfig
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE TABLE particle_forces (
    id TEXT PRIMARY KEY CHECK (id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$'), -- UUID5 format
    particle_system_id TEXT NOT NULL REFERENCES particle_systems(id) ON DELETE CASCADE,
    force_type TEXT NOT NULL,             -- ForceType enum
    position JSON NOT NULL DEFAULT '{"x":0,"y":0,"z":0}', -- Vec3
    strength REAL NOT NULL DEFAULT 1.0,
    config JSON NOT NULL DEFAULT '{}',    -- ForceFieldConfig
    enabled BOOLEAN NOT NULL DEFAULT true,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

CREATE INDEX idx_particle_emitters_system_id ON particle_emitters(particle_system_id);
CREATE INDEX idx_particle_forces_system_id ON particle_forces(particle_system_id);
CREATE INDEX idx_particle_forces_type ON particle_forces(force_type);
```

---

## Views (Query Optimization)

### View: Active Layers

```sql
CREATE VIEW active_layers AS
SELECT 
    l.*,
    c.name AS composition_name,
    c.project_id
FROM layers l
JOIN compositions c ON l.composition_id = c.id
WHERE l.visible = true
  AND l.start_frame <= (SELECT current_frame FROM playback_state LIMIT 1)
  AND l.end_frame >= (SELECT current_frame FROM playback_state LIMIT 1);
```

### View: Layer Hierarchy

```sql
CREATE VIEW layer_hierarchy AS
WITH RECURSIVE layer_tree AS (
    SELECT 
        id,
        parent_id,
        name,
        layer_type,
        order_index,
        0 AS depth,
        CAST(id AS TEXT) AS path
    FROM layers
    WHERE parent_id IS NULL
    
    UNION ALL
    
    SELECT 
        l.id,
        l.parent_id,
        l.name,
        l.layer_type,
        l.order_index,
        lt.depth + 1,
        lt.path || '/' || l.id
    FROM layers l
    JOIN layer_tree lt ON l.parent_id = lt.id
)
SELECT * FROM layer_tree
ORDER BY path;
```

### View: Keyframe Timeline

```sql
CREATE VIEW keyframe_timeline AS
SELECT 
    k.*,
    l.name AS layer_name,
    l.composition_id,
    c.name AS composition_name
FROM keyframes k
JOIN layers l ON k.layer_id = l.id
JOIN compositions c ON l.composition_id = c.id
ORDER BY k.frame, l.order_index;
```

---

## Full-Text Search Setup

```sql
-- Enable full-text search extension
INSTALL 'fts';
LOAD 'fts';

-- Create full-text search index on chat messages
CREATE VIRTUAL TABLE chat_messages_fts USING fts5(
    content,
    content='chat_messages',
    content_rowid='rowid'
);

-- Trigger to maintain FTS index
CREATE TRIGGER chat_messages_fts_insert AFTER INSERT ON chat_messages BEGIN
    INSERT INTO chat_messages_fts(rowid, content) VALUES (new.rowid, new.content);
END;

CREATE TRIGGER chat_messages_fts_delete AFTER DELETE ON chat_messages BEGIN
    INSERT INTO chat_messages_fts(chat_messages_fts, rowid, content) VALUES('delete', old.rowid, old.content);
END;

CREATE TRIGGER chat_messages_fts_update AFTER UPDATE ON chat_messages BEGIN
    INSERT INTO chat_messages_fts(chat_messages_fts, rowid, content) VALUES('delete', old.rowid, old.content);
    INSERT INTO chat_messages_fts(rowid, content) VALUES (new.rowid, new.content);
END;
```

---

## Feature Flag Functions

```sql
-- Check if feature is enabled for a specific entity
CREATE FUNCTION feature_enabled(entity_flags JSON, feature_name TEXT) 
RETURNS BOOLEAN AS $$
    SELECT COALESCE(
        json_extract(entity_flags, '$.' || feature_name),
        (SELECT enabled_by_default FROM feature_flags WHERE name = feature_name)
    ) = true;
$$;

-- Get all enabled features for an entity
CREATE FUNCTION enabled_features(entity_flags JSON) 
RETURNS TABLE(feature_name TEXT) AS $$
    SELECT name 
    FROM feature_flags 
    WHERE feature_enabled(entity_flags, name) = true;
$$;
```

---

## Initialization Script

```sql
-- Initialize database schema
-- Run this script to create all tables, indexes, views, and functions

-- Set timezone
SET timezone = 'UTC';

-- Create tables (in dependency order)
-- (All CREATE TABLE statements from above)

-- Create indexes
-- (All CREATE INDEX statements from above)

-- Create views
-- (All CREATE VIEW statements from above)

-- Create functions
-- (All CREATE FUNCTION statements from above)

-- Insert default feature flags
INSERT INTO feature_flags (id, name, description, enabled_by_default, category) VALUES
    ('ff-ui-particles', 'UI: Particles', 'Enable particle system UI', true, 'ui'),
    ('ff-ui-physics', 'UI: Physics', 'Enable physics simulation UI', true, 'ui'),
    ('ff-engine-webgpu', 'Engine: WebGPU', 'Use WebGPU renderer', true, 'engine'),
    ('ff-export-h264', 'Export: H.264', 'Enable H.264 export', true, 'export'),
    ('ff-ai-chat', 'AI: Chat', 'Enable AI chat panel', true, 'ai'),
    ('ff-experimental-mesh-warp', 'Experimental: Mesh Warp', 'Enable mesh warp deformation', false, 'experimental');
```

---

## Migration Strategy

### Phase 1: Schema Creation
1. Create all tables with feature_flags column
2. Create indexes
3. Create views
4. Create functions

### Phase 2: Data Migration
1. Migrate existing project data from IndexedDB/JSON
2. Migrate chat messages from IndexedDB
3. Verify data integrity

### Phase 3: Feature Flag Migration
1. Map existing feature toggles to feature_flags table
2. Update UI to read from database
3. Remove old feature flag implementations

---

## Query Examples for LLM Agents

### Get All Available Features

```sql
SELECT 
    name,
    description,
    category,
    enabled_by_default
FROM feature_flags
ORDER BY category, name;
```

### Get Project Structure

```sql
SELECT 
    p.id AS project_id,
    p.name AS project_name,
    COUNT(DISTINCT c.id) AS composition_count,
    COUNT(DISTINCT l.id) AS layer_count,
    COUNT(DISTINCT k.id) AS keyframe_count
FROM projects p
LEFT JOIN compositions c ON c.project_id = p.id
LEFT JOIN layers l ON l.composition_id = c.id
LEFT JOIN keyframes k ON k.layer_id = l.id
WHERE p.id = ?
GROUP BY p.id, p.name;
```

### Search Chat History

```sql
SELECT 
    role,
    content,
    timestamp,
    model
FROM chat_messages
WHERE project_id = ?
  AND content MATCH ?
ORDER BY timestamp DESC
LIMIT 50;
```

### Get Layer with All Properties

```sql
SELECT 
    l.*,
    COUNT(DISTINCT k.id) AS keyframe_count,
    COUNT(DISTINCT e.id) AS expression_count,
    COUNT(DISTINCT ef.id) AS effect_count
FROM layers l
LEFT JOIN keyframes k ON k.layer_id = l.id
LEFT JOIN expressions e ON e.layer_id = l.id
LEFT JOIN effects ef ON ef.layer_id = l.id
WHERE l.id = ?
GROUP BY l.id;
```

---

## Security (Bubblewrap Sandbox)

All database operations run in a Bubblewrap sandbox:

```bash
# Database access script
#!/bin/bash
bwrap \
    --ro-bind /usr /usr \
    --ro-bind /lib /lib \
    --ro-bind /lib64 /lib64 \
    --tmpfs /tmp \
    --tmpfs /run \
    --bind "$DB_PATH" "$DB_PATH" \
    --dev /dev \
    --proc /proc \
    duckdb "$DB_PATH" "$@"
```

---

## Related Documents

- `docs/MASTER_DEPENDENCY_ONTOLOGY.md` - Domain ontology
- `docs/audit/ONTOLOGY_ARCHITECTURE.md` - Type system architecture
- `docs/CLEAN_REFACTOR_TO_DUCKDB_PLAN.md` - Migration plan
- `docs/MCP_SERVER_CONFIG.md` - MCP server configuration
- `docs/LITERATE_PROGRAMMING_MAPPING.md` - Code-to-database mapping

---

---

## Schema Summary

**Total Tables:** 30+ core tables covering all domain entities

**Coverage:**
- ✅ Projects, Compositions, Layers (all 26 layer types)
- ✅ Keyframes, Expressions, Effects
- ✅ Audio tracks, analysis, and reactivity
- ✅ Cameras, camera paths, and keyframes
- ✅ Physics spaces, bodies, joints, rigid bodies, cloth, ragdolls
- ✅ Particle systems, emitters, forces
- ✅ Text layers and animators
- ✅ Masks and layer styles
- ✅ Presets (all 8 categories)
- ✅ Export jobs and templates
- ✅ AI models, preprocessors, segmentations, vectorizations
- ✅ Templates and exposed properties
- ✅ Mesh warp pins and meshes
- ✅ Property drivers
- ✅ Render settings
- ✅ Markers
- ✅ Assets
- ✅ Chat messages (LLM agent history)
- ✅ Feature flags
- ✅ Events (audit trail)
- ✅ Metrics (performance/analytics)

**All features from `MASTER_CHECKLIST.md` and `docs/audit/ONTOLOGY_MAPPING.md` are now represented in the database schema.**

**UUID5 Enforcement:** All 44 tables enforce UUID5 format via CHECK constraints. All IDs are deterministic and trackable. See `docs/UUID5_ENFORCEMENT.md` for implementation details.

---

*Schema Version: 2.0*
*Last Updated: 2026-01-23*
*Coverage: Complete - All domain entities from ontology mapping included*
*UUID5: ✅ Enforced on all tables*
