-- Core Database Schema
-- Always loaded - required for all functionality

-- Set timezone
SET timezone = 'UTC';

-- Enable extensions
INSTALL 'fts';
LOAD 'fts';

-- ============================================================================
-- UUID5 VALIDATION FUNCTION
-- ============================================================================

-- Validate UUID5 format (RFC 4122)
-- Pattern: 8-4-4-4-12 hex digits, version 5, variant RFC 4122
CREATE OR REPLACE FUNCTION is_uuid5(id TEXT) RETURNS BOOLEAN AS $$
    SELECT 
        length(id) = 36 AND
        substr(id, 15, 1) = '5' AND  -- Version 5
        substr(id, 20, 1) IN ('8', '9', 'a', 'b') AND  -- Variant RFC 4122
        id ~ '^[0-9a-f]{8}-[0-9a-f]{4}-5[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$';
$$;

-- ============================================================================
-- CORE TABLES
-- ============================================================================

-- Projects
CREATE TABLE IF NOT EXISTS projects (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    name TEXT NOT NULL,
    version INTEGER NOT NULL DEFAULT 1,
    fps INTEGER NOT NULL DEFAULT 30,
    width INTEGER NOT NULL DEFAULT 1920,
    height INTEGER NOT NULL DEFAULT 1080,
    duration_frames INTEGER NOT NULL DEFAULT 0,
    metadata JSON NOT NULL DEFAULT '{}',
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

-- Compositions
CREATE TABLE IF NOT EXISTS compositions (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    project_id TEXT NOT NULL REFERENCES projects(id) ON DELETE CASCADE,
    name TEXT NOT NULL,
    width INTEGER NOT NULL,
    height INTEGER NOT NULL,
    fps INTEGER NOT NULL,
    duration_frames INTEGER NOT NULL DEFAULT 0,
    background_color TEXT NOT NULL DEFAULT '#000000',
    settings JSON NOT NULL DEFAULT '{}',
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

-- Layers
CREATE TABLE IF NOT EXISTS layers (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    composition_id TEXT NOT NULL REFERENCES compositions(id) ON DELETE CASCADE,
    parent_id TEXT REFERENCES layers(id) ON DELETE CASCADE,
    name TEXT NOT NULL,
    layer_type TEXT NOT NULL,
    order_index INTEGER NOT NULL DEFAULT 0,
    visible BOOLEAN NOT NULL DEFAULT true,
    locked BOOLEAN NOT NULL DEFAULT false,
    opacity REAL NOT NULL DEFAULT 1.0 CHECK (opacity >= 0 AND opacity <= 1),
    blend_mode TEXT NOT NULL DEFAULT 'normal',
    start_frame INTEGER NOT NULL DEFAULT 0,
    end_frame INTEGER NOT NULL DEFAULT 0,
    transform JSON NOT NULL DEFAULT '{}',
    mask JSON,
    data JSON NOT NULL,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

-- Keyframes
CREATE TABLE IF NOT EXISTS keyframes (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    property_path TEXT NOT NULL,
    frame INTEGER NOT NULL,
    value JSON NOT NULL,
    interpolation_type TEXT NOT NULL DEFAULT 'linear',
    easing_type TEXT NOT NULL DEFAULT 'ease',
    in_tangent REAL,
    out_tangent REAL,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

-- Expressions
CREATE TABLE IF NOT EXISTS expressions (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    layer_id TEXT NOT NULL REFERENCES layers(id) ON DELETE CASCADE,
    property_path TEXT NOT NULL,
    expression_text TEXT NOT NULL,
    enabled BOOLEAN NOT NULL DEFAULT true,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

-- Assets
CREATE TABLE IF NOT EXISTS assets (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    project_id TEXT NOT NULL REFERENCES projects(id) ON DELETE CASCADE,
    name TEXT NOT NULL,
    file_path TEXT NOT NULL,
    asset_type TEXT NOT NULL,
    metadata JSON NOT NULL DEFAULT '{}',
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

-- Chat Messages (LLM Agent History)
CREATE TABLE IF NOT EXISTS chat_messages (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    project_id TEXT REFERENCES projects(id) ON DELETE CASCADE,
    role TEXT NOT NULL,
    content TEXT NOT NULL,
    tool_calls JSON,
    tool_call_id TEXT,
    model TEXT,
    tokens_used INTEGER DEFAULT 0,
    cost_usd REAL DEFAULT 0.0,
    timestamp INTEGER NOT NULL,
    created_at INTEGER NOT NULL,
    modified_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

-- Feature Flags
CREATE TABLE IF NOT EXISTS feature_flags (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    name TEXT NOT NULL UNIQUE,
    description TEXT NOT NULL,
    enabled_by_default BOOLEAN NOT NULL DEFAULT false,
    category TEXT NOT NULL,
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL
);

-- Events (Audit Trail)
CREATE TABLE IF NOT EXISTS events (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    event_type TEXT NOT NULL,
    project_id TEXT REFERENCES projects(id) ON DELETE CASCADE,
    composition_id TEXT REFERENCES compositions(id) ON DELETE CASCADE,
    layer_id TEXT REFERENCES layers(id) ON DELETE CASCADE,
    user_id TEXT,
    data JSON NOT NULL DEFAULT '{}',
    timestamp INTEGER NOT NULL,
    created_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

-- Metrics (Performance/Analytics)
CREATE TABLE IF NOT EXISTS metrics (
    id TEXT PRIMARY KEY,
    metric_name TEXT NOT NULL,
    category TEXT NOT NULL,
    project_id TEXT REFERENCES projects(id) ON DELETE CASCADE,
    composition_id TEXT REFERENCES compositions(id) ON DELETE CASCADE,
    value REAL NOT NULL,
    unit TEXT NOT NULL,
    timestamp INTEGER NOT NULL,
    created_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

-- Markers
CREATE TABLE IF NOT EXISTS markers (
    id TEXT PRIMARY KEY CHECK (is_uuid5(id)),
    composition_id TEXT NOT NULL REFERENCES compositions(id) ON DELETE CASCADE,
    frame INTEGER NOT NULL,
    label TEXT NOT NULL DEFAULT '',
    color TEXT NOT NULL DEFAULT '#FF0000',
    duration INTEGER NOT NULL DEFAULT 0,
    comment TEXT NOT NULL DEFAULT '',
    created_at INTEGER NOT NULL,
    updated_at INTEGER NOT NULL,
    feature_flags JSON NOT NULL DEFAULT '{}'
);

-- ============================================================================
-- CORE INDEXES
-- ============================================================================

CREATE INDEX IF NOT EXISTS idx_projects_name ON projects(name);
CREATE INDEX IF NOT EXISTS idx_projects_created_at ON projects(created_at);

CREATE INDEX IF NOT EXISTS idx_compositions_project_id ON compositions(project_id);
CREATE INDEX IF NOT EXISTS idx_compositions_name ON compositions(name);

CREATE INDEX IF NOT EXISTS idx_layers_composition_id ON layers(composition_id);
CREATE INDEX IF NOT EXISTS idx_layers_parent_id ON layers(parent_id);
CREATE INDEX IF NOT EXISTS idx_layers_type ON layers(layer_type);
CREATE INDEX IF NOT EXISTS idx_layers_order ON layers(composition_id, order_index);
CREATE INDEX IF NOT EXISTS idx_layers_frame_range ON layers(start_frame, end_frame);

CREATE INDEX IF NOT EXISTS idx_keyframes_layer_id ON keyframes(layer_id);
CREATE INDEX IF NOT EXISTS idx_keyframes_property ON keyframes(layer_id, property_path);
CREATE INDEX IF NOT EXISTS idx_keyframes_frame ON keyframes(layer_id, frame);
CREATE UNIQUE INDEX IF NOT EXISTS idx_keyframes_unique ON keyframes(layer_id, property_path, frame);

CREATE INDEX IF NOT EXISTS idx_expressions_layer_id ON expressions(layer_id);
CREATE INDEX IF NOT EXISTS idx_expressions_property ON expressions(layer_id, property_path);
CREATE UNIQUE INDEX IF NOT EXISTS idx_expressions_unique ON expressions(layer_id, property_path);

CREATE INDEX IF NOT EXISTS idx_assets_project_id ON assets(project_id);
CREATE INDEX IF NOT EXISTS idx_assets_type ON assets(asset_type);

CREATE INDEX IF NOT EXISTS idx_chat_project_id ON chat_messages(project_id);
CREATE INDEX IF NOT EXISTS idx_chat_timestamp ON chat_messages(timestamp);
CREATE INDEX IF NOT EXISTS idx_chat_role ON chat_messages(role);
CREATE INDEX IF NOT EXISTS idx_chat_tool_call_id ON chat_messages(tool_call_id);

CREATE INDEX IF NOT EXISTS idx_feature_flags_category ON feature_flags(category);
CREATE INDEX IF NOT EXISTS idx_feature_flags_enabled ON feature_flags(enabled_by_default);

CREATE INDEX IF NOT EXISTS idx_events_type ON events(event_type);
CREATE INDEX IF NOT EXISTS idx_events_project_id ON events(project_id);
CREATE INDEX IF NOT EXISTS idx_events_timestamp ON events(timestamp);
CREATE INDEX IF NOT EXISTS idx_events_composition_id ON events(composition_id);
CREATE INDEX IF NOT EXISTS idx_events_layer_id ON events(layer_id);

CREATE INDEX IF NOT EXISTS idx_metrics_name ON metrics(metric_name);
CREATE INDEX IF NOT EXISTS idx_metrics_category ON metrics(category);
CREATE INDEX IF NOT EXISTS idx_metrics_project_id ON metrics(project_id);
CREATE INDEX IF NOT EXISTS idx_metrics_timestamp ON metrics(timestamp);

CREATE INDEX IF NOT EXISTS idx_markers_composition_id ON markers(composition_id);
CREATE INDEX IF NOT EXISTS idx_markers_frame ON markers(composition_id, frame);

-- ============================================================================
-- CORE VIEWS
-- ============================================================================

CREATE OR REPLACE VIEW active_layers AS
SELECT 
    l.*,
    c.name AS composition_name,
    c.project_id
FROM layers l
JOIN compositions c ON l.composition_id = c.id
WHERE l.visible = true;

CREATE OR REPLACE VIEW layer_hierarchy AS
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

CREATE OR REPLACE VIEW keyframe_timeline AS
SELECT 
    k.*,
    l.name AS layer_name,
    l.composition_id,
    c.name AS composition_name
FROM keyframes k
JOIN layers l ON k.layer_id = l.id
JOIN compositions c ON l.composition_id = c.id
ORDER BY k.frame, l.order_index;

-- ============================================================================
-- CORE FUNCTIONS
-- ============================================================================

CREATE OR REPLACE FUNCTION feature_enabled(entity_flags JSON, feature_name TEXT) 
RETURNS BOOLEAN AS $$
    SELECT COALESCE(
        json_extract(entity_flags, '$.' || feature_name),
        (SELECT enabled_by_default FROM feature_flags WHERE name = feature_name)
    ) = true;
$$;

-- ============================================================================
-- FULL-TEXT SEARCH
-- ============================================================================

CREATE VIRTUAL TABLE IF NOT EXISTS chat_messages_fts USING fts5(
    content,
    content='chat_messages',
    content_rowid='rowid'
);

CREATE TRIGGER IF NOT EXISTS chat_messages_fts_insert AFTER INSERT ON chat_messages BEGIN
    INSERT INTO chat_messages_fts(rowid, content) VALUES (new.rowid, new.content);
END;

CREATE TRIGGER IF NOT EXISTS chat_messages_fts_delete AFTER DELETE ON chat_messages BEGIN
    INSERT INTO chat_messages_fts(chat_messages_fts, rowid, content) VALUES('delete', old.rowid, old.content);
END;

CREATE TRIGGER IF NOT EXISTS chat_messages_fts_update AFTER UPDATE ON chat_messages BEGIN
    INSERT INTO chat_messages_fts(chat_messages_fts, rowid, content) VALUES('delete', old.rowid, old.content);
    INSERT INTO chat_messages_fts(rowid, content) VALUES (new.rowid, new.content);
END;
