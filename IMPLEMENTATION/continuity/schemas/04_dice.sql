-- 04_dice.sql
-- Continuity Build System - Database Schema
--
-- DICE TABLES
--
-- Based on continuity.lean section 4 (DICE: The Build Engine):
-- - Actions: units of computation
-- - Action graphs: dependency DAGs
-- - Deterministic execution
--
-- Designed for PostgreSQL 15+

--------------------------------------------------------------------------------
-- ENUMS
--------------------------------------------------------------------------------

-- Action execution status
CREATE TYPE action_status AS ENUM (
  'pending',
  'queued',
  'running',
  'completed',
  'failed',
  'cancelled',
  'skipped'  -- Skipped due to cache hit
);

-- Action category (for grouping)
CREATE TYPE action_category AS ENUM (
  'compile',
  'link',
  'test',
  'package',
  'deploy',
  'lint',
  'format',
  'codegen',
  'custom'
);

--------------------------------------------------------------------------------
-- ACTION TABLES
--------------------------------------------------------------------------------

-- DICE actions (Action structure)
CREATE TABLE actions (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  -- Action identity (from Action.key)
  action_key      BYTEA NOT NULL CHECK (length(action_key) = 32),
  category        action_category NOT NULL DEFAULT 'custom',
  identifier      VARCHAR(500) NOT NULL,
  -- Command to execute
  command         TEXT[] NOT NULL,
  -- Environment variables
  env             JSONB NOT NULL DEFAULT '{}',
  -- Expected outputs (names only; paths determined by content)
  output_names    TEXT[] NOT NULL DEFAULT '{}',
  -- Execution constraints
  required_arch   arch,
  required_os     os,
  timeout_seconds INTEGER CHECK (timeout_seconds IS NULL OR timeout_seconds > 0),
  -- Namespace isolation settings
  namespace_user    BOOLEAN NOT NULL DEFAULT true,
  namespace_mount   BOOLEAN NOT NULL DEFAULT true,
  namespace_net     BOOLEAN NOT NULL DEFAULT true,
  namespace_pid     BOOLEAN NOT NULL DEFAULT true,
  namespace_ipc     BOOLEAN NOT NULL DEFAULT true,
  namespace_uts     BOOLEAN NOT NULL DEFAULT true,
  namespace_cgroup  BOOLEAN NOT NULL DEFAULT true,
  -- Metadata
  metadata        JSONB NOT NULL DEFAULT '{}',
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique action key
  CONSTRAINT unique_action_key UNIQUE (action_key)
);

-- Action inputs (Finset StorePath)
CREATE TABLE action_inputs (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  action_id       UUID NOT NULL REFERENCES actions(id) ON DELETE CASCADE,
  input_hash      BYTEA NOT NULL CHECK (length(input_hash) = 32),
  input_name      VARCHAR(500) NOT NULL,
  input_path      TEXT NOT NULL,  -- Mount path inside namespace
  required        BOOLEAN NOT NULL DEFAULT true,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique input per action
  CONSTRAINT unique_action_input UNIQUE (action_id, input_hash)
);

-- Action outputs (produced after execution)
CREATE TABLE action_outputs (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  action_id       UUID NOT NULL REFERENCES actions(id) ON DELETE CASCADE,
  output_name     VARCHAR(500) NOT NULL,
  output_hash     BYTEA CHECK (output_hash IS NULL OR length(output_hash) = 32),
  output_path     TEXT,  -- Path inside namespace where output was produced
  size_bytes      BIGINT CHECK (size_bytes IS NULL OR size_bytes >= 0),
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique output name per action
  CONSTRAINT unique_action_output UNIQUE (action_id, output_name)
);

--------------------------------------------------------------------------------
-- DICE GRAPH TABLES
--------------------------------------------------------------------------------

-- DICE computation graphs (DiceGraph structure)
CREATE TABLE dice_graphs (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name            VARCHAR(255) NOT NULL,
  description     TEXT,
  -- Graph hash (content-addressed)
  graph_hash      BYTEA NOT NULL CHECK (length(graph_hash) = 32),
  -- Root action (entry point)
  root_action_id  UUID,
  -- Proof that graph is acyclic (stored as metadata)
  acyclic_proof   JSONB NOT NULL DEFAULT '{}',
  -- Build state
  status          action_status NOT NULL DEFAULT 'pending',
  started_at      TIMESTAMPTZ,
  completed_at    TIMESTAMPTZ,
  -- Execution statistics
  total_actions   INTEGER NOT NULL DEFAULT 0,
  completed_actions INTEGER NOT NULL DEFAULT 0,
  failed_actions  INTEGER NOT NULL DEFAULT 0,
  cached_actions  INTEGER NOT NULL DEFAULT 0,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique graph hash
  CONSTRAINT unique_graph_hash UNIQUE (graph_hash)
);

-- Graph action membership
CREATE TABLE dice_graph_actions (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  graph_id        UUID NOT NULL REFERENCES dice_graphs(id) ON DELETE CASCADE,
  action_id       UUID NOT NULL REFERENCES actions(id) ON DELETE CASCADE,
  -- Execution order (topological sort order)
  exec_order      INTEGER NOT NULL,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique action per graph
  CONSTRAINT unique_graph_action UNIQUE (graph_id, action_id),
  -- Unique execution order per graph
  CONSTRAINT unique_exec_order UNIQUE (graph_id, exec_order)
);

-- Add foreign key for root action
ALTER TABLE dice_graphs
  ADD CONSTRAINT fk_dice_graphs_root
  FOREIGN KEY (root_action_id) REFERENCES actions(id);

-- DICE edges: action dependencies (deps : Action -> Finset Action)
CREATE TABLE dice_edges (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  graph_id        UUID NOT NULL REFERENCES dice_graphs(id) ON DELETE CASCADE,
  from_action_id  UUID NOT NULL REFERENCES actions(id) ON DELETE CASCADE,
  to_action_id    UUID NOT NULL REFERENCES actions(id) ON DELETE CASCADE,
  edge_type       VARCHAR(50) NOT NULL DEFAULT 'depends',
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- No self-edges
  CONSTRAINT no_self_edge CHECK (from_action_id != to_action_id),
  -- Unique edge per graph
  CONSTRAINT unique_edge UNIQUE (graph_id, from_action_id, to_action_id)
);

--------------------------------------------------------------------------------
-- EXECUTION TABLES
--------------------------------------------------------------------------------

-- Action execution records
CREATE TABLE action_executions (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  action_id       UUID NOT NULL REFERENCES actions(id),
  graph_id        UUID REFERENCES dice_graphs(id),
  -- Execution state
  status          action_status NOT NULL DEFAULT 'pending',
  -- Timing
  queued_at       TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  started_at      TIMESTAMPTZ,
  completed_at    TIMESTAMPTZ,
  -- Execution environment
  worker_id       VARCHAR(255),
  builder_key_id  UUID REFERENCES public_keys(key_id),
  -- Results
  exit_code       INTEGER,
  stdout_hash     BYTEA CHECK (stdout_hash IS NULL OR length(stdout_hash) = 32),
  stderr_hash     BYTEA CHECK (stderr_hash IS NULL OR length(stderr_hash) = 32),
  -- Cache info
  cache_hit       BOOLEAN NOT NULL DEFAULT false,
  cache_key       BYTEA CHECK (cache_key IS NULL OR length(cache_key) = 32),
  -- Resource usage
  cpu_time_ms     BIGINT CHECK (cpu_time_ms IS NULL OR cpu_time_ms >= 0),
  memory_peak_bytes BIGINT CHECK (memory_peak_bytes IS NULL OR memory_peak_bytes >= 0),
  -- Error info
  error_message   TEXT,
  error_details   JSONB,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

-- Execution logs (stored separately for large outputs)
CREATE TABLE execution_logs (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  execution_id    UUID NOT NULL REFERENCES action_executions(id) ON DELETE CASCADE,
  log_type        VARCHAR(50) NOT NULL,  -- stdout, stderr, debug
  content_hash    BYTEA NOT NULL CHECK (length(content_hash) = 32),
  content_size    BIGINT NOT NULL CHECK (content_size >= 0),
  -- Content stored in R2, reference here
  r2_key          TEXT,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

--------------------------------------------------------------------------------
-- CACHE TABLES
--------------------------------------------------------------------------------

-- Action cache (for deterministic replay)
CREATE TABLE action_cache (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  -- Cache key is action_key
  action_key      BYTEA NOT NULL CHECK (length(action_key) = 32),
  -- Cached output hashes
  output_hashes   JSONB NOT NULL,  -- {output_name: hash}
  -- Cache metadata
  hit_count       INTEGER NOT NULL DEFAULT 0,
  last_hit_at     TIMESTAMPTZ,
  -- Builder info (for reproducibility verification)
  builder_key_id  UUID REFERENCES public_keys(key_id),
  build_time_ms   BIGINT,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique cache entry per action key
  CONSTRAINT unique_cache_entry UNIQUE (action_key)
);

--------------------------------------------------------------------------------
-- INDEXES
--------------------------------------------------------------------------------

-- Action indexes
CREATE INDEX idx_actions_key ON actions(action_key);
CREATE INDEX idx_actions_category ON actions(category);
CREATE INDEX idx_actions_identifier ON actions(identifier);
CREATE INDEX idx_actions_created ON actions(created_at DESC);

-- Action input/output indexes
CREATE INDEX idx_action_inputs_action ON action_inputs(action_id);
CREATE INDEX idx_action_inputs_hash ON action_inputs(input_hash);
CREATE INDEX idx_action_outputs_action ON action_outputs(action_id);
CREATE INDEX idx_action_outputs_hash ON action_outputs(output_hash);

-- Graph indexes
CREATE INDEX idx_dice_graphs_hash ON dice_graphs(graph_hash);
CREATE INDEX idx_dice_graphs_status ON dice_graphs(status);
CREATE INDEX idx_dice_graphs_created ON dice_graphs(created_at DESC);

-- Graph action indexes
CREATE INDEX idx_graph_actions_graph ON dice_graph_actions(graph_id);
CREATE INDEX idx_graph_actions_action ON dice_graph_actions(action_id);
CREATE INDEX idx_graph_actions_order ON dice_graph_actions(graph_id, exec_order);

-- Edge indexes
CREATE INDEX idx_dice_edges_graph ON dice_edges(graph_id);
CREATE INDEX idx_dice_edges_from ON dice_edges(from_action_id);
CREATE INDEX idx_dice_edges_to ON dice_edges(to_action_id);

-- Execution indexes
CREATE INDEX idx_executions_action ON action_executions(action_id);
CREATE INDEX idx_executions_graph ON action_executions(graph_id);
CREATE INDEX idx_executions_status ON action_executions(status);
CREATE INDEX idx_executions_started ON action_executions(started_at DESC);
CREATE INDEX idx_executions_cache_key ON action_executions(cache_key);

-- Cache indexes
CREATE INDEX idx_cache_action_key ON action_cache(action_key);
CREATE INDEX idx_cache_last_hit ON action_cache(last_hit_at DESC);

--------------------------------------------------------------------------------
-- TRIGGERS
--------------------------------------------------------------------------------

CREATE TRIGGER actions_updated_at
  BEFORE UPDATE ON actions
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER dice_graphs_updated_at
  BEFORE UPDATE ON dice_graphs
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER action_executions_updated_at
  BEFORE UPDATE ON action_executions
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER action_cache_updated_at
  BEFORE UPDATE ON action_cache
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

-- Update graph statistics on execution completion
CREATE OR REPLACE FUNCTION update_graph_stats()
RETURNS TRIGGER AS $$
BEGIN
  IF NEW.graph_id IS NOT NULL AND NEW.status IN ('completed', 'failed', 'skipped') THEN
    UPDATE dice_graphs
    SET
      completed_actions = completed_actions + CASE WHEN NEW.status = 'completed' THEN 1 ELSE 0 END,
      failed_actions = failed_actions + CASE WHEN NEW.status = 'failed' THEN 1 ELSE 0 END,
      cached_actions = cached_actions + CASE WHEN NEW.cache_hit THEN 1 ELSE 0 END
    WHERE id = NEW.graph_id;
  END IF;
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER execution_update_graph_stats
  AFTER UPDATE ON action_executions
  FOR EACH ROW
  WHEN (OLD.status != NEW.status)
  EXECUTE FUNCTION update_graph_stats();

--------------------------------------------------------------------------------
-- VIEWS
--------------------------------------------------------------------------------

-- Action details with input/output counts
CREATE VIEW action_details AS
SELECT
  a.id,
  a.action_key,
  a.category,
  a.identifier,
  a.command,
  a.output_names,
  (SELECT COUNT(*) FROM action_inputs ai WHERE ai.action_id = a.id) AS input_count,
  (SELECT COUNT(*) FROM action_outputs ao WHERE ao.action_id = a.id) AS output_count,
  a.created_at
FROM actions a;

-- Graph execution summary
CREATE VIEW graph_execution_summary AS
SELECT
  g.id,
  g.name,
  g.status,
  g.total_actions,
  g.completed_actions,
  g.failed_actions,
  g.cached_actions,
  g.started_at,
  g.completed_at,
  EXTRACT(EPOCH FROM (g.completed_at - g.started_at)) AS duration_seconds
FROM dice_graphs g;

-- Action execution history
CREATE VIEW action_execution_history AS
SELECT
  ae.id AS execution_id,
  a.identifier AS action_identifier,
  a.category,
  ae.status,
  ae.cache_hit,
  ae.exit_code,
  ae.started_at,
  ae.completed_at,
  ae.cpu_time_ms,
  ae.memory_peak_bytes,
  ae.error_message
FROM action_executions ae
JOIN actions a ON ae.action_id = a.id
ORDER BY ae.started_at DESC;

--------------------------------------------------------------------------------
-- FUNCTIONS
--------------------------------------------------------------------------------

-- Check if action graph is acyclic using DFS
CREATE OR REPLACE FUNCTION is_graph_acyclic(p_graph_id UUID)
RETURNS BOOLEAN AS $$
DECLARE
  v_has_cycle BOOLEAN;
BEGIN
  -- Use recursive CTE to detect cycles
  WITH RECURSIVE path AS (
    SELECT
      from_action_id,
      to_action_id,
      ARRAY[from_action_id] AS visited,
      FALSE AS has_cycle
    FROM dice_edges
    WHERE graph_id = p_graph_id

    UNION ALL

    SELECT
      e.from_action_id,
      e.to_action_id,
      p.visited || e.from_action_id,
      e.to_action_id = ANY(p.visited)
    FROM path p
    JOIN dice_edges e ON p.to_action_id = e.from_action_id
    WHERE e.graph_id = p_graph_id
      AND NOT p.has_cycle
      AND NOT e.from_action_id = ANY(p.visited)
  )
  SELECT EXISTS (SELECT 1 FROM path WHERE has_cycle) INTO v_has_cycle;

  RETURN NOT v_has_cycle;
END;
$$ LANGUAGE plpgsql STABLE;

-- Get topological order of actions in graph
CREATE OR REPLACE FUNCTION get_topological_order(p_graph_id UUID)
RETURNS TABLE(action_id UUID, topo_order INTEGER) AS $$
BEGIN
  RETURN QUERY
  WITH RECURSIVE topo AS (
    -- Actions with no dependencies (roots)
    SELECT
      ga.action_id,
      0 AS level
    FROM dice_graph_actions ga
    WHERE ga.graph_id = p_graph_id
      AND NOT EXISTS (
        SELECT 1 FROM dice_edges e
        WHERE e.graph_id = p_graph_id
          AND e.to_action_id = ga.action_id
      )

    UNION ALL

    -- Actions whose dependencies are all processed
    SELECT
      ga.action_id,
      t.level + 1
    FROM dice_graph_actions ga
    JOIN dice_edges e ON ga.action_id = e.to_action_id AND e.graph_id = p_graph_id
    JOIN topo t ON e.from_action_id = t.action_id
    WHERE ga.graph_id = p_graph_id
  )
  SELECT DISTINCT ON (t.action_id) t.action_id, t.level
  FROM topo t
  ORDER BY t.action_id, t.level DESC;
END;
$$ LANGUAGE plpgsql STABLE;

-- Check cache for action
CREATE OR REPLACE FUNCTION check_action_cache(p_action_key BYTEA)
RETURNS TABLE(cached BOOLEAN, output_hashes JSONB) AS $$
BEGIN
  UPDATE action_cache
  SET hit_count = hit_count + 1, last_hit_at = NOW()
  WHERE action_key = p_action_key;

  RETURN QUERY
  SELECT
    TRUE AS cached,
    ac.output_hashes
  FROM action_cache ac
  WHERE ac.action_key = p_action_key;

  IF NOT FOUND THEN
    RETURN QUERY SELECT FALSE, NULL::JSONB;
  END IF;
END;
$$ LANGUAGE plpgsql;

-- Record action execution result
CREATE OR REPLACE FUNCTION record_action_result(
  p_action_id UUID,
  p_graph_id UUID,
  p_status action_status,
  p_exit_code INTEGER,
  p_output_hashes JSONB DEFAULT NULL
)
RETURNS UUID AS $$
DECLARE
  v_execution_id UUID;
  v_action_key BYTEA;
BEGIN
  -- Create execution record
  INSERT INTO action_executions (action_id, graph_id, status, exit_code, completed_at)
  VALUES (p_action_id, p_graph_id, p_status, p_exit_code, NOW())
  RETURNING id INTO v_execution_id;

  -- Update cache on success
  IF p_status = 'completed' AND p_output_hashes IS NOT NULL THEN
    SELECT action_key INTO v_action_key FROM actions WHERE id = p_action_id;

    INSERT INTO action_cache (action_key, output_hashes)
    VALUES (v_action_key, p_output_hashes)
    ON CONFLICT (action_key) DO UPDATE
    SET output_hashes = p_output_hashes, updated_at = NOW();
  END IF;

  RETURN v_execution_id;
END;
$$ LANGUAGE plpgsql;

--------------------------------------------------------------------------------
-- COMMENTS
--------------------------------------------------------------------------------

COMMENT ON TABLE actions IS
  'DICE actions from continuity.lean Action structure';
COMMENT ON TABLE action_inputs IS
  'Action input store paths (Finset StorePath)';
COMMENT ON TABLE action_outputs IS
  'Action output store paths (DrvOutput)';
COMMENT ON TABLE dice_graphs IS
  'DICE computation graphs from continuity.lean DiceGraph structure';
COMMENT ON TABLE dice_edges IS
  'Action dependencies (deps : Action -> Finset Action)';
COMMENT ON TABLE action_executions IS
  'Action execution records with timing and results';
COMMENT ON TABLE action_cache IS
  'Deterministic action cache for replay';

COMMENT ON COLUMN actions.action_key IS
  'Content hash of action (inputs + command + env)';
COMMENT ON COLUMN actions.namespace_user IS
  'Enable CLONE_NEWUSER namespace isolation';
COMMENT ON COLUMN dice_graphs.acyclic_proof IS
  'Proof metadata that graph has no cycles';
COMMENT ON COLUMN action_cache.action_key IS
  'Cache key (same as Action.key)';
