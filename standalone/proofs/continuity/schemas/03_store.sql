-- 03_store.sql
-- Continuity Build System - Database Schema
--
-- STORE TABLES
--
-- Based on continuity.lean section 2 (The Store):
-- - Content-addressed store paths
-- - R2 object store (S3-compatible)
-- - Git refs and objects for attestation
--
-- Designed for PostgreSQL 15+

--------------------------------------------------------------------------------
-- ENUMS
--------------------------------------------------------------------------------

-- Store path type
CREATE TYPE store_path_type AS ENUM (
  'source',      -- Source file
  'derivation',  -- Build derivation
  'output',      -- Build output
  'toolchain',   -- Toolchain component
  'sysroot'      -- System root
);

-- Git object type
CREATE TYPE git_object_type AS ENUM (
  'blob',
  'tree',
  'commit',
  'tag'
);

-- R2 storage class
CREATE TYPE storage_class AS ENUM (
  'standard',
  'infrequent',
  'glacier'
);

--------------------------------------------------------------------------------
-- STORE PATH TABLES
--------------------------------------------------------------------------------

-- Content-addressed store paths (StorePath structure)
CREATE TABLE store_paths (
  hash            BYTEA PRIMARY KEY CHECK (length(hash) = 32),
  name            TEXT NOT NULL,
  path_type       store_path_type NOT NULL DEFAULT 'output',
  size_bytes      BIGINT NOT NULL CHECK (size_bytes >= 0),
  -- R2 storage reference
  r2_bucket       VARCHAR(255),
  r2_key          TEXT,
  storage_class   storage_class NOT NULL DEFAULT 'standard',
  -- Integrity
  content_type    VARCHAR(255),
  executable      BOOLEAN NOT NULL DEFAULT false,
  -- References to other store paths (for garbage collection)
  references      BYTEA[] NOT NULL DEFAULT '{}',
  -- Metadata
  metadata        JSONB NOT NULL DEFAULT '{}',
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- All reference hashes must be valid
  CONSTRAINT valid_references CHECK (
    array_length(references, 1) IS NULL OR
    NOT EXISTS (
      SELECT 1 FROM unnest(references) AS ref
      WHERE length(ref) != 32
    )
  )
);

-- Derivation definitions (Derivation structure)
CREATE TABLE derivations (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  -- Content hash of derivation (determines store path)
  drv_hash        BYTEA NOT NULL CHECK (length(drv_hash) = 32),
  name            VARCHAR(255) NOT NULL,
  -- Builder store path
  builder_hash    BYTEA NOT NULL CHECK (length(builder_hash) = 32),
  -- Build arguments
  args            TEXT[] NOT NULL DEFAULT '{}',
  -- Environment variables
  env             JSONB NOT NULL DEFAULT '{}',
  -- Output names
  output_names    TEXT[] NOT NULL DEFAULT '{}',
  -- Platform requirements
  required_arch   arch,
  required_os     os,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique derivation hash
  CONSTRAINT unique_drv_hash UNIQUE (drv_hash)
);

-- Derivation inputs (Finset StorePath)
CREATE TABLE derivation_inputs (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  derivation_id   UUID NOT NULL REFERENCES derivations(id) ON DELETE CASCADE,
  input_hash      BYTEA NOT NULL CHECK (length(input_hash) = 32),
  input_name      VARCHAR(255) NOT NULL,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique input per derivation
  CONSTRAINT unique_drv_input UNIQUE (derivation_id, input_hash)
);

-- Derivation outputs (DrvOutput structure)
CREATE TABLE derivation_outputs (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  derivation_id   UUID NOT NULL REFERENCES derivations(id) ON DELETE CASCADE,
  output_name     VARCHAR(255) NOT NULL,
  output_hash     BYTEA NOT NULL CHECK (length(output_hash) = 32),
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique output name per derivation
  CONSTRAINT unique_drv_output UNIQUE (derivation_id, output_name)
);

--------------------------------------------------------------------------------
-- R2 STORE TABLES
--------------------------------------------------------------------------------

-- R2 store configuration (R2Store structure)
CREATE TABLE r2_stores (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name            VARCHAR(255) NOT NULL UNIQUE,
  bucket          VARCHAR(255) NOT NULL,
  endpoint        VARCHAR(500) NOT NULL,
  region          VARCHAR(50),
  -- Credentials (encrypted or reference to secrets manager)
  access_key_id   VARCHAR(255),
  secret_key_ref  VARCHAR(500),  -- Reference to secrets manager
  active          BOOLEAN NOT NULL DEFAULT true,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

-- R2 object upload records
CREATE TABLE r2_uploads (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  store_id        UUID NOT NULL REFERENCES r2_stores(id),
  store_path_hash BYTEA NOT NULL REFERENCES store_paths(hash),
  r2_key          TEXT NOT NULL,
  etag            VARCHAR(255),
  upload_started  TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  upload_completed TIMESTAMPTZ,
  upload_failed   TIMESTAMPTZ,
  error_message   TEXT,
  retry_count     INTEGER NOT NULL DEFAULT 0,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Track upload state
  CONSTRAINT upload_state CHECK (
    (upload_completed IS NULL AND upload_failed IS NULL) OR
    (upload_completed IS NOT NULL AND upload_failed IS NULL) OR
    (upload_completed IS NULL AND upload_failed IS NOT NULL)
  )
);

--------------------------------------------------------------------------------
-- GIT TABLES
--------------------------------------------------------------------------------

-- Git refs (GitRef structure)
CREATE TABLE git_refs (
  name            TEXT PRIMARY KEY,
  hash            BYTEA NOT NULL CHECK (length(hash) = 32),
  -- Ref metadata
  ref_type        VARCHAR(50) NOT NULL DEFAULT 'branch',
  symbolic        BOOLEAN NOT NULL DEFAULT false,
  symbolic_target TEXT,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Symbolic refs must have target
  CONSTRAINT symbolic_consistency CHECK (
    (symbolic = false AND symbolic_target IS NULL) OR
    (symbolic = true AND symbolic_target IS NOT NULL)
  )
);

-- Git objects (GitObject structure)
CREATE TABLE git_objects (
  hash            BYTEA PRIMARY KEY CHECK (length(hash) = 32),
  object_type     git_object_type NOT NULL,
  content         BYTEA NOT NULL,
  size_bytes      BIGINT NOT NULL CHECK (size_bytes >= 0),
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Content must match declared size
  CONSTRAINT content_size CHECK (length(content) = size_bytes)
);

-- Git commit metadata (extracted from commit objects)
CREATE TABLE git_commits (
  hash            BYTEA PRIMARY KEY REFERENCES git_objects(hash),
  tree_hash       BYTEA NOT NULL CHECK (length(tree_hash) = 32),
  parent_hashes   BYTEA[] NOT NULL DEFAULT '{}',
  author_name     VARCHAR(255) NOT NULL,
  author_email    VARCHAR(255) NOT NULL,
  author_time     TIMESTAMPTZ NOT NULL,
  committer_name  VARCHAR(255) NOT NULL,
  committer_email VARCHAR(255) NOT NULL,
  committer_time  TIMESTAMPTZ NOT NULL,
  message         TEXT NOT NULL,
  -- GPG signature if present
  gpg_signature   BYTEA,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

--------------------------------------------------------------------------------
-- STORE TABLES (unified view)
--------------------------------------------------------------------------------

-- Unified store (Store structure from continuity.lean)
CREATE TABLE stores (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name            VARCHAR(255) NOT NULL UNIQUE,
  r2_store_id     UUID REFERENCES r2_stores(id),
  -- Local cache settings
  local_cache_path TEXT,
  max_cache_bytes BIGINT,
  -- GC settings
  gc_enabled      BOOLEAN NOT NULL DEFAULT true,
  gc_keep_days    INTEGER NOT NULL DEFAULT 30,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

--------------------------------------------------------------------------------
-- INDEXES
--------------------------------------------------------------------------------

-- Store path indexes
CREATE INDEX idx_store_paths_name ON store_paths(name);
CREATE INDEX idx_store_paths_type ON store_paths(path_type);
CREATE INDEX idx_store_paths_bucket ON store_paths(r2_bucket);
CREATE INDEX idx_store_paths_created ON store_paths(created_at DESC);
CREATE INDEX idx_store_paths_refs ON store_paths USING GIN(references);

-- Derivation indexes
CREATE INDEX idx_derivations_hash ON derivations(drv_hash);
CREATE INDEX idx_derivations_builder ON derivations(builder_hash);
CREATE INDEX idx_derivations_name ON derivations(name);

-- Derivation input/output indexes
CREATE INDEX idx_drv_inputs_derivation ON derivation_inputs(derivation_id);
CREATE INDEX idx_drv_inputs_hash ON derivation_inputs(input_hash);
CREATE INDEX idx_drv_outputs_derivation ON derivation_outputs(derivation_id);
CREATE INDEX idx_drv_outputs_hash ON derivation_outputs(output_hash);

-- R2 indexes
CREATE INDEX idx_r2_uploads_store ON r2_uploads(store_id);
CREATE INDEX idx_r2_uploads_path ON r2_uploads(store_path_hash);
CREATE INDEX idx_r2_uploads_pending ON r2_uploads(upload_started)
  WHERE upload_completed IS NULL AND upload_failed IS NULL;

-- Git indexes
CREATE INDEX idx_git_refs_hash ON git_refs(hash);
CREATE INDEX idx_git_objects_type ON git_objects(object_type);
CREATE INDEX idx_git_commits_tree ON git_commits(tree_hash);
CREATE INDEX idx_git_commits_author_time ON git_commits(author_time DESC);

--------------------------------------------------------------------------------
-- TRIGGERS
--------------------------------------------------------------------------------

CREATE TRIGGER store_paths_updated_at
  BEFORE UPDATE ON store_paths
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER r2_stores_updated_at
  BEFORE UPDATE ON r2_stores
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER git_refs_updated_at
  BEFORE UPDATE ON git_refs
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER stores_updated_at
  BEFORE UPDATE ON stores
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

--------------------------------------------------------------------------------
-- VIEWS
--------------------------------------------------------------------------------

-- Store paths with R2 info
CREATE VIEW store_path_details AS
SELECT
  sp.hash,
  sp.name,
  sp.path_type,
  sp.size_bytes,
  sp.r2_bucket,
  sp.r2_key,
  sp.storage_class,
  sp.executable,
  array_length(sp.references, 1) AS ref_count,
  sp.created_at
FROM store_paths sp;

-- Derivation with inputs and outputs
CREATE VIEW derivation_details AS
SELECT
  d.id,
  d.drv_hash,
  d.name,
  d.builder_hash,
  d.args,
  d.output_names,
  d.required_arch,
  d.required_os,
  (SELECT COUNT(*) FROM derivation_inputs di WHERE di.derivation_id = d.id) AS input_count,
  (SELECT COUNT(*) FROM derivation_outputs do WHERE do.derivation_id = d.id) AS output_count,
  d.created_at
FROM derivations d;

-- Git commit history
CREATE VIEW git_commit_history AS
SELECT
  gc.hash,
  gc.tree_hash,
  gc.author_name,
  gc.author_email,
  gc.author_time,
  gc.message,
  array_length(gc.parent_hashes, 1) AS parent_count,
  gc.gpg_signature IS NOT NULL AS signed
FROM git_commits gc
ORDER BY gc.author_time DESC;

--------------------------------------------------------------------------------
-- FUNCTIONS
--------------------------------------------------------------------------------

-- Check if store contains a path
CREATE OR REPLACE FUNCTION store_contains(p_hash BYTEA)
RETURNS BOOLEAN AS $$
BEGIN
  RETURN EXISTS (SELECT 1 FROM store_paths WHERE hash = p_hash);
END;
$$ LANGUAGE plpgsql STABLE;

-- Get closure of a store path (all transitive references)
CREATE OR REPLACE FUNCTION get_closure(p_hash BYTEA)
RETURNS SETOF BYTEA AS $$
BEGIN
  RETURN QUERY
  WITH RECURSIVE closure AS (
    -- Base case
    SELECT p_hash AS hash

    UNION

    -- Recursive case
    SELECT unnest(sp.references)
    FROM closure c
    JOIN store_paths sp ON c.hash = sp.hash
    WHERE sp.references IS NOT NULL
      AND array_length(sp.references, 1) > 0
  )
  SELECT DISTINCT hash FROM closure;
END;
$$ LANGUAGE plpgsql STABLE;

-- Get closure size in bytes
CREATE OR REPLACE FUNCTION get_closure_size(p_hash BYTEA)
RETURNS BIGINT AS $$
BEGIN
  RETURN (
    SELECT COALESCE(SUM(sp.size_bytes), 0)
    FROM store_paths sp
    WHERE sp.hash IN (SELECT get_closure(p_hash))
  );
END;
$$ LANGUAGE plpgsql STABLE;

-- Register a new store path
CREATE OR REPLACE FUNCTION register_store_path(
  p_hash BYTEA,
  p_name TEXT,
  p_type store_path_type,
  p_size BIGINT,
  p_references BYTEA[] DEFAULT '{}'
)
RETURNS VOID AS $$
BEGIN
  INSERT INTO store_paths (hash, name, path_type, size_bytes, references)
  VALUES (p_hash, p_name, p_type, p_size, p_references)
  ON CONFLICT (hash) DO NOTHING;
END;
$$ LANGUAGE plpgsql;

-- Git object content-addressing verification
CREATE OR REPLACE FUNCTION verify_git_object(p_hash BYTEA)
RETURNS BOOLEAN AS $$
DECLARE
  v_content BYTEA;
  v_computed BYTEA;
BEGIN
  SELECT content INTO v_content FROM git_objects WHERE hash = p_hash;

  IF v_content IS NULL THEN
    RETURN FALSE;
  END IF;

  -- Note: In production, would compute actual git object hash
  -- This is a placeholder that assumes content is valid
  RETURN TRUE;
END;
$$ LANGUAGE plpgsql STABLE;

--------------------------------------------------------------------------------
-- COMMENTS
--------------------------------------------------------------------------------

COMMENT ON TABLE store_paths IS
  'Content-addressed store paths from continuity.lean StorePath structure';
COMMENT ON TABLE derivations IS
  'Build derivations from continuity.lean Derivation structure';
COMMENT ON TABLE derivation_inputs IS
  'Input store paths for derivations (Finset StorePath)';
COMMENT ON TABLE derivation_outputs IS
  'Output store paths from derivations (DrvOutput structure)';
COMMENT ON TABLE r2_stores IS
  'R2 object store configuration from continuity.lean R2Store structure';
COMMENT ON TABLE git_refs IS
  'Git references from continuity.lean GitRef structure';
COMMENT ON TABLE git_objects IS
  'Git objects from continuity.lean GitObject structure';
COMMENT ON TABLE stores IS
  'Unified store configuration from continuity.lean Store structure';

COMMENT ON COLUMN store_paths.hash IS
  'SHA-256 content hash (32 bytes)';
COMMENT ON COLUMN store_paths.references IS
  'Array of referenced store path hashes (for GC roots)';
COMMENT ON COLUMN git_objects.hash IS
  'SHA-256 of git object content (32 bytes)';
