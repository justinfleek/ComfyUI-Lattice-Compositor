-- 05_config.sql
-- Continuity Build System - Database Schema
--
-- CONFIGURATION TABLES
--
-- Based on continuity.lean section 15 (The Continuity Stack):
-- - ContinuityConfig structure
-- - Namespace isolation settings
-- - MicroVM (isospin) configuration
-- - Dhall BUILD file tracking
--
-- Designed for PostgreSQL 15+

--------------------------------------------------------------------------------
-- ENUMS
--------------------------------------------------------------------------------

-- Config status
CREATE TYPE config_status AS ENUM (
  'draft',
  'active',
  'deprecated',
  'archived'
);

-- Isolation level
CREATE TYPE isolation_level AS ENUM (
  'none',        -- No isolation
  'namespace',   -- Linux namespace isolation
  'microvm'      -- Full MicroVM isolation
);

--------------------------------------------------------------------------------
-- NAMESPACE CONFIGURATION
--------------------------------------------------------------------------------

-- Namespace configurations (Namespace structure)
CREATE TABLE namespace_configs (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name            VARCHAR(255) NOT NULL UNIQUE,
  description     TEXT,
  -- Namespace flags (from Namespace structure)
  ns_user         BOOLEAN NOT NULL DEFAULT true,   -- CLONE_NEWUSER
  ns_mount        BOOLEAN NOT NULL DEFAULT true,   -- CLONE_NEWNS
  ns_net          BOOLEAN NOT NULL DEFAULT true,   -- CLONE_NEWNET
  ns_pid          BOOLEAN NOT NULL DEFAULT true,   -- CLONE_NEWPID
  ns_ipc          BOOLEAN NOT NULL DEFAULT true,   -- CLONE_NEWIPC
  ns_uts          BOOLEAN NOT NULL DEFAULT true,   -- CLONE_NEWUTS
  ns_cgroup       BOOLEAN NOT NULL DEFAULT true,   -- CLONE_NEWCGROUP
  -- Additional settings
  seccomp_profile TEXT,
  apparmor_profile TEXT,
  capabilities    TEXT[] NOT NULL DEFAULT '{}',
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

-- Insert default full isolation namespace
INSERT INTO namespace_configs (name, description)
VALUES ('full', 'Full namespace isolation (Namespace.full from continuity.lean)');

--------------------------------------------------------------------------------
-- MICROVM CONFIGURATION
--------------------------------------------------------------------------------

-- MicroVM configurations (MicroVM/Isospin structure)
CREATE TABLE microvm_configs (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name            VARCHAR(255) NOT NULL UNIQUE,
  description     TEXT,
  -- MicroVM settings (from MicroVM structure)
  kernel_hash     BYTEA NOT NULL CHECK (length(kernel_hash) = 32),
  kernel_name     VARCHAR(255) NOT NULL,
  rootfs_hash     BYTEA NOT NULL CHECK (length(rootfs_hash) = 32),
  rootfs_name     VARCHAR(255) NOT NULL,
  vcpus           INTEGER NOT NULL CHECK (vcpus > 0),
  mem_mb          INTEGER NOT NULL CHECK (mem_mb > 0),
  net_enabled     BOOLEAN NOT NULL DEFAULT false,
  gpu_passthrough BOOLEAN NOT NULL DEFAULT false,
  -- Isospin properties
  kernel_minimal  BOOLEAN NOT NULL DEFAULT true,
  drivers_verified BOOLEAN NOT NULL DEFAULT true,
  -- Nvidia driver (optional, from IsospinGPU)
  nvidia_module_hash BYTEA CHECK (nvidia_module_hash IS NULL OR length(nvidia_module_hash) = 32),
  nvidia_in_tree  BOOLEAN,
  kvm_enabled     BOOLEAN NOT NULL DEFAULT true,
  -- Status
  status          config_status NOT NULL DEFAULT 'draft',
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Nvidia consistency
  CONSTRAINT nvidia_consistency CHECK (
    (nvidia_module_hash IS NULL AND nvidia_in_tree IS NULL) OR
    (nvidia_module_hash IS NOT NULL AND nvidia_in_tree IS NOT NULL)
  ),
  -- GPU requires KVM
  CONSTRAINT gpu_requires_kvm CHECK (
    NOT gpu_passthrough OR kvm_enabled
  )
);

--------------------------------------------------------------------------------
-- BUILD FILE CONFIGURATION
--------------------------------------------------------------------------------

-- Dhall BUILD file tracking (SourceManifest from section 8)
CREATE TABLE build_files (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  -- File identity
  file_hash       BYTEA NOT NULL CHECK (length(file_hash) = 32),
  file_path       TEXT NOT NULL,
  -- Explicit file list (no globs - from SourceManifest.explicit)
  source_files    TEXT[] NOT NULL,
  -- Parsed configuration
  parsed_config   JSONB NOT NULL DEFAULT '{}',
  -- Validation
  is_valid        BOOLEAN NOT NULL DEFAULT true,
  validation_errors TEXT[],
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique file hash
  CONSTRAINT unique_build_file_hash UNIQUE (file_hash)
);

--------------------------------------------------------------------------------
-- CONTINUITY CONFIGURATION
--------------------------------------------------------------------------------

-- Main Continuity configuration (ContinuityConfig structure)
CREATE TABLE continuity_configs (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name            VARCHAR(255) NOT NULL UNIQUE,
  description     TEXT,
  -- References to sub-configurations
  toolchain_id    UUID NOT NULL REFERENCES toolchains(id),
  store_id        UUID NOT NULL REFERENCES stores(id),
  namespace_id    UUID NOT NULL REFERENCES namespace_configs(id),
  microvm_id      UUID REFERENCES microvm_configs(id),  -- Optional VM isolation
  -- DICE graph reference
  default_graph_id UUID REFERENCES dice_graphs(id),
  -- Build file references
  build_file_ids  UUID[] NOT NULL DEFAULT '{}',
  -- Validation state (ContinuityConfig.valid from continuity.lean)
  is_valid        BOOLEAN NOT NULL DEFAULT false,
  validation_errors TEXT[],
  -- Status
  status          config_status NOT NULL DEFAULT 'draft',
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

-- Configuration history (for audit trail)
CREATE TABLE config_history (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  config_id       UUID NOT NULL REFERENCES continuity_configs(id) ON DELETE CASCADE,
  version         INTEGER NOT NULL,
  -- Snapshot of configuration
  config_snapshot JSONB NOT NULL,
  -- Change metadata
  changed_by      VARCHAR(255),
  change_reason   TEXT,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique version per config
  CONSTRAINT unique_config_version UNIQUE (config_id, version)
);

--------------------------------------------------------------------------------
-- STOCHASTIC OMEGA CONFIGURATION
--------------------------------------------------------------------------------

-- stochastic_omega configuration (from section 13)
CREATE TABLE stochastic_omega_configs (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name            VARCHAR(255) NOT NULL UNIQUE,
  description     TEXT,
  -- Search parameters
  max_iterations  INTEGER NOT NULL CHECK (max_iterations > 0),
  temperature     DECIMAL(5,4) NOT NULL CHECK (temperature > 0 AND temperature <= 2),
  -- Oracle settings
  oracle_model    VARCHAR(255) NOT NULL,
  oracle_endpoint TEXT,
  -- Constraints (rfl-based soundness)
  require_rfl     BOOLEAN NOT NULL DEFAULT true,
  timeout_seconds INTEGER CHECK (timeout_seconds IS NULL OR timeout_seconds > 0),
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

--------------------------------------------------------------------------------
-- INDEXES
--------------------------------------------------------------------------------

-- Namespace indexes
CREATE INDEX idx_namespace_configs_name ON namespace_configs(name);

-- MicroVM indexes
CREATE INDEX idx_microvm_configs_name ON microvm_configs(name);
CREATE INDEX idx_microvm_configs_status ON microvm_configs(status);
CREATE INDEX idx_microvm_configs_kernel ON microvm_configs(kernel_hash);

-- Build file indexes
CREATE INDEX idx_build_files_hash ON build_files(file_hash);
CREATE INDEX idx_build_files_path ON build_files(file_path);
CREATE INDEX idx_build_files_valid ON build_files(is_valid);

-- Config indexes
CREATE INDEX idx_continuity_configs_name ON continuity_configs(name);
CREATE INDEX idx_continuity_configs_status ON continuity_configs(status);
CREATE INDEX idx_continuity_configs_toolchain ON continuity_configs(toolchain_id);
CREATE INDEX idx_continuity_configs_store ON continuity_configs(store_id);
CREATE INDEX idx_continuity_configs_valid ON continuity_configs(is_valid);

-- History indexes
CREATE INDEX idx_config_history_config ON config_history(config_id);
CREATE INDEX idx_config_history_version ON config_history(config_id, version DESC);

--------------------------------------------------------------------------------
-- TRIGGERS
--------------------------------------------------------------------------------

CREATE TRIGGER namespace_configs_updated_at
  BEFORE UPDATE ON namespace_configs
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER microvm_configs_updated_at
  BEFORE UPDATE ON microvm_configs
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER build_files_updated_at
  BEFORE UPDATE ON build_files
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER continuity_configs_updated_at
  BEFORE UPDATE ON continuity_configs
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER stochastic_omega_configs_updated_at
  BEFORE UPDATE ON stochastic_omega_configs
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

-- Auto-increment config version on update
CREATE OR REPLACE FUNCTION record_config_history()
RETURNS TRIGGER AS $$
DECLARE
  v_next_version INTEGER;
BEGIN
  SELECT COALESCE(MAX(version), 0) + 1 INTO v_next_version
  FROM config_history WHERE config_id = NEW.id;

  INSERT INTO config_history (config_id, version, config_snapshot)
  VALUES (NEW.id, v_next_version, row_to_json(NEW)::JSONB);

  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

CREATE TRIGGER continuity_configs_history
  AFTER UPDATE ON continuity_configs
  FOR EACH ROW
  EXECUTE FUNCTION record_config_history();

--------------------------------------------------------------------------------
-- VIEWS
--------------------------------------------------------------------------------

-- Full namespace details
CREATE VIEW namespace_details AS
SELECT
  id,
  name,
  ns_user,
  ns_mount,
  ns_net,
  ns_pid,
  ns_ipc,
  ns_uts,
  ns_cgroup,
  -- Check if full isolation
  (ns_user AND ns_mount AND ns_net AND ns_pid AND ns_ipc AND ns_uts AND ns_cgroup) AS is_full_isolation,
  created_at
FROM namespace_configs;

-- MicroVM with kernel/rootfs info
CREATE VIEW microvm_details AS
SELECT
  m.id,
  m.name,
  m.kernel_name,
  m.rootfs_name,
  m.vcpus,
  m.mem_mb,
  m.net_enabled,
  m.gpu_passthrough,
  m.kernel_minimal,
  m.drivers_verified,
  m.status,
  -- isospin compliance
  (m.kernel_minimal AND m.drivers_verified) AS is_isospin,
  m.created_at
FROM microvm_configs m;

-- Full config view
CREATE VIEW continuity_config_details AS
SELECT
  c.id,
  c.name,
  c.description,
  t.name AS toolchain_name,
  s.name AS store_name,
  n.name AS namespace_name,
  m.name AS microvm_name,
  c.is_valid,
  c.status,
  c.created_at,
  c.updated_at
FROM continuity_configs c
JOIN toolchains t ON c.toolchain_id = t.id
JOIN stores s ON c.store_id = s.id
JOIN namespace_configs n ON c.namespace_id = n.id
LEFT JOIN microvm_configs m ON c.microvm_id = m.id;

--------------------------------------------------------------------------------
-- FUNCTIONS
--------------------------------------------------------------------------------

-- Validate a Continuity configuration (ContinuityConfig.valid)
CREATE OR REPLACE FUNCTION validate_continuity_config(p_config_id UUID)
RETURNS TABLE(is_valid BOOLEAN, errors TEXT[]) AS $$
DECLARE
  v_config continuity_configs%ROWTYPE;
  v_errors TEXT[] := '{}';
  v_namespace namespace_configs%ROWTYPE;
  v_toolchain_closure BYTEA[];
  v_missing_paths BYTEA[];
BEGIN
  SELECT * INTO v_config FROM continuity_configs WHERE id = p_config_id;

  IF v_config IS NULL THEN
    RETURN QUERY SELECT FALSE, ARRAY['Config not found'];
    RETURN;
  END IF;

  -- Check 1: Namespace is full isolation
  SELECT * INTO v_namespace FROM namespace_configs WHERE id = v_config.namespace_id;
  IF NOT (v_namespace.ns_user AND v_namespace.ns_mount AND v_namespace.ns_net AND
          v_namespace.ns_pid AND v_namespace.ns_ipc AND v_namespace.ns_uts AND
          v_namespace.ns_cgroup) THEN
    v_errors := array_append(v_errors, 'Namespace is not full isolation');
  END IF;

  -- Check 2: All toolchain paths are in store
  -- (Simplified - would need full implementation)
  SELECT ARRAY[t.compiler_hash, t.sysroot_hash]
  INTO v_toolchain_closure
  FROM toolchains t WHERE t.id = v_config.toolchain_id;

  SELECT ARRAY_AGG(h)
  INTO v_missing_paths
  FROM unnest(v_toolchain_closure) AS h
  WHERE h IS NOT NULL AND NOT store_contains(h);

  IF array_length(v_missing_paths, 1) > 0 THEN
    v_errors := array_append(v_errors, 'Missing toolchain paths in store');
  END IF;

  -- Update config validation state
  UPDATE continuity_configs
  SET is_valid = (array_length(v_errors, 1) IS NULL OR array_length(v_errors, 1) = 0),
      validation_errors = v_errors
  WHERE id = p_config_id;

  RETURN QUERY
  SELECT
    (array_length(v_errors, 1) IS NULL OR array_length(v_errors, 1) = 0),
    v_errors;
END;
$$ LANGUAGE plpgsql;

-- Check if namespace provides hermetic isolation
CREATE OR REPLACE FUNCTION is_namespace_hermetic(p_namespace_id UUID)
RETURNS BOOLEAN AS $$
DECLARE
  v_ns namespace_configs%ROWTYPE;
BEGIN
  SELECT * INTO v_ns FROM namespace_configs WHERE id = p_namespace_id;

  -- Full isolation = hermetic (from hermetic_build theorem)
  RETURN v_ns.ns_user AND v_ns.ns_mount AND v_ns.ns_net AND
         v_ns.ns_pid AND v_ns.ns_ipc AND v_ns.ns_uts AND v_ns.ns_cgroup;
END;
$$ LANGUAGE plpgsql STABLE;

-- Check if config can build offline (from offline_build_possible theorem)
CREATE OR REPLACE FUNCTION can_build_offline(p_config_id UUID)
RETURNS BOOLEAN AS $$
DECLARE
  v_config continuity_configs%ROWTYPE;
  v_toolchain_closure BYTEA[];
  v_all_present BOOLEAN;
BEGIN
  SELECT * INTO v_config FROM continuity_configs WHERE id = p_config_id;

  -- Get toolchain closure
  SELECT ARRAY[t.compiler_hash, t.sysroot_hash]
  INTO v_toolchain_closure
  FROM toolchains t WHERE t.id = v_config.toolchain_id;

  -- Check all paths present in store
  SELECT NOT EXISTS (
    SELECT 1 FROM unnest(v_toolchain_closure) AS h
    WHERE h IS NOT NULL AND NOT store_contains(h)
  ) INTO v_all_present;

  RETURN v_all_present;
END;
$$ LANGUAGE plpgsql STABLE;

-- Get latest config version
CREATE OR REPLACE FUNCTION get_config_version(p_config_id UUID)
RETURNS INTEGER AS $$
BEGIN
  RETURN (
    SELECT COALESCE(MAX(version), 0)
    FROM config_history
    WHERE config_id = p_config_id
  );
END;
$$ LANGUAGE plpgsql STABLE;

--------------------------------------------------------------------------------
-- COMMENTS
--------------------------------------------------------------------------------

COMMENT ON TABLE namespace_configs IS
  'Linux namespace configurations from continuity.lean Namespace structure';
COMMENT ON TABLE microvm_configs IS
  'MicroVM/Isospin configurations from continuity.lean MicroVM/Isospin structures';
COMMENT ON TABLE build_files IS
  'Dhall BUILD file tracking with explicit file lists (no globs)';
COMMENT ON TABLE continuity_configs IS
  'Main Continuity configuration from continuity.lean ContinuityConfig structure';
COMMENT ON TABLE config_history IS
  'Configuration change audit trail';
COMMENT ON TABLE stochastic_omega_configs IS
  'stochastic_omega LLM proof search configuration';

COMMENT ON COLUMN namespace_configs.ns_user IS
  'Enable CLONE_NEWUSER (user namespace isolation)';
COMMENT ON COLUMN microvm_configs.kernel_minimal IS
  'Kernel is minimal and proven (Isospin property)';
COMMENT ON COLUMN microvm_configs.drivers_verified IS
  'Driver stack is verified (Isospin property)';
COMMENT ON COLUMN continuity_configs.is_valid IS
  'Configuration passes ContinuityConfig.valid predicate';
COMMENT ON COLUMN stochastic_omega_configs.require_rfl IS
  'Require rfl-based soundness (stochastic_omega_sound axiom)';
