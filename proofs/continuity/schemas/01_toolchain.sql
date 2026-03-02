-- 01_toolchain.sql
-- Continuity Build System - Database Schema
--
-- TOOLCHAIN TABLES
--
-- Based on continuity.lean section 3 (Toolchains):
-- - Typed compiler flags (no strings)
-- - Target triples (arch/os/abi)
-- - Coset equivalence classes
--
-- Designed for PostgreSQL 15+

--------------------------------------------------------------------------------
-- ENUMS (from continuity.lean)
--------------------------------------------------------------------------------

-- CPU architecture (Arch inductive type)
CREATE TYPE arch AS ENUM (
  'x86_64',
  'aarch64',
  'wasm32',
  'riscv64'
);

-- Operating system (OS inductive type)
CREATE TYPE os AS ENUM (
  'linux',
  'darwin',
  'wasi',
  'none'
);

-- Optimization level (OptLevel inductive type)
CREATE TYPE opt_level AS ENUM (
  'O0',
  'O1',
  'O2',
  'O3',
  'Oz',
  'Os'
);

-- Link-time optimization mode (LTOMode inductive type)
CREATE TYPE lto_mode AS ENUM (
  'off',
  'thin',
  'fat'
);

-- Typed flag discriminator (Flag inductive type)
CREATE TYPE flag_type AS ENUM (
  'opt_level',
  'lto',
  'target_cpu',
  'debug',
  'pic'
);

-- Source language (Lang inductive type from section 12)
CREATE TYPE lang AS ENUM (
  'purescript',
  'haskell',
  'rust',
  'lean'
);

-- Compilation target (Target inductive type from section 12)
CREATE TYPE compilation_target AS ENUM (
  'js',
  'native',
  'wasm',
  'c'
);

--------------------------------------------------------------------------------
-- TOOLCHAIN TABLES
--------------------------------------------------------------------------------

-- Target triple (Triple structure)
CREATE TABLE triples (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  arch            arch NOT NULL,
  os              os NOT NULL,
  abi             VARCHAR(50) NOT NULL,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique triple combination
  CONSTRAINT unique_triple UNIQUE (arch, os, abi)
);

-- Toolchain: compiler + host + target + flags (Toolchain structure)
CREATE TABLE toolchains (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name            VARCHAR(255) NOT NULL,
  compiler_hash   BYTEA NOT NULL CHECK (length(compiler_hash) = 32),
  compiler_name   VARCHAR(255) NOT NULL,
  host_triple_id  UUID NOT NULL REFERENCES triples(id),
  target_triple_id UUID NOT NULL REFERENCES triples(id),
  sysroot_hash    BYTEA CHECK (sysroot_hash IS NULL OR length(sysroot_hash) = 32),
  sysroot_name    VARCHAR(255),
  coset_id        UUID,  -- Links to cosets table for equivalence
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Sysroot name required if hash present
  CONSTRAINT sysroot_consistency CHECK (
    (sysroot_hash IS NULL AND sysroot_name IS NULL) OR
    (sysroot_hash IS NOT NULL AND sysroot_name IS NOT NULL)
  )
);

-- Typed compiler flags (Flag inductive type)
CREATE TABLE toolchain_flags (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  toolchain_id    UUID NOT NULL REFERENCES toolchains(id) ON DELETE CASCADE,
  flag_type       flag_type NOT NULL,
  -- Polymorphic value storage based on flag_type:
  -- opt_level: stored in opt_level_value
  -- lto: stored in lto_value
  -- target_cpu: stored in string_value
  -- debug: stored in bool_value
  -- pic: stored in bool_value
  opt_level_value opt_level,
  lto_value       lto_mode,
  string_value    VARCHAR(255),
  bool_value      BOOLEAN,
  flag_order      INTEGER NOT NULL DEFAULT 0,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Ensure correct value column is populated for flag type
  CONSTRAINT flag_value_consistency CHECK (
    (flag_type = 'opt_level' AND opt_level_value IS NOT NULL AND lto_value IS NULL AND string_value IS NULL AND bool_value IS NULL) OR
    (flag_type = 'lto' AND lto_value IS NOT NULL AND opt_level_value IS NULL AND string_value IS NULL AND bool_value IS NULL) OR
    (flag_type = 'target_cpu' AND string_value IS NOT NULL AND opt_level_value IS NULL AND lto_value IS NULL AND bool_value IS NULL) OR
    (flag_type = 'debug' AND bool_value IS NOT NULL AND opt_level_value IS NULL AND lto_value IS NULL AND string_value IS NULL) OR
    (flag_type = 'pic' AND bool_value IS NOT NULL AND opt_level_value IS NULL AND lto_value IS NULL AND string_value IS NULL)
  )
);

-- Build equivalence cosets (section 5: The Coset)
-- Same coset = same outputs for all sources
CREATE TABLE cosets (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name            VARCHAR(255),
  description     TEXT,
  -- Representative hash: content hash of normalized toolchain config
  representative_hash BYTEA NOT NULL CHECK (length(representative_hash) = 32),
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Each coset has unique representative
  CONSTRAINT unique_coset_hash UNIQUE (representative_hash)
);

-- Add foreign key from toolchains to cosets
ALTER TABLE toolchains
  ADD CONSTRAINT fk_toolchains_coset
  FOREIGN KEY (coset_id) REFERENCES cosets(id);

-- Language equivalence mappings (section 12: Language Coset)
CREATE TABLE language_equivalences (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  source_lang     lang NOT NULL,
  target_lang     lang NOT NULL,
  compilation_target compilation_target NOT NULL,
  semantics_preserved BOOLEAN NOT NULL DEFAULT true,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique language pair per target
  CONSTRAINT unique_lang_equiv UNIQUE (source_lang, target_lang, compilation_target)
);

--------------------------------------------------------------------------------
-- INDEXES
--------------------------------------------------------------------------------

-- Triple indexes
CREATE INDEX idx_triples_arch ON triples(arch);
CREATE INDEX idx_triples_os ON triples(os);

-- Toolchain indexes
CREATE INDEX idx_toolchains_compiler_hash ON toolchains(compiler_hash);
CREATE INDEX idx_toolchains_host ON toolchains(host_triple_id);
CREATE INDEX idx_toolchains_target ON toolchains(target_triple_id);
CREATE INDEX idx_toolchains_coset ON toolchains(coset_id);
CREATE INDEX idx_toolchains_created ON toolchains(created_at DESC);

-- Flag indexes
CREATE INDEX idx_flags_toolchain ON toolchain_flags(toolchain_id);
CREATE INDEX idx_flags_type ON toolchain_flags(flag_type);
CREATE INDEX idx_flags_order ON toolchain_flags(toolchain_id, flag_order);

-- Coset indexes
CREATE INDEX idx_cosets_hash ON cosets(representative_hash);

--------------------------------------------------------------------------------
-- TRIGGERS
--------------------------------------------------------------------------------

CREATE TRIGGER triples_updated_at
  BEFORE UPDATE ON triples
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER toolchains_updated_at
  BEFORE UPDATE ON toolchains
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER cosets_updated_at
  BEFORE UPDATE ON cosets
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

--------------------------------------------------------------------------------
-- VIEWS
--------------------------------------------------------------------------------

-- Full toolchain view with triples
CREATE VIEW toolchain_details AS
SELECT
  t.id,
  t.name,
  t.compiler_hash,
  t.compiler_name,
  h.arch AS host_arch,
  h.os AS host_os,
  h.abi AS host_abi,
  tg.arch AS target_arch,
  tg.os AS target_os,
  tg.abi AS target_abi,
  t.sysroot_hash,
  t.sysroot_name,
  c.name AS coset_name,
  c.representative_hash AS coset_hash,
  t.created_at,
  t.updated_at
FROM toolchains t
JOIN triples h ON t.host_triple_id = h.id
JOIN triples tg ON t.target_triple_id = tg.id
LEFT JOIN cosets c ON t.coset_id = c.id;

-- Flags for a toolchain (ordered)
CREATE VIEW toolchain_flags_ordered AS
SELECT
  tf.toolchain_id,
  tf.flag_type,
  tf.opt_level_value,
  tf.lto_value,
  tf.string_value,
  tf.bool_value,
  tf.flag_order
FROM toolchain_flags tf
ORDER BY tf.toolchain_id, tf.flag_order;

--------------------------------------------------------------------------------
-- FUNCTIONS
--------------------------------------------------------------------------------

-- Get all toolchains in a coset (build-equivalent toolchains)
CREATE OR REPLACE FUNCTION get_coset_members(p_coset_id UUID)
RETURNS SETOF toolchains AS $$
BEGIN
  RETURN QUERY
  SELECT * FROM toolchains WHERE coset_id = p_coset_id;
END;
$$ LANGUAGE plpgsql STABLE;

-- Check if two toolchains are build-equivalent (same coset)
CREATE OR REPLACE FUNCTION are_build_equivalent(
  p_toolchain1_id UUID,
  p_toolchain2_id UUID
)
RETURNS BOOLEAN AS $$
DECLARE
  v_coset1 UUID;
  v_coset2 UUID;
BEGIN
  SELECT coset_id INTO v_coset1 FROM toolchains WHERE id = p_toolchain1_id;
  SELECT coset_id INTO v_coset2 FROM toolchains WHERE id = p_toolchain2_id;

  IF v_coset1 IS NULL OR v_coset2 IS NULL THEN
    RETURN FALSE;
  END IF;

  RETURN v_coset1 = v_coset2;
END;
$$ LANGUAGE plpgsql STABLE;

--------------------------------------------------------------------------------
-- COMMENTS
--------------------------------------------------------------------------------

COMMENT ON TABLE triples IS
  'Target triples: arch + os + abi (from continuity.lean Triple structure)';
COMMENT ON TABLE toolchains IS
  'Toolchain definitions: compiler + host + target + flags (from continuity.lean Toolchain structure)';
COMMENT ON TABLE toolchain_flags IS
  'Typed compiler flags (from continuity.lean Flag inductive type)';
COMMENT ON TABLE cosets IS
  'Build equivalence classes: toolchains in same coset produce identical outputs';
COMMENT ON TABLE language_equivalences IS
  'Cross-language semantic equivalence mappings';

COMMENT ON COLUMN toolchains.compiler_hash IS
  'SHA-256 hash of compiler StorePath (32 bytes)';
COMMENT ON COLUMN toolchains.coset_id IS
  'Equivalence class: same coset = same build outputs';
COMMENT ON COLUMN cosets.representative_hash IS
  'Content hash of normalized toolchain configuration';
