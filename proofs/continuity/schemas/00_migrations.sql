-- 00_migrations.sql
-- Continuity Build System - Database Schema
--
-- MIGRATION TRACKING AND SCHEMA VERSIONING
--
-- Based on the formal specification in continuity.lean:
-- - Content-addressed derivations
-- - Typed toolchains with coset equivalence
-- - DICE action graphs
-- - R2+git attestation
--
-- Designed for PostgreSQL 15+
-- Schema version: 1.0.0

--------------------------------------------------------------------------------
-- EXTENSIONS
--------------------------------------------------------------------------------

CREATE EXTENSION IF NOT EXISTS "uuid-ossp";
CREATE EXTENSION IF NOT EXISTS "pgcrypto";  -- For cryptographic functions

--------------------------------------------------------------------------------
-- SCHEMA VERSION TRACKING
--------------------------------------------------------------------------------

CREATE TABLE continuity_schema_migrations (
  version         VARCHAR(50) PRIMARY KEY,
  description     TEXT NOT NULL,
  applied_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  applied_by      VARCHAR(255) NOT NULL DEFAULT 'system',
  execution_time  INTERVAL,
  checksum        BYTEA,  -- SHA-256 of migration script
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

-- Insert initial version
INSERT INTO continuity_schema_migrations (version, description, applied_by)
VALUES ('1.0.0', 'Initial Continuity schema creation', 'system');

--------------------------------------------------------------------------------
-- MIGRATION PROCEDURES
--------------------------------------------------------------------------------

-- Check if migration has been applied
CREATE OR REPLACE FUNCTION continuity_migration_applied(p_version VARCHAR)
RETURNS BOOLEAN AS $$
BEGIN
  RETURN EXISTS (
    SELECT 1 FROM continuity_schema_migrations WHERE version = p_version
  );
END;
$$ LANGUAGE plpgsql STABLE;

-- Record migration
CREATE OR REPLACE FUNCTION continuity_record_migration(
  p_version VARCHAR,
  p_description TEXT,
  p_applied_by VARCHAR DEFAULT 'system',
  p_checksum BYTEA DEFAULT NULL
)
RETURNS VOID AS $$
BEGIN
  INSERT INTO continuity_schema_migrations (version, description, applied_by, checksum)
  VALUES (p_version, p_description, p_applied_by, p_checksum);
END;
$$ LANGUAGE plpgsql;

-- Get current schema version
CREATE OR REPLACE FUNCTION continuity_current_version()
RETURNS VARCHAR AS $$
BEGIN
  RETURN (
    SELECT version
    FROM continuity_schema_migrations
    ORDER BY applied_at DESC
    LIMIT 1
  );
END;
$$ LANGUAGE plpgsql STABLE;

-- List all applied migrations
CREATE OR REPLACE FUNCTION continuity_list_migrations()
RETURNS TABLE(
  version VARCHAR,
  description TEXT,
  applied_at TIMESTAMPTZ,
  applied_by VARCHAR
) AS $$
BEGIN
  RETURN QUERY
  SELECT
    m.version,
    m.description,
    m.applied_at,
    m.applied_by
  FROM continuity_schema_migrations m
  ORDER BY m.applied_at ASC;
END;
$$ LANGUAGE plpgsql STABLE;

--------------------------------------------------------------------------------
-- MAINTENANCE PROCEDURES
--------------------------------------------------------------------------------

-- Update timestamp trigger function
CREATE OR REPLACE FUNCTION continuity_update_timestamp()
RETURNS TRIGGER AS $$
BEGIN
  NEW.updated_at = NOW();
  RETURN NEW;
END;
$$ LANGUAGE plpgsql;

-- Validate hash length (32 bytes for SHA-256)
CREATE OR REPLACE FUNCTION continuity_validate_hash(p_hash BYTEA)
RETURNS BOOLEAN AS $$
BEGIN
  RETURN p_hash IS NOT NULL AND length(p_hash) = 32;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- Validate signature length (64 bytes for Ed25519)
CREATE OR REPLACE FUNCTION continuity_validate_signature(p_sig BYTEA)
RETURNS BOOLEAN AS $$
BEGIN
  RETURN p_sig IS NOT NULL AND length(p_sig) = 64;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

-- Validate public key length (32 bytes for Ed25519)
CREATE OR REPLACE FUNCTION continuity_validate_pubkey(p_key BYTEA)
RETURNS BOOLEAN AS $$
BEGIN
  RETURN p_key IS NOT NULL AND length(p_key) = 32;
END;
$$ LANGUAGE plpgsql IMMUTABLE;

--------------------------------------------------------------------------------
-- HEALTH CHECK
--------------------------------------------------------------------------------

CREATE OR REPLACE FUNCTION continuity_health_check()
RETURNS TABLE(
  check_name TEXT,
  status TEXT,
  details TEXT
) AS $$
BEGIN
  -- Schema version
  RETURN QUERY
  SELECT
    'schema_version'::TEXT,
    'OK'::TEXT,
    'Current version: ' || continuity_current_version();

  -- Toolchain count
  RETURN QUERY
  SELECT
    'toolchains'::TEXT,
    CASE WHEN (SELECT COUNT(*) FROM toolchains) > 0 THEN 'OK' ELSE 'WARNING' END,
    'Total toolchains: ' || (SELECT COUNT(*) FROM toolchains);

  -- Store paths count
  RETURN QUERY
  SELECT
    'store_paths'::TEXT,
    CASE WHEN (SELECT COUNT(*) FROM store_paths) >= 0 THEN 'OK' ELSE 'ERROR' END,
    'Total store paths: ' || (SELECT COUNT(*) FROM store_paths);

  -- Attestation count
  RETURN QUERY
  SELECT
    'attestations'::TEXT,
    'OK'::TEXT,
    'Total attestations: ' || (SELECT COUNT(*) FROM attestations);

  -- DICE actions count
  RETURN QUERY
  SELECT
    'dice_actions'::TEXT,
    'OK'::TEXT,
    'Total actions: ' || (SELECT COUNT(*) FROM actions);

  -- Check for invalid hashes
  RETURN QUERY
  SELECT
    'invalid_store_hashes'::TEXT,
    CASE WHEN (SELECT COUNT(*) FROM store_paths WHERE NOT continuity_validate_hash(hash)) = 0
      THEN 'OK' ELSE 'ERROR' END,
    'Invalid hashes: ' || (SELECT COUNT(*) FROM store_paths WHERE NOT continuity_validate_hash(hash));
END;
$$ LANGUAGE plpgsql;

--------------------------------------------------------------------------------
-- COMMENTS
--------------------------------------------------------------------------------

COMMENT ON TABLE continuity_schema_migrations IS
  'Track applied database migrations for Continuity build system';
COMMENT ON FUNCTION continuity_migration_applied IS
  'Check if a migration version has been applied';
COMMENT ON FUNCTION continuity_current_version IS
  'Get the current schema version';
COMMENT ON FUNCTION continuity_validate_hash IS
  'Validate SHA-256 hash is exactly 32 bytes';
COMMENT ON FUNCTION continuity_validate_signature IS
  'Validate Ed25519 signature is exactly 64 bytes';
COMMENT ON FUNCTION continuity_validate_pubkey IS
  'Validate Ed25519 public key is exactly 32 bytes';
