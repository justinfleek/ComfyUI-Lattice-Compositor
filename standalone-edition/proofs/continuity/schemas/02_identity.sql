-- 02_identity.sql
-- Continuity Build System - Database Schema
--
-- IDENTITY AND ATTESTATION TABLES
--
-- Based on continuity.lean section 5 (Identity) and section 6 (Attestation):
-- - Ed25519 public keys (32 bytes)
-- - Ed25519 signatures (64 bytes)
-- - Attestations: signed claims about artifacts
--
-- Designed for PostgreSQL 15+

--------------------------------------------------------------------------------
-- ENUMS
--------------------------------------------------------------------------------

-- Key status for lifecycle management
CREATE TYPE key_status AS ENUM (
  'active',
  'revoked',
  'expired',
  'pending'
);

-- Attestation type
CREATE TYPE attestation_type AS ENUM (
  'build',       -- Build output attestation
  'source',      -- Source code attestation
  'review',      -- Code review attestation
  'deployment',  -- Deployment attestation
  'audit'        -- Security audit attestation
);

--------------------------------------------------------------------------------
-- IDENTITY TABLES
--------------------------------------------------------------------------------

-- Ed25519 public keys (PublicKey structure)
CREATE TABLE public_keys (
  key_id          UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  bytes           BYTEA NOT NULL CHECK (length(bytes) = 32),
  name            VARCHAR(255),
  description     TEXT,
  owner           VARCHAR(255),
  status          key_status NOT NULL DEFAULT 'active',
  -- Key fingerprint for quick lookup (SHA-256 of public key bytes)
  fingerprint     BYTEA NOT NULL CHECK (length(fingerprint) = 32),
  valid_from      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  valid_until     TIMESTAMPTZ,
  revoked_at      TIMESTAMPTZ,
  revocation_reason TEXT,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique public key bytes
  CONSTRAINT unique_pubkey_bytes UNIQUE (bytes),
  -- Unique fingerprint
  CONSTRAINT unique_fingerprint UNIQUE (fingerprint),
  -- Revocation requires revoked status
  CONSTRAINT revocation_consistency CHECK (
    (status != 'revoked' AND revoked_at IS NULL) OR
    (status = 'revoked' AND revoked_at IS NOT NULL)
  )
);

-- Key trust relationships (web of trust)
CREATE TABLE key_trust (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  truster_key_id  UUID NOT NULL REFERENCES public_keys(key_id) ON DELETE CASCADE,
  trustee_key_id  UUID NOT NULL REFERENCES public_keys(key_id) ON DELETE CASCADE,
  trust_level     SMALLINT NOT NULL CHECK (trust_level >= 0 AND trust_level <= 100),
  signature       BYTEA NOT NULL CHECK (length(signature) = 64),
  valid_from      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  valid_until     TIMESTAMPTZ,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- No self-trust
  CONSTRAINT no_self_trust CHECK (truster_key_id != trustee_key_id),
  -- Unique trust relationship
  CONSTRAINT unique_trust UNIQUE (truster_key_id, trustee_key_id)
);

--------------------------------------------------------------------------------
-- ATTESTATION TABLES
--------------------------------------------------------------------------------

-- Attestations: signed claims about artifacts (Attestation structure)
CREATE TABLE attestations (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  artifact_hash   BYTEA NOT NULL CHECK (length(artifact_hash) = 32),
  builder_key_id  UUID NOT NULL REFERENCES public_keys(key_id),
  attestation_type attestation_type NOT NULL DEFAULT 'build',
  timestamp       BIGINT NOT NULL,  -- Unix timestamp (Nat in Lean)
  signature       BYTEA NOT NULL CHECK (length(signature) = 64),
  -- Additional attestation metadata
  metadata        JSONB NOT NULL DEFAULT '{}',
  -- Optional reference to derivation that produced the artifact
  derivation_id   UUID,
  -- Verification status (cached)
  verified        BOOLEAN,
  verified_at     TIMESTAMPTZ,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique attestation per artifact/builder/type combination
  CONSTRAINT unique_attestation UNIQUE (artifact_hash, builder_key_id, attestation_type, timestamp)
);

-- Attestation chains (for multi-party attestations)
CREATE TABLE attestation_chains (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  name            VARCHAR(255) NOT NULL,
  description     TEXT,
  -- Minimum number of attestations required
  required_count  INTEGER NOT NULL DEFAULT 1 CHECK (required_count > 0),
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

-- Chain membership
CREATE TABLE attestation_chain_members (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  chain_id        UUID NOT NULL REFERENCES attestation_chains(id) ON DELETE CASCADE,
  attestation_id  UUID NOT NULL REFERENCES attestations(id) ON DELETE CASCADE,
  position        INTEGER NOT NULL DEFAULT 0,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique position in chain
  CONSTRAINT unique_chain_position UNIQUE (chain_id, position),
  -- Unique attestation per chain
  CONSTRAINT unique_chain_attestation UNIQUE (chain_id, attestation_id)
);

-- Builder identity records (for build reproducibility)
CREATE TABLE builders (
  id              UUID PRIMARY KEY DEFAULT uuid_generate_v4(),
  key_id          UUID NOT NULL REFERENCES public_keys(key_id),
  name            VARCHAR(255) NOT NULL,
  description     TEXT,
  -- Builder capabilities
  supported_archs arch[] NOT NULL DEFAULT '{}',
  supported_os    os[] NOT NULL DEFAULT '{}',
  -- Trust level (0-100)
  trust_level     SMALLINT NOT NULL DEFAULT 50 CHECK (trust_level >= 0 AND trust_level <= 100),
  active          BOOLEAN NOT NULL DEFAULT true,
  created_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),
  updated_at      TIMESTAMPTZ NOT NULL DEFAULT NOW(),

  -- Unique builder per key
  CONSTRAINT unique_builder_key UNIQUE (key_id)
);

--------------------------------------------------------------------------------
-- INDEXES
--------------------------------------------------------------------------------

-- Public key indexes
CREATE INDEX idx_pubkeys_fingerprint ON public_keys(fingerprint);
CREATE INDEX idx_pubkeys_status ON public_keys(status);
CREATE INDEX idx_pubkeys_owner ON public_keys(owner);
CREATE INDEX idx_pubkeys_active ON public_keys(status) WHERE status = 'active';

-- Key trust indexes
CREATE INDEX idx_trust_truster ON key_trust(truster_key_id);
CREATE INDEX idx_trust_trustee ON key_trust(trustee_key_id);
CREATE INDEX idx_trust_level ON key_trust(trust_level DESC);

-- Attestation indexes
CREATE INDEX idx_attestations_artifact ON attestations(artifact_hash);
CREATE INDEX idx_attestations_builder ON attestations(builder_key_id);
CREATE INDEX idx_attestations_type ON attestations(attestation_type);
CREATE INDEX idx_attestations_timestamp ON attestations(timestamp DESC);
CREATE INDEX idx_attestations_verified ON attestations(verified) WHERE verified = true;
CREATE INDEX idx_attestations_derivation ON attestations(derivation_id) WHERE derivation_id IS NOT NULL;

-- Builder indexes
CREATE INDEX idx_builders_key ON builders(key_id);
CREATE INDEX idx_builders_active ON builders(active) WHERE active = true;
CREATE INDEX idx_builders_trust ON builders(trust_level DESC);

--------------------------------------------------------------------------------
-- TRIGGERS
--------------------------------------------------------------------------------

CREATE TRIGGER public_keys_updated_at
  BEFORE UPDATE ON public_keys
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER attestations_updated_at
  BEFORE UPDATE ON attestations
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER attestation_chains_updated_at
  BEFORE UPDATE ON attestation_chains
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

CREATE TRIGGER builders_updated_at
  BEFORE UPDATE ON builders
  FOR EACH ROW
  EXECUTE FUNCTION continuity_update_timestamp();

--------------------------------------------------------------------------------
-- VIEWS
--------------------------------------------------------------------------------

-- Active keys with owner info
CREATE VIEW active_keys AS
SELECT
  key_id,
  bytes,
  name,
  owner,
  fingerprint,
  valid_from,
  valid_until,
  created_at
FROM public_keys
WHERE status = 'active'
  AND (valid_until IS NULL OR valid_until > NOW());

-- Attestations with builder info
CREATE VIEW attestation_details AS
SELECT
  a.id,
  a.artifact_hash,
  a.attestation_type,
  a.timestamp,
  a.signature,
  a.verified,
  a.verified_at,
  pk.name AS builder_name,
  pk.owner AS builder_owner,
  pk.fingerprint AS builder_fingerprint,
  b.trust_level AS builder_trust,
  a.created_at
FROM attestations a
JOIN public_keys pk ON a.builder_key_id = pk.key_id
LEFT JOIN builders b ON pk.key_id = b.key_id;

-- Trust network summary
CREATE VIEW trust_network AS
SELECT
  t.truster_key_id,
  pk1.name AS truster_name,
  t.trustee_key_id,
  pk2.name AS trustee_name,
  t.trust_level,
  t.valid_from,
  t.valid_until
FROM key_trust t
JOIN public_keys pk1 ON t.truster_key_id = pk1.key_id
JOIN public_keys pk2 ON t.trustee_key_id = pk2.key_id
WHERE pk1.status = 'active' AND pk2.status = 'active';

--------------------------------------------------------------------------------
-- FUNCTIONS
--------------------------------------------------------------------------------

-- Get attestations for an artifact
CREATE OR REPLACE FUNCTION get_artifact_attestations(p_artifact_hash BYTEA)
RETURNS SETOF attestation_details AS $$
BEGIN
  RETURN QUERY
  SELECT * FROM attestation_details
  WHERE artifact_hash = p_artifact_hash
  ORDER BY timestamp DESC;
END;
$$ LANGUAGE plpgsql STABLE;

-- Check if artifact has sufficient attestations
CREATE OR REPLACE FUNCTION artifact_has_attestations(
  p_artifact_hash BYTEA,
  p_min_count INTEGER DEFAULT 1,
  p_min_trust INTEGER DEFAULT 50
)
RETURNS BOOLEAN AS $$
DECLARE
  v_count INTEGER;
BEGIN
  SELECT COUNT(*) INTO v_count
  FROM attestations a
  JOIN builders b ON a.builder_key_id = b.key_id
  WHERE a.artifact_hash = p_artifact_hash
    AND a.verified = true
    AND b.trust_level >= p_min_trust;

  RETURN v_count >= p_min_count;
END;
$$ LANGUAGE plpgsql STABLE;

-- Revoke a key
CREATE OR REPLACE FUNCTION revoke_key(
  p_key_id UUID,
  p_reason TEXT DEFAULT NULL
)
RETURNS VOID AS $$
BEGIN
  UPDATE public_keys
  SET
    status = 'revoked',
    revoked_at = NOW(),
    revocation_reason = p_reason
  WHERE key_id = p_key_id;
END;
$$ LANGUAGE plpgsql;

-- Calculate transitive trust level
CREATE OR REPLACE FUNCTION calculate_trust_path(
  p_from_key_id UUID,
  p_to_key_id UUID,
  p_max_depth INTEGER DEFAULT 5
)
RETURNS INTEGER AS $$
DECLARE
  v_trust INTEGER;
BEGIN
  -- Simple BFS for trust path (returns minimum trust along path)
  WITH RECURSIVE trust_path AS (
    -- Base case: direct trust
    SELECT
      trustee_key_id,
      trust_level,
      1 AS depth,
      ARRAY[truster_key_id, trustee_key_id] AS path
    FROM key_trust
    WHERE truster_key_id = p_from_key_id

    UNION ALL

    -- Recursive case
    SELECT
      kt.trustee_key_id,
      LEAST(tp.trust_level, kt.trust_level),
      tp.depth + 1,
      tp.path || kt.trustee_key_id
    FROM trust_path tp
    JOIN key_trust kt ON tp.trustee_key_id = kt.truster_key_id
    WHERE tp.depth < p_max_depth
      AND NOT kt.trustee_key_id = ANY(tp.path)
  )
  SELECT MAX(trust_level) INTO v_trust
  FROM trust_path
  WHERE trustee_key_id = p_to_key_id;

  RETURN COALESCE(v_trust, 0);
END;
$$ LANGUAGE plpgsql STABLE;

--------------------------------------------------------------------------------
-- COMMENTS
--------------------------------------------------------------------------------

COMMENT ON TABLE public_keys IS
  'Ed25519 public keys (32 bytes) from continuity.lean PublicKey structure';
COMMENT ON TABLE key_trust IS
  'Web of trust relationships between keys';
COMMENT ON TABLE attestations IS
  'Signed claims about artifacts from continuity.lean Attestation structure';
COMMENT ON TABLE attestation_chains IS
  'Multi-party attestation requirements';
COMMENT ON TABLE builders IS
  'Builder identity records with capabilities and trust levels';

COMMENT ON COLUMN public_keys.bytes IS
  'Ed25519 public key bytes (exactly 32 bytes)';
COMMENT ON COLUMN public_keys.fingerprint IS
  'SHA-256 hash of public key for quick lookup';
COMMENT ON COLUMN attestations.artifact_hash IS
  'SHA-256 hash of attested artifact (32 bytes)';
COMMENT ON COLUMN attestations.signature IS
  'Ed25519 signature (exactly 64 bytes)';
COMMENT ON COLUMN attestations.timestamp IS
  'Unix timestamp (Nat in Lean) of attestation';
