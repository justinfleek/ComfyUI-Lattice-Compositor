# Protocol Migration Gap Analysis

**Date:** 2026-02-02  
**Status:** Gap Analysis - Current State vs Target State

## Executive Summary

Current codebase is TypeScript/Python. Target state requires:
1. **Literate Programming** - All code in `.lit` files with `@target`, `@name`, `@description` annotations
2. **NEWSPECS API** - Unified API implementation (straylight-unified-api.yaml)
3. **trtllm Integration** - TensorRT-LLM serving infrastructure
4. **Aleph Protocols** - Dhall build language, typed toolchains, content-addressed storage

## Current State

### Codebase Structure
- **Frontend:** TypeScript/Vue (`ui/src/`)
- **Backend:** Python (`src/lattice/`)
- **Build System:** Nix (partial), npm/pip
- **Documentation:** Markdown files

### Current Languages
- TypeScript (UI layer)
- Python (Backend services)
- Nix (Build configuration, partial)
- Lean4 (Proofs, minimal)

## Target State (NEWSPECS + Aleph + trtllm)

### 1. Literate Programming (STRAYLIGHT-011)

**Requirement:** All code in `.lit`, `.mdx`, `.lit.hs`, `.lit.cpp`, `.lit.purs` files

**Format:**
```cpp
@target: cpp23
@name: component-name
@description: Human-readable description
// Code here
```

**Chunk References:**
```cpp
<<other-chunk-name>>
```

**Current Gap:**
- ❌ 0% of codebase uses literate programming format
- ❌ All code in `.ts`, `.py`, `.hs` files (not `.lit.*`)
- ❌ No `@target`, `@name`, `@description` annotations
- ❌ No chunk references (`<<name>>`)

**Migration Required:**
- Convert all `.ts` → `.lit.ts` or `.lit.js` with annotations
- Convert all `.py` → `.lit.py` with annotations  
- Convert all `.hs` → `.lit.hs` with annotations
- Add chunk structure and references

### 2. NEWSPECS Unified API

**Requirement:** Implement `NEWSPECS/straylight-unified-api.yaml`

**Key Components:**
- MAESTRO orchestrator
- CMO Domain (content, campaigns, analytics)
- Compositor Domain (render, effects, animation)
- Vector Domain (intelligence, partnerships)
- Event sourcing
- Multi-agent workflows

**Current Gap:**
- ❌ No unified API implementation
- ❌ No MAESTRO orchestrator
- ❌ No event sourcing infrastructure
- ❌ No multi-agent workflow system
- ❌ Domain separation not implemented

**Migration Required:**
- Implement OpenAPI spec endpoints
- Build MAESTRO predictive orchestrator
- Implement event sourcing (Postgres-backed)
- Create agent registry system
- Implement domain separation

### 3. trtllm Integration

**Requirement:** TensorRT-LLM serving with speculative decoding

**Key Components:**
- `trtllm-serve` (OpenAI-compatible server)
- Engine building (`trtllm-engine.nix`)
- Model configuration (Qwen3, LLaMA, etc.)
- Speculative decoding (Eagle/Eagle3, MTP, NGram)

**Current Gap:**
- ❌ No trtllm integration
- ❌ No TensorRT-LLM serving infrastructure
- ❌ No model engine building pipeline
- ❌ No speculative decoding support

**Migration Required:**
- Integrate `NEWSPECS/trtllm-serve-main/` into build system
- Set up model serving infrastructure
- Implement engine building pipeline
- Add speculative decoding support

### 4. Aleph Protocols (aleph-008)

**Requirement:** Continuity project implementation

**Key Components:**

#### 4.1 Dhall Build Language
- Replace Nix/Starlark with Dhall
- System Fω, total, content-addressed imports
- Explicit file lists (no globs)
- Typed toolchains

**Current Gap:**
- ❌ Using Nix (not Dhall)
- ❌ Using globs in build files
- ❌ No typed toolchain system
- ❌ No BUILD.dhall files

**Migration Required:**
- Convert `flake.nix` → `BUILD.dhall`
- Replace globs with explicit file lists
- Implement typed toolchain system
- Use Dhall for all build configuration

#### 4.2 Content-Addressed Storage (R2)
- R2 bucket for CAS blobs
- Git for attestations
- ed25519 for signing

**Current Gap:**
- ❌ No R2 integration
- ❌ No content-addressed storage
- ❌ No attestation system
- ❌ No cryptographic signing

**Migration Required:**
- Set up R2 bucket infrastructure
- Implement CAS layer
- Add git attestation system
- Implement ed25519 signing

#### 4.3 Armitage Witness Proxy
- Replace nix daemon
- Witness proxy for fetches
- Coeffect checker (Lean4)
- Attestation system

**Current Gap:**
- ❌ Using nix daemon (not armitage)
- ❌ No witness proxy
- ❌ No coeffect checker
- ❌ No attestation system

**Migration Required:**
- Implement armitage witness proxy
- Build coeffect checker in Lean4
- Implement attestation workflow
- Replace nix daemon calls

#### 4.4 DICE Builds (Buck2)
- Replace Bazel with Buck2
- Dhall BUILD files
- Action graph execution
- WASM sandbox / isospin executor

**Current Gap:**
- ❌ Not using Buck2/DICE
- ❌ No action graph system
- ❌ No WASM sandbox executor
- ❌ No isospin integration

**Migration Required:**
- Set up Buck2/DICE build system
- Convert builds to DICE format
- Implement WASM sandbox executor
- Integrate isospin for builds

## Gap Summary

| Component | Current | Target | Gap % |
|-----------|---------|--------|-------|
| **Literate Programming** | 0% | 100% | 100% |
| **NEWSPECS API** | 0% | 100% | 100% |
| **trtllm Integration** | 0% | 100% | 100% |
| **Dhall Build Language** | 0% | 100% | 100% |
| **R2 CAS Storage** | 0% | 100% | 100% |
| **Armitage Proxy** | 0% | 100% | 100% |
| **DICE Builds** | 0% | 100% | 100% |
| **Typed Toolchains** | 0% | 100% | 100% |

## Migration Phases

### Phase 1: Foundation
1. Set up literate programming tooling
2. Create `.lit` file templates
3. Convert critical modules to `.lit` format
4. Set up Dhall build system

### Phase 2: Infrastructure
1. Set up R2 bucket and CAS layer
2. Implement armitage witness proxy
3. Set up Buck2/DICE build system
4. Implement typed toolchain system

### Phase 3: API & Services
1. Implement NEWSPECS unified API
2. Build MAESTRO orchestrator
3. Implement event sourcing
4. Set up multi-agent workflows

### Phase 4: Integration
1. Integrate trtllm serving
2. Set up model engine pipeline
3. Implement speculative decoding
4. Complete attestation system

## Critical Path

1. **Literate Programming** - Required for all code
2. **Dhall Build System** - Required for builds
3. **R2 CAS** - Required for storage
4. **Armitage** - Required for builds
5. **NEWSPECS API** - Required for services
6. **trtllm** - Required for LLM serving

## Next Steps

1. Create literate programming migration plan
2. Set up Dhall build infrastructure
3. Implement R2 CAS layer
4. Build armitage witness proxy
5. Implement NEWSPECS API endpoints
6. Integrate trtllm serving
