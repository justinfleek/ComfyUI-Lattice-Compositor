# Implementation Plan: Universal WebGPU Rendering Engine

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                              // implementation // plan // v1.0
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Generated:** 2026-02-26
**Source:** Council analysis of 190-paper survey (`need_to_implement.md`)
**Status:** ACTIVE

## Core Architecture Principles

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│   Lean4 (Source of Truth)                                                   │
│     ↓ generates                                                             │
│   Schema.purs (PureScript types)                                            │
│   Schema.hs   (Haskell types)                                               │
│   Schema.wgsl (WebGPU struct definitions)                                   │
│     ↓ all serialize to                                                      │
│   Schema.bin  (binary wire format, UUID5-addressed)                         │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Language Responsibilities

| Language | Role | Hot Path? |
|----------|------|-----------|
| **Lean4** | Prove properties, generate types | Build-time only |
| **Haskell** | Agent logic, constraint solving, diffusion orchestration | Yes (backend) |
| **PureScript** | Type definitions, Schema atoms, translation layer | Build-time + type checking |
| **WebGPU/WGSL** | Interpret Element bytes → GPU commands | Yes (frontend) |
| **JavaScript** | NONE in hot path | Legacy export only |
| **CSS** | NONE anywhere | Legacy export only |

### The Data Flow

```
Agent (Haskell)
  ↓ emits
Identified<Element> (typed, UUID5-tagged)
  ↓ serializes to
ByteBuffer (GPU-native layout)
  ↓ transfers via
Zero-copy to GPU
  ↓ interpreted by
Minimal WebGPU Runtime (pipeline dispatcher)
  ↓ outputs
Pixels / Haptics / Audio
```

## Schema Additions Required

### 1. Memory-Layout-Aware Types

```purescript
-- Types must specify their GPU representation
type GPUStorable a = 
  { value :: a
  , sizeBytes :: Int
  , alignment :: Int
  , serialize :: a → ByteBuffer
  , deserialize :: ByteBuffer → Maybe a
  }
```

**Lean4 proof required:** `deserialize (serialize x) = x` for all types

### 2. Temporal Identity

```purescript
-- Everything has stable identity across frames
type Identified a =
  { uuid :: UUID5
  , value :: a
  , generation :: Int  -- Increments on change, enables cache invalidation
  }
```

**Lean4 proof required:** Same content → same UUID5 (determinism)

### 3. Hierarchical Grouping

```purescript
-- Groups share transforms, reduce bandwidth
type Group a =
  { groupId :: UUID5
  , transform :: Transform3D
  , members :: Array (Identified a)
  , boundingVolume :: AABB  -- For culling
  }
```

**Critical for swarm scale:** 1000 agents moving together = 1 transform update, not 1000

### 4. Utility Metadata

```purescript
-- Submodular selection needs scores
type Prioritized a =
  { value :: a
  , utility :: UnitInterval
  , budget :: ResourceBudget
  , lastAccessed :: Timestamp
  , dependents :: Array UUID5
  }
```

**Lean4 proof required:** Greedy selection achieves (1 - 1/e) ≈ 63% of optimal

### 5. Diff Primitives

```purescript
-- Don't send full state, send changes
data Patch a
  = NoChange
  | Replace a
  | UpdateField FieldName ByteBuffer
  | ApplyTransform Transform3D
  | Composite (Array (Patch a))
```

**Bandwidth math:**
- Full frame: 1B agents × 80 bytes = 80 GB (impossible)
- With diffs: 1M changed × 80 bytes + hierarchical grouping = ~100 MB (feasible)

## Interpreter Design (Minimal WebGPU Runtime)

The interpreter is intentionally dumb. Intelligence lives in Haskell.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│ WebGPU Interpreter                                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│ 1. Pipeline Registry                                                        │
│    - Pre-compiled pipeline for each Element type                            │
│    - Gaussian splatting, rectangles, text, etc.                             │
│                                                                             │
│ 2. Buffer Pool                                                              │
│    - UUID5-keyed GPU buffers                                                │
│    - Reusable across frames                                                 │
│    - LRU eviction when memory constrained                                   │
│                                                                             │
│ 3. Diff Applicator                                                          │
│    - Applies Patch to GPU buffers in-place                                  │
│    - No CPU-side copy when possible                                         │
│                                                                             │
│ 4. Frame Scheduler                                                          │
│    - Submodular selection: what to render this frame?                       │
│    - Respects latency budget (16.67ms at 60fps)                             │
│    - Graceful degradation under load                                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Haskell Backend Responsibilities

| Component | Papers | Description |
|-----------|--------|-------------|
| Agent Runtime | FLAME GPU, TeraAgent | Execute agent logic, emit `Identified Element` |
| Diff Computer | Adapton, Self-Adjusting | Compare frames, emit `Patch` |
| Constraint Solver | Cassowary, XPBD | Layout computation, physics |
| Diffusion Orchestrator | StreamDiffusion, LCM | Schedule diffusion across frames |
| Swarm Coordinator | Boids, Vicsek, Cucker-Smale | Topological neighbor discovery |

## Latency Budget (60 FPS Target)

| Stage | Budget | Notes |
|-------|--------|-------|
| Haskell agent computation | 2ms | Simple agents only at this budget |
| Diff computation | 1ms | Incremental, not full comparison |
| Serialization | 1ms | Zero-copy when possible |
| Network transfer | 2ms | Local only; network adds latency |
| GPU compute | 8ms | Diffusion is the bottleneck |
| GPU rasterization | 2ms | 3DGS can do this |
| Display | 1ms | Fixed overhead |
| **Total** | **17ms** | Slightly over budget — need optimization |

## Critical Insights from Council

### 1. UUID5 is the Bridge

Same UUID5 across frames means:
- Same entity (temporal coherence)
- Interpolatable (smooth animation)
- Cacheable (GPU resources persist)
- Deduplicatable (multiple agents, same output)

### 2. Rendering is Allocation

At billion-agent scale, you cannot render everything. Submodular optimization decides:
- What contributes most to user's goal?
- What fits in GPU memory?
- What meets latency budget?

### 3. The Schema is Already Capable

Most of the 190 papers describe processes whose outputs fit existing Schema atoms:
- Diffusion → `Tensor Shape Color`
- Gaussians → `{ position, covariance, color, opacity }`
- Constraints → `{ element, position, size }`

The gap is the **interpreter** and **serialization**, not the types.

### 4. Temporal Coherence Requires Identity + Velocity

```purescript
type AnimatedElement msg =
  { identity :: UUID5
  , current :: Element msg
  , velocity :: ElementDelta  -- For prediction/interpolation
  }
```

## Implementation Priority

| Priority | Component | Effort | Impact | Dependencies |
|----------|-----------|--------|--------|--------------|
| **P0** | GPUStorable typeclass + Lean proofs | 2 weeks | Critical | None |
| **P0** | Identified wrapper + UUID5 | 1 week | Critical | GPUStorable |
| **P1** | Patch diff types | 2 weeks | High | Identified |
| **P1** | Minimal WebGPU interpreter | 3 weeks | High | GPUStorable |
| **P2** | Group hierarchical identity | 2 weeks | High | Identified |
| **P2** | Prioritized + submodular selection | 2 weeks | High | Existing Allocation.purs |
| **P3** | Gaussian splatting pipeline | 3 weeks | Medium | Interpreter |
| **P3** | Diffusion pipeline | 4 weeks | Medium | Interpreter |
| **P4** | Swarm topology module | 2 weeks | Medium | Group |
| **P4** | Voice-driven UI | 4 weeks | Medium | Full stack |

## Novel Contributions

The survey identifies gaps that this system addresses:

1. **Cross-language type-safe serialization** — Lean4 generates PureScript, Haskell, and WGSL types with proven equivalence

2. **WebGPU from functional languages** — No existing paper addresses Haskell/PureScript → WGSL

3. **AI self-representation as first-class** — Agents choose their visual representation using Schema atoms

4. **Submodular rendering allocation** — Formal guarantees on what gets rendered under constraints

---

                                                               — Council v1.0
                                                                    2026-02-26
