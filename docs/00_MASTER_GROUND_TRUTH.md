# WEYL COMPOSITOR — MASTER GROUND TRUTH

**Document ID**: 00_MASTER_GROUND_TRUTH
**Version**: 1.1.0
**Last Updated**: December 20, 2025
**Status**: CANONICAL
**Authority**: This document overrides all prior chat instructions, inline code comments, and legacy assumptions.

> **Implementation Status (Dec 2025):** The core determinism rule is implemented via `MotionEngine.ts` which provides pure frame evaluation. Particle system uses checkpoint-based determinism with SeededRandom (Mulberry32). See `HANDOFF.md` for current implementation status.

---

## PURPOSE OF THIS DOCUMENT

This is the **single source of truth** for Weyl Compositor. Claude Code must use this document to:

1. **Audit** the existing codebase for violations
2. **Identify** systems that contradict these specifications
3. **Correct** code that deviates from these rules
4. **Verify** that the architecture matches the intent

**If any code, comment, or prior instruction contradicts this document, this document wins.**

---

## 1. PROJECT IDENTITY

### 1.1 What Weyl Compositor Is

Weyl Compositor is a **deterministic, frame-addressable motion graphics and conditioning engine** built specifically for the **ComfyUI ecosystem**.

**Weyl is a compiler for motion and conditioning data.**

Conceptually, it combines:

- **Adobe After Effects** — timeline, graph editor, layers, precomps
- **Trapcode Particular / X-Particles** — procedural particle systems
- **TouchDesigner / Nuke** — deterministic graph evaluation and reproducibility

### 1.2 What Weyl Is NOT

Weyl is **NOT**:

- ❌ A real-time game engine
- ❌ A continuously advancing simulation
- ❌ A playback-first renderer
- ❌ A UI demo
- ❌ A reactive animation system

**Claude Code must audit the codebase for any patterns that treat Weyl as a real-time system. These are violations.**

### 1.3 Core Product Goals

The system must support:

- Frame-accurate animation
- Deterministic scrubbing (frame N always produces identical output)
- Keyframed properties with graph-based interpolation
- Audio-reactive motion
- Procedural particle systems
- Camera animation with spline paths
- Timeline and Curve Editor
- PropertyLink-style property linking
- Precompositions
- Deterministic exports for diffusion models

**Visual polish is explicitly out of scope until correctness is achieved.**

---

## 2. THE DETERMINISM RULE

### 2.1 Absolute Requirement (NON-NEGOTIABLE)

> **Evaluating frame N must always produce the exact same result, regardless of playback history or scrub order.**

This means:

- Scrubbing `0 → 300 → 10 → 300` must yield **identical** output at frame 300
- Rendering frame 100 ten times must produce **byte-identical** output
- Particles, audio, camera, transforms, and exports must **all** obey this rule

**If any system violates this, it is considered architecturally broken.**

### 2.2 Forbidden Patterns (Global)

The following are **FORBIDDEN** inside any evaluation code:

```typescript
// ❌ NEVER USE IN EVALUATION
Date.now()
performance.now()
Math.random()
requestAnimationFrame()  // for evaluation logic
this.state += delta
particle.age += dt
camera.position += velocity * dt
previousFrame  // referencing prior frame state
lastFrame      // referencing prior frame state
```

### 2.3 Required Patterns

```typescript
// ✅ ALWAYS USE
const state = evaluate(frame, project, config)
const position = interpolate(keyframes, frame)
const random = seededRNG(seed, frame, particleId)
Object.freeze(result)  // Immutable outputs
```

---

## 3. ARCHITECTURAL PRINCIPLES

### 3.1 Single Time Authority

There must be **exactly one** system that answers:

> "What is the evaluated state of the project at frame N?"

This system is called **MotionEngine**.

**Audit Instruction**: Claude Code must verify that MotionEngine is the sole evaluator. If frame evaluation occurs in multiple places, this is a violation.

### 3.2 Separation of Concerns

| Layer | Responsibility | Must NOT Do |
|-------|----------------|-------------|
| **UI (Timeline/Graph)** | Edit data only | Evaluate animation |
| **Stores** | Hold UI state only | Store evaluated values |
| **MotionEngine** | Pure evaluation | Mutate state |
| **Render Engine** | Apply evaluated values | Evaluate or interpolate |
| **Particles** | Deterministic evaluation | Accumulate state |

### 3.3 Data Flow

```
Project Data (immutable)
       ↓
MotionEngine.evaluate(frame, project)
       ↓
FrameState (frozen, immutable)
       ↓
RenderEngine.applyFrameState(frameState)
       ↓
Display / Export
```

---

## 4. MOTIONENGINE RESPONSIBILITIES

MotionEngine is responsible for:

1. ✅ Interpolating all keyframed properties
2. ✅ Resolving property dependencies (pickwhip links)
3. ✅ Sampling pre-computed audio features at frame N
4. ✅ Evaluating layer visibility at frame N
5. ✅ Evaluating camera state at frame N
6. ✅ Requesting particle snapshots from ParticleSimulationController
7. ✅ Composing layer transforms

MotionEngine is **NOT** responsible for:

- ❌ Storing evaluated values
- ❌ Advancing simulations
- ❌ Playing audio
- ❌ Managing UI state
- ❌ Rendering pixels

---

## 5. FRAMESTATE OUTPUT

Every evaluation produces a **FrameState**:

```typescript
interface FrameState {
  readonly frame: number
  readonly timestamp: number
  readonly layers: readonly EvaluatedLayer[]
  readonly camera: EvaluatedCamera
  readonly particles: ParticleSnapshot
  readonly audio: EvaluatedAudio
}
```

**All FrameState objects must be frozen and immutable.**

---

## 6. DOCUMENT INDEX

This specification is split into the following documents:

| Document | Purpose |
|----------|---------|
| `00_MASTER_GROUND_TRUTH.md` | This document — overview and principles |
| `01_TYPE_DEFINITIONS.md` | All TypeScript interfaces and types |
| `02_MOTION_ENGINE.md` | Core evaluation engine specification |
| `03_LAYER_SYSTEM.md` | Layer types, evaluation, composition |
| `04_PARTICLE_SYSTEM.md` | Deterministic particle architecture |
| `05_PARTICLE_SYSTEM.md` | Research-validated particle spec (v2.0) |
| `06_CAMERA_SPLINE.md` | Camera and 3D spline system |
| `07_TEXT_SHAPE.md` | Text, fonts, and vector graphics |
| `08_TIMELINE_GRAPH.md` | Timeline and graph editor UI contract |
| `09_PICKWHIP_DEPENDENCIES.md` | Property linking and DAG evaluation |
| `10_AUDIO_REACTIVITY.md` | Audio analysis and mapping |
| `11_PRECOMPOSITION.md` | Nested composition system |
| `12_COMPOSITION_IMPORT.md` | Project structure and asset import |
| `13_EXPORT_PIPELINE.md` | Export buffers and ComfyUI integration |
| `14_VISION_AUTHORING.md` | AI-assisted motion authoring |
| `15_DETERMINISM_TESTING.md` | Validation and test requirements |
| `16_IMPLEMENTATION_CHECKLIST.md` | Phased build plan |

---

## 7. DEFINITION OF SUCCESS

The project is considered **unblocked** when:

1. ✅ MotionEngine is the sole evaluator
2. ✅ Frame evaluation is deterministic
3. ✅ Scrubbing is safe (order-independent)
4. ✅ Particles replay correctly
5. ✅ Timeline truly drives output (data only)
6. ✅ Graph editor edits propagate correctly
7. ✅ All exports are bit-identical across runs

**Only after this is achieved may visuals or features be addressed.**

---

## 8. FINAL AUTHORITY

This document and its companion specifications override:

- All prior chat instructions
- Inline code comments
- Legacy assumptions
- Visual output that "looks correct"

**When in doubt:**

> Favor **determinism**, **purity**, and **clarity** over speed or appearance.

---

## 9. CODEBASE LOCATION

Repository: `https://github.com/justinfleek/weyl-compositor`

Claude Code should:
1. Clone the repository
2. Run the audit script for forbidden patterns
3. Compare implementation against these specifications
4. Document all violations
5. Propose corrections

---

**Next Document**: [01_TYPE_DEFINITIONS.md](./01_TYPE_DEFINITIONS.md)
