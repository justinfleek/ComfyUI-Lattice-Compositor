# Master Integration Checklist: Schema → GPU → Diffusion

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                           // master // integration // checklist
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "A button animation and a diffusion trajectory are the same math.
    One renders to pixels, one renders to latent space conditioning."

                                                                      — Session

**Created:** 2026-02-27
**Status:** ACTIVE — Single source of truth
**Goal:** Pure data window between humans and AI

---

## The Vision

Build a system where:

1. **Schema atoms** (Hue, Pixel, UnitInterval) compose into UI compounds
2. **Compounds** (Button, ColorPicker) render to **WebGPU** OR **diffusion conditioning**
3. **Same animation math** drives interactive UI AND AI video generation
4. **No strings, no CSS** — pure typed data at every layer
5. **Proven invariants** (Lean4) guarantee correctness at billion-agent scale

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  HUMAN / AI INTERFACE                                                       │
│  After Effects-like timeline, keyframes, layers                             │
│  (Vue reference exists, final impl is PureScript → WebGPU)                  │
├─────────────────────────────────────────────────────────────────────────────┤
│  HYDROGEN SCHEMA                                                            │
│  Every atom is bounded, proven, composable                                  │
│  Button = f(BrandSchema, AnimationState, InteractionState)                  │
├─────────────────────────────────────────────────────────────────────────────┤
│  COMPASS (Animation/Motion)                                                 │
│  Keyframes, easing, expressions - deterministic frame evaluation            │
│  Same math that drives UI drives diffusion conditioning                     │
├─────────────────────────────────────────────────────────────────────────────┤
│  RENDER TARGETS                                                             │
│  WebGPU → pixels (interactive)                                              │
│  Export → trajectories (MotionCtrl, Wan, ATI, TTM)                          │
│  Same data, different projections                                           │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Phase 0: Foundation Audit

### 0.1 Schema Atoms Status

| Pillar | Files | Status | GPUStorable | Notes |
|--------|-------|--------|-------------|-------|
| Color | 54 | ✅ Complete | ⚠️ Partial | Need instances for all spaces |
| Dimension | 39 | ✅ Complete | ⚠️ Partial | Vec2/3/4 done, others needed |
| Geometry | 65 | ✅ Complete | ⚠️ Partial | Transform, Angle done |
| Typography | 36 | ✅ Complete | ❌ Not started | Need font metrics → GPU |
| Material | 42 | ✅ Complete | ❌ Not started | Noise, gradients |
| Elevation | 10 | ✅ Complete | ❌ Not started | Shadows, depth |
| Temporal | 35 | ✅ Complete | N/A | Pure computation |
| Motion | 40 | ✅ Complete | ❌ Not started | Keyframes, springs |
| Reactive | 19 | ✅ Complete | N/A | State flags |
| Gestural | 30 | ✅ Complete | N/A | Input events |
| Haptic | 4 | ✅ Complete | N/A | Device feedback |
| Audio | 22 | ✅ Complete | ⚠️ Partial | WebAudio integration |
| Spatial | 46 | ✅ Complete | ⚠️ Partial | 3D types |
| Brand | 37 | ✅ Complete | N/A | Token composition |

**AUDIT RESULT (2026-02-27):**
- Total Schema files: 585
- GPUStorable instances: 30 (in `Schema/GPU/Storable.purs`)
- Coverage: ~5% (most Schema atoms not yet GPU-serializable)

GPUStorable instances implemented:
- Primitives: Number, Int, Boolean, UnitInterval
- Vectors: Vec2, Vec3, Vec4, Point2D, Size2D
- Color: SRGB, SRGBA, RGB, RGBA, Channel, Opacity, Hue, Saturation, Lightness, HSL, HSLA
- Geometry: Degrees, Radians, Turns, Radius
- Transform: Scale, Translate, Rotate, Skew, Origin, Transform2D

### 0.2 GPU Layer Status

| Component | File | Lines | Status |
|-----------|------|-------|--------|
| GPUStorable typeclass | `Schema/GPU/Storable.purs` | 300+ | ✅ Exists |
| DrawCommand ADT | `GPU/DrawCommand.purs` | ? | ✅ Exists |
| WebGPU Device | `GPU/WebGPU/Device.purs` | 254+ | ✅ Exists |
| WebGPU Pipeline | `GPU/WebGPU/Pipeline.purs` | ? | ✅ Exists |
| Diffusion types | `GPU/Diffusion.purs` | ? | ✅ Exists |
| Scene3D | `GPU/Scene3D/` | 16 files | ✅ Exists |
| Glyph rendering | `GPU/GlyphConvert.purs` | ? | ✅ Exists |
| UI Render | `GPU/UI/Render.purs` | ? | ⚠️ Partial |

### 0.3 Runtime Status

| Target | File | Status | Notes |
|--------|------|--------|-------|
| DOM | `Target/DOM.purs` | ✅ 450 lines | diff/patch |
| Static | `Target/Static.purs` | ✅ 292 lines | SSG |
| Halogen | `Target/Halogen.purs` | ✅ 310 lines | Adapter |
| Canvas | — | ❌ Not started | 2D rendering |
| WebGL/WebGPU | — | ❌ Not started | Needs wrapper |

### 0.4 Proof Status

| Area | Files | Theorems | Axioms | Sorry |
|------|-------|----------|--------|-------|
| Math | 19 | ~400 | ? | 0 |
| Schema | 21 | ~300 | ? | 0 |
| GPU | 3 | ~100 | ? | 0 |
| **Total** | 95 | 1330 | 52 | **0** |

---

## Phase 1: Viewport Layer

**Goal:** Create the container layer that houses Elements and World Models.

### 1.1 Viewport Core Types
- [ ] Create `Hydrogen/Viewport.purs`
- [ ] `Viewport` type with shape, bounds, elevation, fill, children
- [ ] `ViewportContent` ADT (Elements, SubViewports, WorldModel, Diffusion, Mixed)
- [ ] `ViewportFill` ADT (Solid, Gradient, Noise, Diffusion, Image, Video, Transparent)
- [ ] `Elevation` type with rest/hover/pressed distances + spring config

### 1.2 Viewport Interactions
- [ ] Create `Hydrogen/Viewport/Interaction.purs`
- [ ] `Interaction` ADT (OnHover, OnPress, OnDrag, OnGesture, OnTrigger)
- [ ] Integration with Gestural pillar atoms

### 1.3 Viewport Triggers
- [ ] Create `Hydrogen/Viewport/Trigger.purs`
- [ ] `Trigger` type (source, target, condition, effect, msg)
- [ ] `TriggerCondition` ADT (hover, press, drag, animation, value change, time, intersection)
- [ ] `TriggerEffect` ADT (elevation, opacity, transform, animation, fill, filter, message)

### 1.4 Diffusion Surface Integration
- [ ] Create `Hydrogen/Viewport/Diffusion.purs`
- [ ] `DiffusionConfig` type (model, prompt, seed, strength, steps, mask, controlNet)
- [ ] `DiffusionSurface` type (scheduler, guidance, latentBlending, frameCoherence)
- [ ] Wire to existing `GPU/Diffusion.purs` types

### 1.5 Viewport Proofs
- [ ] Create `proofs/Hydrogen/Viewport/Core.lean`
- [ ] Prove: Elevation bounds [0, 1000]
- [ ] Prove: Viewport nesting depth bounded
- [ ] Prove: Trigger graph acyclic (no infinite loops)

---

## Phase 2: GPUStorable Completeness

**Goal:** Every Schema atom that needs GPU representation has GPUStorable.

### 2.1 Color Instances
- [x] SRGB (4 bytes: r, g, b, padding)
- [x] Channel (1 byte)
- [x] Opacity (4 bytes: f32)
- [x] Hue (4 bytes: f32 degrees)
- [x] Saturation (4 bytes: f32)
- [x] Lightness (4 bytes: f32)
- [x] HSL (16 bytes: vec4 with padding)
- [x] HSLA (16 bytes: vec4)
- [ ] OKLCH (16 bytes: L, C, H, A)
- [ ] LAB (16 bytes: L, a, b, padding)
- [ ] LinearRGB (16 bytes: r, g, b, padding)

### 2.2 Dimension Instances
- [x] Vec2 (8 bytes)
- [x] Vec3 (16 bytes with padding)
- [x] Vec4 (16 bytes)
- [x] Point2D (8 bytes)
- [ ] Size2D (8 bytes)
- [ ] Pixel (4 bytes: f32)
- [ ] Bounds2D (16 bytes: minX, minY, maxX, maxY)

### 2.3 Geometry Instances
- [x] Angle (4 bytes: f32 radians)
- [x] Radius (4 bytes: f32)
- [x] Transform2D (24 bytes: 6 f32)
- [ ] Transform3D (64 bytes: mat4)
- [ ] CornerRadii (16 bytes: 4 f32)
- [ ] Quaternion (16 bytes: x, y, z, w)

### 2.4 Material Instances
- [ ] Blur (4 bytes: radius)
- [ ] Shadow (24 bytes: x, y, blur, spread, color, opacity)
- [ ] Gradient stop (20 bytes: position, color)

### 2.5 Storable Proofs
- [x] `proofs/Hydrogen/Schema/GPU/Storable.lean` — roundtrip theorem
- [x] `proofs/Hydrogen/Schema/GPU/Color.lean` — color serialization
- [ ] Add proofs for each new instance

---

## Phase 3: Element → GPU Pipeline

**Goal:** Convert pure Element data to GPU draw commands.

### 3.1 DrawCommand Completeness
- [ ] Audit `GPU/DrawCommand.purs` for all needed commands
- [ ] Rectangle (position, size, fill, stroke, corners, shadow)
- [ ] Text (position, content, font, color, effects)
- [ ] Path (commands, fill, stroke)
- [ ] Image (position, size, source, effects)
- [ ] Viewport (nested rendering context)

### 3.2 Element → DrawCommand Translation
- [ ] Create `Hydrogen/GPU/Compile.purs`
- [ ] `compileElement :: Element msg → Array DrawCommand`
- [ ] Handle all Element variants (Text, Element, Keyed, Lazy, Animation, Empty)
- [ ] Layout resolution (ILP solver already exists)
- [ ] Animation interpolation (Motion pillar)

### 3.3 Viewport → DrawCommand Translation
- [ ] `compileViewport :: Viewport msg → Array DrawCommand`
- [ ] Elevation → shadow computation
- [ ] Clipping region setup
- [ ] Fill rendering (solid, gradient, noise, diffusion)
- [ ] Child element compilation

### 3.4 Target.WebGPU
- [ ] Create `Hydrogen/Target/WebGPU.purs`
- [ ] `render :: Canvas → Array Viewport msg → Effect Unit`
- [ ] Pipeline caching (same DrawCommand type → same pipeline)
- [ ] Buffer management (GPUStorable serialization)
- [ ] Frame scheduling

### 3.5 Pipeline Proofs
- [ ] Create `proofs/Hydrogen/GPU/Compile.lean`
- [ ] Prove: Same Element → same DrawCommands (determinism)
- [ ] Prove: Layout constraints satisfiable (ILP feasibility)

---

## Phase 4: Animation System Bridge

**Goal:** Unify Hydrogen Motion pillar with LATTICE animation system.

### 4.1 Keyframe Types Alignment
- [ ] Compare `Hydrogen/Schema/Motion/Keyframe.purs` with LATTICE keyframes
- [ ] Ensure identical semantics (frame, value, easing, expression)
- [ ] Create shared type definitions if needed

### 4.2 Easing Function Parity
- [ ] Verify all 35 easing functions match between systems
- [ ] Linear, ease variants, spring, elastic, bounce, back, custom bezier
- [ ] Create `Motion/Easing/Equivalence.lean` proof

### 4.3 Expression Language
- [ ] Port LATTICE expression functions to Hydrogen
- [ ] `wiggle`, `repeatAfter`, `bounce`, `inertia`, `elastic`
- [ ] Deterministic evaluation (seeded RNG)

### 4.4 Timeline/Composition
- [ ] Composition timeline types
- [ ] Layer ordering and parenting
- [ ] Pre-composition (nested timelines)

### 4.5 Frame Evaluation
- [ ] `evaluate :: Frame → Project → DeterministicResult`
- [ ] Pure function, no side effects
- [ ] Same frame + same project = identical output (proven)

---

## Phase 5: Diffusion Export System

**Goal:** Same animation data exports to AI video model conditioning.

### 5.1 Camera Trajectory Export
- [ ] Port `cameraExportFormats.ts` to PureScript
- [ ] MotionCtrl format (4x4 RT matrices per frame)
- [ ] MotionCtrl-SVD format (preset + optional poses)
- [ ] Wan 2.2 Fun Camera format (camera motion preset)
- [ ] AnimateDiff CameraCtrl format (motion type + speed + frame length)
- [ ] Full matrix export (view + projection)

### 5.2 Point Trajectory Export
- [ ] Port `wanMoveExport.ts` to PureScript
- [ ] Wan-Move format (tracks: [N][T][2], visibility: [N][T])
- [ ] NPY binary export for Python consumption
- [ ] Deterministic point tracking

### 5.3 Tensor Shape Definitions
- [ ] Port `LatentShape` to PureScript
- [ ] SDXL: { batch: 1, channels: 4, height: 128, width: 128 }
- [ ] SD3: { batch: 1, channels: 16, height: 128, width: 128 }
- [ ] Video models: { batch: 1, channels: 4, frames: T, height: H, width: W }

### 5.4 Scheduler/Sampler Config
- [ ] Port scheduler types to PureScript
- [ ] DDPM, DDIM, Euler, EulerAncestral, DPMPP2M, DPMPP2MKarras, Heun, LMS
- [ ] Sigma schedule types (strictly decreasing, terminates at 0)
- [ ] Use existing `GPU/Diffusion.purs` as base

### 5.5 Export Proofs
- [ ] Create `proofs/Hydrogen/Export/Trajectory.lean`
- [ ] Prove: Trajectory length matches frame count
- [ ] Prove: All values within model-expected bounds
- [ ] Prove: Sigma schedule invariants (from LATTICE proofs)

---

## Phase 6: UI Component Library

**Goal:** All After Effects-equivalent UI rendered via atoms.

### 6.1 Timeline Component
- [ ] Playhead (scrubbing, frame display)
- [ ] Layer tracks (reorderable, nested)
- [ ] Keyframe diamonds (semantic shapes per easing type)
- [ ] Work area (in/out points)
- [ ] Zoom/scroll controls

### 6.2 Property Panel
- [ ] Property tree (expandable groups)
- [ ] Keyframe indicators per property
- [ ] Expression editor
- [ ] Value sliders with bounds from Schema atoms

### 6.3 Curve Editor
- [ ] Bezier handle manipulation
- [ ] Multiple curves overlay
- [ ] Value/velocity graph toggle
- [ ] Snap to grid

### 6.4 Preview Window
- [ ] WebGPU rendering target
- [ ] Resolution/quality settings
- [ ] Safe areas overlay
- [ ] Guides and rulers

### 6.5 Export Panel
- [ ] Format selection (all supported targets)
- [ ] Resolution/frame rate settings
- [ ] Render queue
- [ ] Progress tracking

---

## Phase 7: LATTICE ↔ Hydrogen Integration

**Goal:** Bidirectional data flow between systems.

### 7.1 Shared Types Package
- [ ] Create `straylight-types` package
- [ ] Shared Schema atoms (duplicated currently)
- [ ] Shared animation types
- [ ] Import in both Hydrogen and LATTICE

### 7.2 Import Path
- [ ] LATTICE Vue project → export to Hydrogen Schema JSON
- [ ] Parse existing `.lattice` project files
- [ ] Convert to Hydrogen Composition type

### 7.3 Export Path
- [ ] Hydrogen Composition → LATTICE-compatible format
- [ ] Generate ComfyUI workflow JSON
- [ ] Direct diffusion model conditioning

### 7.4 Real-time Bridge
- [ ] WebSocket communication between systems
- [ ] State synchronization
- [ ] Collaborative editing support

---

## Phase 8: Proof Completion

**Goal:** All critical paths have Lean4 proofs.

### 8.1 Roundtrip Proofs
- [x] GPUStorable serialize/deserialize
- [ ] Schema atom construction/extraction
- [ ] Animation keyframe interpolation

### 8.2 Bounds Proofs
- [ ] All Schema atoms stay within bounds
- [ ] GPU buffer sizes never exceed limits
- [ ] Tensor shapes match model requirements

### 8.3 Determinism Proofs
- [ ] Same input → same output for all pure functions
- [ ] Seeded RNG produces identical sequences
- [ ] Frame evaluation determinism

### 8.4 Termination Proofs
- [ ] All recursive functions terminate
- [ ] Sigma schedules reach zero
- [ ] Layout solver converges

---

## Verification Commands

After each phase, run:

```bash
# Hydrogen
cd /home/jpyxal/jpyxal/hydrogen
nix develop --command spago build    # 0 errors, 0 warnings
nix develop --command spago test     # All tests pass
nix develop --command lake build     # Proofs check

# LATTICE standalone
cd /home/jpyxal/jpyxal/LATTICE/standalone-edition
nix develop --command cabal build    # Haskell compiles
nix develop --command lake build     # Proofs check
```

---

## Success Criteria

### Milestone 1: Basic Button Rendering
- [ ] Schema Button compound → GPUStorable bytes → WebGPU draw → pixels
- [ ] Button hover animation working
- [ ] No strings in render path

### Milestone 2: Animation Export
- [ ] Button animation → keyframe data → Wan-Move trajectory
- [ ] Same animation renders identically in UI and as export

### Milestone 3: Full Viewport Stack
- [ ] Viewport with elevation, shadows, interactions
- [ ] Nested viewports working
- [ ] Diffusion surface rendering (even placeholder)

### Milestone 4: After Effects Parity
- [ ] Timeline UI complete
- [ ] Curve editor working
- [ ] All export formats functional
- [ ] Real projects can be created

---

## Cross-References

- **Hydrogen CLAUDE.md:** `/home/jpyxal/jpyxal/hydrogen/CLAUDE.md`
- **LATTICE CLAUDE.md:** `/home/jpyxal/jpyxal/LATTICE/CLAUDE.md`
- **Continuity Vision:** `/home/jpyxal/jpyxal/hydrogen/docs/CONTINUITY_VISION.md`
- **Rendering Architecture:** `/home/jpyxal/jpyxal/hydrogen/docs/RENDERING_ARCHITECTURE.md`
- **Implementation Plan:** `/home/jpyxal/jpyxal/LATTICE/docs/INTERNAL/IMPLEMENTATION_PLAN.md`
- **Schema Completion:** `/home/jpyxal/jpyxal/LATTICE/docs/INTERNAL/SCHEMA_COMPLETION_PLAN.md`
- **Continuity Roadmap:** `/home/jpyxal/jpyxal/LATTICE/straylight-protocol/docs/rfc/straylight-008-continuity/ROADMAP.md`

---

```
                                                         — Session // 2026-02-27
```
