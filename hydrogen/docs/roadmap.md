# hydrogen
> The purest web design language ever created.

UI as data, not framework-specific code. Pure PureScript describing interfaces that targets interpret to reality: DOM, Canvas, WebGL, Static HTML. Zero external framework dependencies.

**Build Status:** 0 errors, 0 warnings (Lean: 3192 jobs, PureScript: 905 files)
**Schema:** 516 PureScript files across 17 pillars (~166K LOC)
**Proofs:** 80 Lean files, ~1100 theorems, 16 axioms, **0 sorry**

---

## Alpha Release (First Version)

### Schema Pillars — Complete

All atoms, molecules, and compounds implemented with full type safety.

- [x] **Color** (53 files) — sRGB, P3, LAB, LCH, OKLAB, OKLCH, CMYK, XYZ, camera log curves (ARRI LogC, Sony S-Log3, RED, Panasonic V-Log, Canon Log3, BMD Film), LUT support, CDL, lift/gamma/gain, ICC profiles, video spaces (YCbCr, YUV, YIQ)
- [x] **Dimension** (38 files) — Device units (Pixel, DP, SP), SI prefixes (complete from yocto to quetta), physical units (metric, imperial, atomic, astronomical), typographic units, relative units (em, rem, ch), viewport/container units, flex units
- [x] **Geometry** (46 files) — Angles (degrees, radians, gradians, turns, arc minute/second), bezier control, SVG path commands, points (2D, 3D, polar, spherical), shapes (circle, ellipse, rectangle, polygon, star, arc), curves (quadratic, cubic, catmull-rom, B-spline, NURBS), transforms, squircle, clip path, mask
- [x] **Typography** (36 files) — Font weight/width, size/spacing, optical sizing, OpenType metrics, font families/stacks, type scales, OpenType features (ligatures, numerals, fractions, stylistic sets, kerning, CJK)
- [x] **Material** (42 files) — Blur/effects, noise (Perlin, simplex, Worley, FBM), borders, gradients (linear, radial, conic, mesh), fill types, surface compounds (matte, glossy, metallic, satin, textured), frosted glass, neumorphism, duotone
- [x] **Elevation** (10 files) — Z-index, shadow parameters, perspective, depth of field, box/drop/text shadows, semantic elevation levels (0-5), parallax, depth stack, floating UI
- [x] **Temporal** (35 files) — Time units, frame-based timing, progress/iteration, easing parameters, spring physics, keyframes, all 30 standard easing functions, animation orchestration (sequence, parallel, stagger, timeline)
- [x] **Reactive** (18 files) — Interactive flags (enabled, visible, selected, etc.), progress states, focus ring, loading/selection states, semantic states (idle, loading, success, error), data states, validation states, feedback types
- [x] **Gestural** (30 files) — Pointer metrics, motion, timing (click count, hold duration), scroll, multi-touch, gesture compounds (tap, swipe, pan, pinch, rotate), drag and drop, keyboard, focus management, selection, hover patterns, context menu, vim-style key sequences, triggers
- [x] **Haptic** (4 files) — Vibration parameters, audio parameters, haptic events/patterns, impact/notification/selection feedback, iOS system patterns
- [x] **Audio** (22 files) — Level/amplitude, frequency, time/duration, stereo/spatial, synthesis (oscillators, filters, envelopes, LFOs), effects (reverb, delay, compressor, EQ, distortion, chorus, phaser, flanger, gate, limiter), analysis (waveform, spectrum, metering, pitch/BPM detection), audio effect ADT, AV sync
- [x] **Spatial** (46 files) — Position/scale, camera parameters (FOV, clipping, focal length, aperture), light parameters, PBR material parameters, vectors (Vec2-4), rotations (Euler, quaternion, axis-angle), matrices, bounds (AABB, sphere, OBB, frustum), camera types, light types, materials (StandardPBR, unlit, transparent, subsurface, cloth, hair, toon), geometry (mesh, skinned mesh, instanced, point cloud), XR (session, anchor, plane, mesh, hand, controller, hit test), scene graph
- [x] **Accessibility** (6 files) — WAI-ARIA 1.2 roles (widget, composite, structure, window), states, properties, live regions, landmarks, molecules (disclosure, selection, range, tab, dialog)
- [x] **Sensation** (8 files) — Proprioceptive atoms, contact, environment, force, temporal perception, social awareness, body/environment/social state molecules, experiential compounds (comfort, distress, flow, grounding, vigilance)
- [x] **Scheduling** (8 files) — Time-based scheduling primitives
- [x] **Epistemic** (6 files) — Model-level phenomenology (coherence, confidence, valence, alignment, affect, operational state)

### Schema Pillars — In Progress

- [x] **Brand** (37 files, ~90%) — Tokens (color, spacing, shadow, radius, duration, easing, z-index, size), themes (light/dark/contrast/auto), logo system, typography, palette, voice, identity, mission, tagline, values, provenance. Missing: export formats (CSS variables, Tailwind, Figma tokens, JSON)
- [x] **Attestation** (11 files) — Cryptographic attestation primitives: SHA-256/512, Keccak-256, UUID5, Merkle trees, timestamps, signed data (ECDSA/Ed25519/RSA), W3C DIDs (key/web/ethr/ion/pkh methods, DID documents, verification methods), W3C Verifiable Credentials (credential types, proofs, status), W3C Verifiable Presentations

### Runtime Targets

- [x] Basic Element type (pure data describing UI)
- [x] Event handling (msg dispatch)
- [ ] **Hydrogen.Target.DOM** — Direct browser manipulation with diff/patch
- [ ] **Hydrogen.Target.Static** — HTML strings for SSG (partial: SSG.purs exists)
- [ ] **Hydrogen.Target.Canvas** — 2D canvas rendering
- [ ] **Hydrogen.Target.WebGL** — 3D rendering
- [ ] **Hydrogen.Target.Halogen** — Full Halogen integration (pending)

### Lean Proofs

- [x] Math proofs (19 files) — Vec2/3/4, Mat3/4, quaternion, Euler, ray, plane, sphere, triangle, frustum, Box3, constraint, force, integration
- [x] Schema/Color proofs (13 files) — Hue rotation (fully verified), color conversions (10 proven theorems)
- [x] WorldModel proofs (9 files) — Affective, attention, consensus, economy, governance, integrity, pose, rights
- [x] Light proofs (6 files) — Attenuation, directional, point, shadow, spot
- [x] Material proofs (5 files) — BRDF, ISP, sparkle
- [x] Geometry proofs (5 files) — Bounds, mesh, primitives, texture, vertex
- [x] Scene proofs (4 files) — Diff, graph, node, resource
- [x] Camera proofs (3 files) — Lens, projection, types
- [x] GPU proofs (1 file) — Diffusion kernel types
- [x] Eliminate all `sorry` placeholders (DONE — 0 sorry in codebase)
- [ ] HSL/LCH conversion proofs
- [ ] Dimension bounds proofs
- [ ] Transform composition proofs

### API Layer

- [x] **Query** — Data fetching with caching, deduplication, stale-while-revalidate
- [x] **Router** — Type-safe client-side routing with ADT routes
- [x] **API Client** — HTTP client with JSON, auth, logging
- [x] **SSG** — Static site generation with route integration
- [x] **Format** — Pure formatting functions (bytes, numbers)
- [x] **RemoteData** — Lawful monad for async state

### GPU/Compute

- [x] **Diffusion** (~840 lines) — Complete diffusion kernel types for AI image generation (schedulers, noise types, guidance modes, implicit solvers, VAE encode/decode, denoising, CFG, latent blending, conditioning, presets)

---

## Later On (Future Work)

### Schema Extensions

- [ ] Voice pillar — TTS synthesis parameters, speech recognition, formants, IPA vowels, voice character presets
- [ ] Complete SI prefix atoms (quetta through yocto for all base units)
- [ ] Animation integration compounds (Lottie, Rive, GSAP, Framer Motion configs)

### Runtime Targets

- [ ] WebGPU target for high-performance rendering
- [ ] Native targets (iOS/Android via wasm or native bindings)
- [ ] Server-side rendering with streaming

### Proofs

- [ ] Formalize interval arithmetic for floating-point precision bounds
- [ ] Prove all color conversion roundtrip properties
- [ ] Proof-carrying code generation (Lean4 → PureScript with embedded proofs)
- [ ] Replace remaining axioms with constructive proofs where feasible

### Tooling

- [ ] Design token export CLI (CSS variables, Tailwind config, Figma tokens)
- [ ] Visual schema explorer / documentation generator
- [ ] Integration with sensenet//publish for scope-graph docs

### Integration

- [ ] LATTICE integration (motion graphics rendering)
- [ ] COMPASS integration (AI marketing agents)
- [ ] Brand ingestion pipeline (analyze existing assets → generate Schema tokens)

---

## File Counts by Pillar

| Pillar | Files | Status |
|--------|-------|--------|
| Color | 53 | Complete |
| Spatial | 46 | Complete |
| Geometry | 46 | Complete |
| Material | 42 | Complete |
| Dimension | 38 | Complete |
| Typography | 36 | Complete |
| Temporal | 35 | Complete |
| Gestural | 30 | Complete |
| Brand | 24 | In Progress (~60%) |
| Motion | 23 | Complete |
| Audio | 22 | Complete |
| Phone | 20 | Complete |
| Reactive | 18 | Complete |
| Attestation | 11 | In Progress (~80%) |
| Elevation | 10 | Complete |
| Sensation | 8 | Complete |
| Scheduling | 8 | Complete |
| Epistemic | 6 | Complete |
| Accessibility | 6 | Complete |
| Tensor | 4 | Complete |
| Haptic | 4 | Complete |
| Graph | 4 | Complete |
| Physics | 2 | Complete |
| Navigation | 2 | Complete |
| Compute | 2 | Complete |

**Total:** 516 PureScript Schema files

---

## Proof Statistics

| Domain | Files | Theorems | Notes |
|--------|-------|----------|-------|
| Math | 19 | ~549 | Vec, Mat, Quaternion, physics |
| Schema/Color | 13 | ~36 | Hue fully verified, conversions partial |
| WorldModel | 9 | ~119 | Agent states, governance, rights |
| Light | 6 | ~58 | Attenuation, shadows |
| Material | 5 | ~107 | BRDF, ISP |
| Geometry | 5 | ~69 | Mesh, bounds, primitives |
| Scene | 4 | ~42 | Graph, diff, resources |
| Camera | 3 | ~25 | Lens, projection |
| Optimize | 5 | ~60 | Submodular optimization (RAOCO, continuous greedy, FAA) |
| GPU | 1 | — | Diffusion types |

**Total:** 80 Lean files, ~1100 theorems/lemmas, 16 axioms, **0 sorry**

---

## Playground Completion (AI Velocity Estimate)

Based on observed velocity (~80K LOC/day, ~$3K/day at current token costs), here's the estimate to complete the playground with full runtime targets:

| Component | LOC Est. | AI Hours | Notes |
|-----------|----------|----------|-------|
| Canvas Target | ~500 | 2-3h | 2D rendering, path drawing, compositing |
| WebGL/WebGPU bindings | ~1,500 | 4-6h | Shader compilation, buffer management, draw calls |
| Lottie integration | ~800 | 3-4h | JSON parsing, animation interpolation |
| Icon system | ~400 | 2h | SVG sprite handling, icon registry |
| Animation runtime loop | ~600 | 3-4h | requestAnimationFrame, spring physics |
| Playground runtime wiring | ~400 | 2-3h | Element → Target dispatch |
| Video/Audio players | ~1,300 | 5-7h | Media controls, streaming, sync |
| Map component | ~1,000 | 4-5h | Tile rendering, gestures, markers |
| 3D model viewer | ~1,200 | 5-6h | glTF loading, orbit controls, PBR |
| Code editor | ~1,500 | 5-6h | Syntax highlighting, line numbers, selection |
| Effects (blur, glow) | ~600 | 2-3h | WebGL post-processing |
| Reactive triggers | ~400 | 2-3h | Event → Msg wiring, debounce/throttle |
| Polish/a11y/tests | ~2,000 | 6-8h | ARIA, keyboard nav, test coverage |
| **Total** | **~12,200** | **40-60h** | **~2-3 days, ~$1-2K** |

### Velocity Context

The current codebase was built in approximately 4 days of AI development time:
- **316K LOC PureScript** (Schema, API, Render)
- **80 Lean proof files** (~1100 theorems)
- **Cost:** ~$3K in API tokens

This suggests the playground completion is well within a single focused sprint.
