# hydrogen
> The purest web design language ever created.

UI as data, not framework-specific code. Pure PureScript describing interfaces that targets interpret to reality: DOM, Canvas, WebGL, Static HTML. Zero external framework dependencies.

**Build Status:** 0 errors, 0 warnings
**Tests:** 602/602 passing (2 pending)
**Schema:** 585 PureScript files across 21 pillars
**Element Compounds:** 226 UI components
**GPU/WebGPU:** 61 files
**Proofs:** 95 Lean files, 1330 theorems/lemmas, 52 axioms, 0 sorry

---

## Alpha Release (First Version)

### Schema Pillars — Complete

All atoms, molecules, and compounds implemented with full type safety.

- [x] **Color** (54 files) — sRGB, P3, LAB, LCH, OKLAB, OKLCH, CMYK, XYZ, camera log curves (ARRI LogC, Sony S-Log3, RED, Panasonic V-Log, Canon Log3, BMD Film), LUT support, CDL, lift/gamma/gain, ICC profiles, video spaces (YCbCr, YUV, YIQ)
- [x] **Dimension** (39 files) — Device units (Pixel, DP, SP), SI prefixes (complete from yocto to quetta), physical units (metric, imperial, atomic, astronomical), typographic units, relative units (em, rem, ch), viewport/container units, flex units
- [x] **Geometry** (65 files) — Angles (degrees, radians, gradians, turns, arc minute/second), bezier control, SVG path commands, points (2D, 3D, polar, spherical), shapes (circle, ellipse, rectangle, polygon, star, arc), curves (quadratic, cubic, catmull-rom, B-spline, NURBS), transforms, squircle, clip path, mask, Mesh2D
- [x] **Typography** (36 files) — Font weight/width, size/spacing, optical sizing, OpenType metrics, font families/stacks, type scales, OpenType features (ligatures, numerals, fractions, stylistic sets, kerning, CJK)
- [x] **Material** (42 files) — Blur/effects, noise (Perlin, simplex, Worley, FBM), borders, gradients (linear, radial, conic, mesh), fill types, surface compounds (matte, glossy, metallic, satin, textured), frosted glass, neumorphism, duotone
- [x] **Elevation** (10 files) — Z-index, shadow parameters, perspective, depth of field, box/drop/text shadows, semantic elevation levels (0-5), parallax, depth stack, floating UI
- [x] **Temporal** (35 files) — Time units, frame-based timing, progress/iteration, easing parameters, spring physics, keyframes, all 30 standard easing functions, animation orchestration (sequence, parallel, stagger, timeline)
- [x] **Motion** (40 files) — Animation composition, keyframes, timeline, easing, path motion, text animator, layer system, Lottie support, mesh warp, time remap, transitions, Camera3D, zoom levels
- [x] **Reactive** (19 files) — Interactive flags (enabled, visible, selected, etc.), progress states, focus ring, loading/selection states, semantic states (idle, loading, success, error), data states, validation states, feedback types
- [x] **Gestural** (30 files) — Pointer metrics, motion, timing (click count, hold duration), scroll, multi-touch, gesture compounds (tap, swipe, pan, pinch, rotate), drag and drop, keyboard, focus management, selection, hover patterns, context menu, vim-style key sequences, triggers
- [x] **Haptic** (4 files) — Vibration parameters, audio parameters, haptic events/patterns, impact/notification/selection feedback, iOS system patterns
- [x] **Audio** (22 files) — Level/amplitude, frequency, time/duration, stereo/spatial, synthesis (oscillators, filters, envelopes, LFOs), effects (reverb, delay, compressor, EQ, distortion, chorus, phaser, flanger, gate, limiter), analysis (waveform, spectrum, metering, pitch/BPM detection), audio effect ADT, AV sync
- [x] **Spatial** (46 files) — Position/scale, camera parameters (FOV, clipping, focal length, aperture), light parameters, PBR material parameters, vectors (Vec2-4), rotations (Euler, quaternion, axis-angle), matrices, bounds (AABB, sphere, OBB, frustum), camera types, light types, materials (StandardPBR, unlit, transparent, subsurface, cloth, hair, toon), geometry (mesh, skinned mesh, instanced, point cloud), XR (session, anchor, plane, mesh, hand, controller, hit test), scene graph
- [x] **Accessibility** (6 files) — WAI-ARIA 1.2 roles (widget, composite, structure, window), states, properties, live regions, landmarks, molecules (disclosure, selection, range, tab, dialog)
- [x] **Sensation** (8 files) — Proprioceptive atoms, contact, environment, force, temporal perception, social awareness, body/environment/social state molecules, experiential compounds (comfort, distress, flow, grounding, vigilance)
- [x] **Scheduling** (8 files) — Time-based scheduling primitives, events, recurrence, invites, RSVP
- [x] **Epistemic** (6 files) — Model-level phenomenology (coherence, confidence, valence, alignment, affect, operational state)
- [x] **Attestation** (11 files) — Cryptographic attestation primitives: SHA-256/512, Keccak-256, UUID5, Merkle trees, timestamps, signed data (ECDSA/Ed25519/RSA), W3C DIDs (key/web/ethr/ion/pkh methods, DID documents, verification methods), W3C Verifiable Credentials (credential types, proofs, status), W3C Verifiable Presentations
- [x] **Phone** (20 files) — International phone number handling, country codes, dial codes, formatting, parsing, validation, complete country database (Africa, Americas, Asia, Europe, Middle East, Oceania)
- [x] **Numeric** (4 files) — ForwardError monad, sensitivity tracking, bounded primitives, graded error propagation
- [x] **Brand** (37 files) — Identity, palette, spacing, typography, voice, mission, values, tagline, provenance, color systems, themes, Logo system, Token system (color, duration, easing, radius, shadow, size, spacing, z-index), compound types

### Runtime Targets

- [x] Basic Element type (pure data describing UI)
- [x] Event handling (msg dispatch)
- [x] **Hydrogen.Target.DOM** (450 lines) — Direct browser manipulation with diff/patch
- [x] **Hydrogen.Target.Static** (292 lines) — HTML strings for SSG
- [x] **Hydrogen.Target.Halogen** (310 lines) — Halogen adapter
- [ ] **Hydrogen.Target.Canvas** — 2D canvas rendering
- [ ] **Hydrogen.Target.WebGL** — 3D rendering (GPU/WebGPU exists, needs target wrapper)

### Layout System

- [x] **Layout/Flex.purs** (386 lines) — Flexbox layout primitives
- [x] **Layout/Constraint.purs** (167 lines) — LinTerm, Rel, LinConstraint, Formula
- [x] **Layout/Encode.purs** (152 lines) — Layout → constraint translation
- [x] **Layout/Verify.purs** (344 lines) — Satisfiability checking
- [x] **Layout/ILP/** (2429 lines total) — Integer linear programming solver
  - Problem.purs (865 lines) — ILP problem types
  - Simplex.purs (642 lines) — LP relaxation solver
  - BranchBound.purs (539 lines) — Integer solution finder
  - Formulate.purs (383 lines) — Layout → ILP translation

### Lean Proofs (95 files)

- [x] Math proofs (19 files) — Vec2/3/4, Mat3/4, quaternion, Euler, ray, plane, sphere, triangle, frustum, Box3, constraint, force, integration
- [x] Schema proofs (21 files) — Brand (10), Color (4), Numeric, Diff, Group, Priority
- [x] WorldModel proofs (12 files) — Affective, attention, consensus, consent, economy, governance, grounding, integrity, pose, rights, sensation, witness
- [x] Light proofs (6 files) — Attenuation, directional, point, shadow, spot, types
- [x] Optimize proofs (6 files) — Submodular optimization (Core, ContinuousGreedy, FAA, Matroid, RAOCO)
- [x] Material proofs (5 files) — BRDF, ISP, sparkle, layer, types
- [x] Geometry proofs (5 files) — Bounds, mesh, primitives, texture, vertex
- [x] Scene proofs (4 files) — Diff, graph, node, resource
- [x] Camera proofs (3 files) — Lens, projection, types
- [x] GPU proofs (3 files) — Diffusion kernel types
- [x] Layout proofs (2 files) — ILP, Presburger
- [x] **All `sorry` placeholders eliminated** (0 remaining)
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

### GPU/Compute (61 files)

- [x] **Diffusion.purs** — Complete diffusion kernel types for AI image generation (schedulers, noise types, guidance modes, implicit solvers, VAE encode/decode, denoising, CFG, latent blending, conditioning, presets)
- [x] **ComputeKernel.purs** — GPU compute abstractions
- [x] **WebGPU/** — Pipeline, shaders, device management
- [x] **Scene3D/** (16 files) — 3D scene management
- [x] **Text.purs, GlyphConvert.purs** — GPU text rendering

### Element Compounds (226 files)

Complete UI component library built on Schema atoms:

**Form Components:**
Input, Textarea, Select, Checkbox, Radio, Switch, Toggle, Slider, DatePicker, TimePicker, ColorPicker, NumberInput, OTPInput, PhoneInput, PasswordInput, TagInput, SearchInput, Signature, RangeSlider, FileUpload

**Display Components:**
Card, StatCard, Badge, Avatar, Alert, AlertDialog, Toast, Progress, Skeleton, Separator, Timeline, Breadcrumb, Rating, CodeBlock, ChatBubble, Tooltip, Popover, HoverCard

**Navigation Components:**
Tabs, Accordion, Stepper, Pagination, Carousel, TreeView, Navbar, Sidebar, Breadcrumb

**Layout Components:**
DataGrid, Table, Kanban, Sheet, AppShell, Container, Grid, Stack, Masonry, Split

**Special Components:**
QRCode, Confetti, CreditCard, MeshGradient, GradientEditor, Tour, Widget, Command palette

---

## Later On (Future Work)

### Schema Extensions

- [ ] Voice pillar — TTS synthesis parameters, speech recognition, formants, IPA vowels, voice character presets
- [ ] Complete SI prefix atoms (quetta through yocto for all base units)
- [ ] Rive integration (Motion pillar already has Lottie)

### Runtime Targets

- [ ] **Hydrogen.Target.Canvas** — 2D canvas rendering
- [ ] **Hydrogen.Target.WebGL** — 3D target wrapper for GPU/WebGPU
- [ ] Native targets (iOS/Android via wasm or native bindings)
- [ ] Server-side rendering with streaming

### Proofs

- [x] **All `sorry` placeholders eliminated** (completed 2026-02-27)
- [ ] Formalize interval arithmetic for floating-point precision bounds
- [ ] Prove all color conversion roundtrip properties
- [ ] Proof-carrying code generation (Lean4 → PureScript with embedded proofs)
- [ ] Replace remaining 105 axioms with constructive proofs where feasible

### Tooling

- [ ] Design token export CLI (CSS variables, Tailwind config, Figma tokens)
- [ ] Visual schema explorer / documentation generator
- [ ] Integration with sensenet//publish for scope-graph docs

### Integration

- [ ] LATTICE integration (motion graphics rendering)
- [ ] COMPASS integration (AI marketing agents)
- [ ] Brand ingestion pipeline (analyze existing assets → generate Schema tokens)
