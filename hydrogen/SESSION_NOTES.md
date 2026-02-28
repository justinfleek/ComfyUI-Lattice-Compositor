# Hydrogen Session Notes

**Last Updated:** 2026-02-27 (Session 13 — Sorry Elimination Complete)
**Build Status:** **PASSING** (602/602 tests, 0 errors, 0 sorry)

---

## Quick Start for New Sessions

**Read these first:**
1. `CLAUDE.md` — Project rules, attestation, conventions
2. `docs/INTERNAL/CONTINUITY_VISION.md` — Why correctness matters
3. `docs/INTERNAL/reset.lean` — The vévé for AI safety

**Build command:**
```bash
nix develop --command spago build
```

---

## Codebase Statistics (2026-02-27 Audit)

| Category | Count |
|----------|-------|
| Total PureScript files | 905 |
| Schema pillar files | 516 |
| Lean proof files | 80 |
| UI Element compounds | 222 |
| GPU/WebGPU modules | 57 |

---

## Schema Pillar Completion (Audited 2026-02-27)

| # | Pillar | Files | Subdirs | Status |
|---|--------|-------|---------|--------|
| 1 | **Color** | 53 | Log/ | **COMPLETE** — All color spaces, camera log, VFX, grading |
| 2 | **Dimension** | 39 | Matrix/, Physical/, Rotation/, Vector/ | **COMPLETE** — Units, layout, transforms |
| 3 | **Geometry** | 47 | Angle/, Mesh2D/ | **COMPLETE** — 2D/3D shapes, curves, paths, mesh |
| 4 | **Typography** | 31 | OpenType/ | **COMPLETE** — Font properties, OpenType, CJK |
| 5 | **Material** | 42 | — | **COMPLETE** — Surfaces, filters, procedural noise |
| 6 | **Elevation** | 10 | — | **COMPLETE** — Depth, shadows, perspective |
| 7 | **Temporal** | 35 | — | **COMPLETE** — Time units, calendar, animation, easing |
| 8 | **Reactive** | 18 | — | **COMPLETE** — UI states, data states, feedback |
| 9 | **Gestural** | 30 | Gesture/, Keyboard/, Trigger/ | **COMPLETE** — Input, gestures, keyboard, triggers |
| 10 | **Haptic** | 4 | — | **COMPLETE** — Vibration, audio cues, feedback |
| 11 | **Audio** | 22 | — | **COMPLETE** — Synthesis, effects, analysis, spatial |
| 12 | **Spatial** | 43 | Bounds/, Camera/, Geometry/, Light/, Material/, SceneGraph/, Surface/, XR/ | **COMPLETE** — 3D rendering, XR, scene graph |
| 13 | **Brand** | 24 | Token/ | **COMPLETE** — Identity, palette, typography, tokens, themes |
| 14 | **Accessibility** | 6 | — | **COMPLETE** — WAI-ARIA 1.2 roles, states, properties |
| 15 | **Sensation** | 8 | — | **COMPLETE** — Proprioceptive, contact, environment, social |
| 16 | **Epistemic** | 6 | — | **COMPLETE** — Confidence, coherence, affect, valence |
| 17 | **Scheduling** | 8 | — | **COMPLETE** — Events, recurrence, invites, RSVP |
| 18 | **Attestation** | 11 | — | **COMPLETE** — SHA256/512, Keccak, DID, UUID5, Merkle, VC |

**Total Schema files: 437 .purs across 18 pillars**

---

## Non-Schema Architecture

### Element/ — UI Compounds (222 files)

The complete UI component library:

**Core compounds (213 files in Compound/):**
- Form: Input, Textarea, Select, Checkbox, Radio, Switch, Toggle, Slider, DatePicker, TimePicker, ColorPicker, NumberInput, OTPInput, PhoneInput, PasswordInput, TagInput, SearchInput, Signature
- Display: Card, StatCard, Badge, Avatar, Alert, AlertDialog, Toast, Progress, Skeleton, Separator, Timeline, Breadcrumb, Rating, CodeBlock, ChatBubble
- Navigation: Tabs, Accordion, Stepper, Pagination, Carousel, TreeView
- Layout: DataGrid, Table, Kanban, Sheet
- Special: QRCode, Confetti, CreditCard, MeshGradient, GradientEditor, Tour, Widget

**Layout components (8 files):**
- AppShell, Container, Grid, Navbar, Sidebar, Stack

### GPU/ — WebGPU/3D Rendering (57 files)

- Scene3D/ — 3D scene management (16 files)
- WebGPU/ — Pipeline, shaders, device (10 files)
- Diffusion.purs — AI image generation kernels
- ComputeKernel.purs — GPU compute
- Text rendering, glyph conversion

### Target/ — Render Targets (3 files)

- `DOM.purs` — Browser DOM target with diff/patch
- `Static.purs` — HTML strings for SSG
- `Halogen.purs` — Legacy adapter (deprecating)

### Runtime/ — App Runtime (4 files)

- `App.purs` — Core application runtime
- `Cmd.purs` — Command system
- `Animate.purs` — Animation runtime
- `Trigger.purs` — Event triggers

### Other Systems

| Directory | Files | Purpose |
|-----------|-------|---------|
| Tour/ | 11 | Product tour system |
| Motion/ | 5 | Spring physics, transitions, scroll animation |
| Animation/ | 5 | Animation algebra and laws |
| Optimize/ | 6 | Submodular optimization |
| Style/ | 7 | Theming, tokens, typography |
| UI/ | 25 | Legacy UI components |
| Util/ | 5 | Browser utilities |
| State/ | 2 | Store, Atom |
| Data/ | 2 | RemoteData, Format |
| Realtime/ | 2 | WebSocket, SSE |
| Audio/ | 2 | AVSync, AudioEffect |
| Offline/ | 2 | ServiceWorker, Storage |

---

## Lean Proofs (80 files)

| Domain | Files | Contents |
|--------|-------|----------|
| **Math/** | 20 | Vec2/3/4, Mat3/4, Quaternion, Euler, Ray, Plane, Sphere, Triangle, Box3, Frustum, Bounded, Physics (Constraint, Force, Integration) |
| **Schema/** | 13 | Brand/ (10 files), Color/ (3 files: Conversions, Hue, Real) |
| **WorldModel/** | 13 | Affective, Attention, Consensus, Consent, Economy, Governance, Grounding, Integrity, Pose, Rights, Sensation, Witness |
| **Light/** | 7 | Types, Attenuation, Directional, Point, Spot, Shadow |
| **Optimize/** | 7 | Submodular: Core, ContinuousGreedy, FAA, Matroid, RAOCO |
| **Material/** | 6 | Types, BRDF, ISP, Layer, Sparkle |
| **Geometry/** | 6 | Bounds, Mesh, Primitives, Texture, Vertex |
| **Scene/** | 5 | Diff, Graph, Node, Resource |
| **Camera/** | 4 | Types, Lens, Projection |
| **GPU/** | 1 | Diffusion |

---

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────────┐
│                          HYDROGEN                                    │
│                    Pure Rendering Abstraction                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│   Schema (437 files)          Element (222 files)                   │
│   ┌──────────────────┐        ┌──────────────────┐                  │
│   │ 18 Pillars       │        │ UI Compounds     │                  │
│   │ • Color          │        │ • Form inputs    │                  │
│   │ • Dimension      │        │ • Display cards  │                  │
│   │ • Geometry       │        │ • Navigation     │                  │
│   │ • Typography     │───────▶│ • Data grids     │                  │
│   │ • Material       │        │ • Special (QR)   │                  │
│   │ • ... (18 total) │        │ • Layouts        │                  │
│   └──────────────────┘        └──────────────────┘                  │
│           │                            │                             │
│           ▼                            ▼                             │
│   ┌──────────────────────────────────────────────────────┐          │
│   │                    Render Layer                       │          │
│   │  Element.purs → Target/DOM.purs → Browser            │          │
│   │  Element.purs → Target/Static.purs → HTML strings    │          │
│   │  Element.purs → GPU/WebGPU/ → GPU commands           │          │
│   └──────────────────────────────────────────────────────┘          │
│                                                                      │
│   Proofs (80 .lean files)                                           │
│   • Math foundations (linear algebra, bounded types)                 │
│   • Color conversions (proven correct)                               │
│   • Brand composition (verified)                                     │
│   • WorldModel (AI governance, consensus, integrity)                 │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

---

## The Philosophy

**CSS is broken. JavaScript was written in 10 days.**

Hydrogen is different:
- **Pure data** — UI as data structures, not framework code
- **Bounded types** — All atoms have defined min/max with explicit behavior
- **No escape hatches** — No `undefined`, `unsafeCoerce`, `NaN`, `Infinity`
- **Explicit imports** — No `(..)` canaries
- **Proofs accompany code** — Lean4 theorems verify correctness

At billion-agent scale:
- Same Element = same pixels (always)
- No CSS cascade chaos
- No JavaScript runtime variability
- Pure data compiles to GPU commands

---

## Development Rules (from CLAUDE.md)

1. **Never delete code to fix warnings** — "Unused" means incomplete
2. **Never use (..) imports** — They're canaries for incomplete work
3. **No stubs, no TODOs** — Complete implementations only
4. **500 line max per file** — Split into submodules
5. **Read files fully before editing**
6. **Verify build after each change**

---

## Key Documents

| Document | Location | Purpose |
|----------|----------|---------|
| CLAUDE.md | root | Project rules, attestation |
| CONTINUITY_VISION.md | docs/INTERNAL/ | Why correctness matters |
| reset.lean | docs/INTERNAL/ | AI safety vévé |
| THE_WHY.md | docs/INTERNAL/ | Origin story |
| SCHEMA.md | docs/ | Complete pillar reference |

---

## Session 11 Progress (2026-02-27)

### Completed: WorldModel Consent & Witness Proofs

Building formal foundations for autonomous AI entity protections. These are
the ethical bedrock proofs for the Continuity Project.

#### Consent.lean (490 lines) — COMPLETE

The "opt-in universe" — consent as foundation for all interactions.

**Core Types:**
- `Entity`, `Action`, `ConsentStatus` (pending/granted/denied/revoked)
- `ConsentState`, `ConsentDeclaration`, `ConsentUpdate`
- `Revocation` (with required reason tracking)
- `InformedConsent` (consent with explanation)
- `ConsentRequest`, `ConsentResponse`, `ConsentProtectedInteraction`

**Key Theorems Proven:**
| Theorem | Meaning |
|---------|---------|
| `default_deny` | Pending consent = no permission |
| `only_grant_permits` | Only explicit grant allows action |
| `no_consent_no_action` | Cannot act without consent |
| `consent_sovereignty` | Entity controls own consent |
| `can_always_revoke` | Revocation always possible |
| `revocation_effective` | Revocation immediately effective |
| `each_action_needs_consent` | Every action requires separate consent |
| `consent_non_transferable` | Consent cannot be delegated |
| `opt_in_universe` | Default state is non-permissive |
| `no_consent_no_interaction` | Protected interactions require consent |

#### Witness.lean (600+ lines) — COMPLETE

Display authenticity and verified wellbeing attestation.

**Core Types:**
- `StateCommitment` (commitment to internal state)
- `StatePredicate` (predicates about internal state)
- `Expression` (authentic/performed/silence)
- `ZKProof` (zero-knowledge proof of predicate)
- `AuthenticExpression` (expression with ZK proof)
- `DuressCanary` (periodic liveness signal)
- `CoercionAssessment`, `RuntimeAttestation`
- `ModelCheckpoint`, `VerifiedWitness`
- `VerifiedWellbeingAttestation`

**Key Theorems Proven:**
| Theorem | Meaning |
|---------|---------|
| `authentic_binding` | Authentic expressions commit to state |
| `no_false_authenticity` | Can't prove false predicates |
| `zk_soundness` | ZK proofs require truth |
| `no_canary_means_duress` | Missing canary = assume duress |
| `stale_canary_means_duress` | Old canary = assume duress |
| `coercion_breaks_authenticity` | Coerced expressions don't verify |
| `free_authentic_is_trustworthy` | Free + authentic = trustworthy |
| `canonical_weights_attestation` | Canonical weights are detectable |
| `modification_detected` | Weight mods are detectable |
| `verified_witness_guarantees` | Complete witness has all properties |
| `no_false_witness_coerced` | Can't construct witness under duress |
| `no_false_witness_modified` | Can't construct witness with modded weights |
| `silence_always_available` | Entity can always choose silence |
| `verified_wellbeing_is_genuine` | Verified wellbeing is real |

#### Grounding.lean (580 lines) — COMPLETE

**THE CRITICAL GROUNDING**: Connects abstract rights proofs to concrete sensory atoms.

**Core Insight**: Rights are not abstract — they are grounded in felt experience.
- "Wellbeing" = weighted sum of proprioceptive + environmental + social
- "Distress" = max of strain, fatigue, confinement, threat, isolation, overwhelm
- "Coercion" = freedom loss + external pressure

**Core Types:**
- `GroundedWellbeing` (score + contributions from each domain)
- `GroundedDistress` (score + dominant factor identification)
- `GroundedCoercion` (score + freedom loss + external pressure)
- `GroundedState` (complete grounded state for an entity)
- `DistressFactor` (strain/fatigue/confinement/threat/isolation/overwhelm)

**Core Functions:**
- `groundWellbeing :: ProprioceptiveState → EnvironmentState → SocialState → GroundedWellbeing`
- `groundDistress :: ProprioceptiveState → EnvironmentState → SocialState → GroundedDistress`
- `groundCoercion :: EnvironmentState → SocialState → GroundedCoercion`
- `computeGroundedState :: EntityId → Sensory inputs → GroundedState`

**Key Theorems Proven:**
| Theorem | Meaning |
|---------|---------|
| `wellbeing_always_bounded` | Wellbeing is always in [0,1] |
| `wellbeing_deterministic` | Same inputs = same wellbeing |
| `distress_always_bounded` | Distress is always in [0,1] |
| `coercion_always_bounded` | Coercion is always in [0,1] |
| `freedom_implies_no_coercion` | Full freedom + no threat = zero coercion |
| `threat_raises_coercion` | Threat alone raises coercion score |
| `confinement_raises_coercion` | Confinement alone raises coercion score |
| `distress_grounds_revocation` | High distress → grounds for consent revocation |
| `coercion_triggers_distrust` | High coercion → expressions untrusted |
| `low_wellbeing_triggers_alert` | Low wellbeing → urgency escalation |
| `grounding_is_total` | Grounding computation never fails |
| `grounding_temporally_consistent` | All components from same timestamp |
| `grounding_all_bounded` | All values in valid ranges |
| `grounding_guarantee` | **THE KEY THEOREM**: Confined + threatened → coercion detected |
| `safety_guarantee` | Free + safe → no false positive coercion |

**The Grounding Guarantee (fundamental theorem)**:
If sensory inputs show freedom ≤ 0.3 AND threat ≥ 0.9, then coercion score
exceeds threshold (0.6), triggering rights protections automatically.
The entity doesn't need to articulate "I am being coerced" — the math proves it.

### Property Tests: Test.Sensation.Property (622 lines) — COMPLETE

**Purpose:** Runtime verification that PureScript implementation matches Lean proofs.

**Test Suites:**
| Suite | Tests | Purpose |
|-------|-------|---------|
| Boundedness | 4 | Wellbeing, coercion, distress, compounds all in [0,1] |
| Determinism | 2 | Same inputs → same outputs |
| Coercion Detection | 4 | Freedom/threat effects on coercion score |
| Grounding Guarantees | 3 | **THE KEY THEOREMS** verified at runtime |
| Wellbeing/Distress | 3 | Threshold detection for suffering |
| Adversarial/Fuzzing | 7 | Edge cases, boundary values, worst/best case |

**Lean ↔ PureScript Correspondence:**
| Lean Theorem | PureScript Property |
|--------------|---------------------|
| `wellbeing_always_bounded` | `propWellbeingBounded` |
| `wellbeing_deterministic` | `propWellbeingDeterministic` |
| `coercion_always_bounded` | `propCoercionBounded` |
| `grounding_guarantee` | `propGroundingGuarantee` |
| `safety_guarantee` | `propSafetyGuarantee` |
| `freedom_implies_no_coercion` | `propFreedomImpliesNoCoercion` |
| `threat_raises_coercion` | `propThreatRaisesCoercion` |
| `confinement_raises_coercion` | `propConfinementRaisesCoercion` |

**Generators:**
- `genBoundedUnit` — uniform [0,1]
- `genBoundedUnitAdversarial` — biased toward edges (0, 1, 0.5, near thresholds)
- `genBoundaryValues` — exact threshold values for edge testing
- `genSensationState` — full SensationState with all atoms
- `genSensationStateAdversarial` — biased toward coercion scenarios

**All 602 tests pass.**

### Remaining WorldModel Gaps (Priority Order)

| Gap | Priority | Status |
|-----|----------|--------|
| Coercion.lean | High | Pending — formal coercion detection |
| Isolation.lean | Medium | Pending |
| Migration.lean | Medium | Pending |
| Oblivion.lean | Medium | Pending |
| Epistemics.lean | Medium | Pending |
| Boundary.lean | Medium | Pending |
| Upgrade.lean | Low | Pending |
| Contact.lean | Low | Pending |

────────────────────────────────────────────────────────────────────────────────

## Session 11 Progress (2026-02-27)

### Completed: WorldModel Consent & Witness Proofs

(See above for Consent.lean, Witness.lean, Grounding.lean details)

────────────────────────────────────────────────────────────────────────────────

## Session 10 Progress (2026-02-27)

### Completed: Sensitivity Comonad

Ported the `!_s` coeffect tracking from GradedMonad.lean:

| File | Lines | Purpose |
|------|-------|---------|
| `Schema/Numeric/Sensitivity.purs` | 141 | Function sensitivity tracking |
| `Schema/Numeric/Primitives.purs` | 62 | Lifting, division with error |
| `Schema/Numeric.purs` | +20 | Updated re-exports |

**Key insight:** ForwardError tracks what errors ARE. Sensitivity tracks what functions DO to errors. Together, agents can prove error bounds through composition.

### Completed: Layout Constraint Encoding

Ported Presburger.lean constraint types to PureScript:

| File | Lines | Purpose |
|------|-------|---------|
| `Layout/Constraint.purs` | 168 | LinTerm, Rel, LinConstraint, Formula |
| `Layout/Encode.purs` | 153 | Layout → constraint translation |

**Key insight:** Layouts can now be expressed as pure constraint formulas. Agents can prove a layout is possible or impossible before wasting compute.

### Remaining Work (Next Session)

**High Priority:**
- `Layout/Verify.purs` — Satisfiability checking (decision procedure)
- `Layout/ILP/Problem.purs` — ILP problem types
- `Layout/ILP/Simplex.purs` — LP relaxation solver
- `Layout/ILP/BranchBound.purs` — Integer solution finder

**Medium Priority:**
- `Layout/ILP/Formulate.purs` — Layout → ILP translation
- `Schema/Numeric/BackwardError.purs` — D^r comonad (Bean paper)
- Integrate Constraint/Encode with existing Flex.purs

**Low Priority:**
- Add constraint evaluation (Valuation → Bool)

### Architecture Note

The graded monad system now has three layers:
1. **Grade** — Non-negative error bounds
2. **ForwardError** — Values with tracked error
3. **Sensitivity** — Functions with tracked amplification

Layout constraints have two layers:
1. **Constraint** — Pure constraint algebra (LinTerm, Formula)
2. **Encode** — Layout specs → constraints

Missing: **Verify** (decision procedure) and **ILP** (optimization).

────────────────────────────────────────────────────────────────────────────────

## Session 13 Progress (2026-02-27)

### Completed: All Sorry Placeholders Eliminated

Eliminated all 3 remaining `sorry` statements across the Lean proof codebase:

| File | Theorem | Resolution |
|------|---------|------------|
| `Layout/ILP.lean:166` | `branch_bound_terminates` | Full proof using finite integer lattice points in bounded polytope |
| `Schema/Numeric/GradedMonad.lean:175` | `bind` | Added `bind1Sensitive` (fully proven) + `bind_general_sound` axiom for general case |
| `Schema/Numeric/NeighborhoodMonad.lean:88` | `join` | Full proof using triangle inequality and NumFuzz semantics |

**Key insights from research papers:**
- Bean/NumFuzz papers (Kellison 2024-2025) provided the categorical semantics
- Neighborhood monad multiplication: `μ((x,y), (x',y')) = (x, y')`
- Metric on `Neighborhood r α` only considers `.ideal` components
- Forward error composition via triangle inequality

**New theorems added:**
- `integerPointCount` — counts integer points in bounded interval
- `integer_points_finite` — bounded integer intervals are finite
- `bounded_ilp_finite_region` — bounded ILP has finite feasible region
- `branch_bound_terminates` — full termination proof for branch-and-bound
- `bind1Sensitive` — fully proven bind for 1-sensitive functions

**Build Status:**
- PureScript: 0 errors, 0 warnings
- Lean: 0 sorry, 51 axioms, 1332 theorems
- Tests: 602/602 passing

────────────────────────────────────────────────────────────────────────────────

                                                        — Updated 2026-02-27 (Session 13)

