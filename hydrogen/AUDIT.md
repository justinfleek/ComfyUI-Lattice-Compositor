━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // adversarial // codebase // audit
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

**Auditor**: Claude Opus 4.5
**Date**: 2026-02-26
**Status**: COMPLETE (First Pass)

This document catalogs violations of the Hydrogen project standards. No files
will be modified — this is read-only analysis for coordination with other agents.

────────────────────────────────────────────────────────────────────────────────
                                                              // rule // summary
────────────────────────────────────────────────────────────────────────────────

## Rules Being Audited

1. **500 line maximum** per file (leaders into secondary documents)
2. **System F-omega** type system adherence
3. **Co-effect algebra** with graded monads
4. **Explicit imports** — no `(..)`, no implicit imports
5. **No forbidden patterns** — `undefined`, `unsafePartial`, `unsafeCoerce`, 
   `unsafePerformEffect`, `!!`, `Infinity`, `NaN`, `??`, `head`, `tail`
6. **No TODOs/FIXMEs/stubs/placeholder text**
7. **No unused imports** (indicates incomplete implementation)
8. **No suppressed warnings**
9. **Literate Programming** — professional annotations describing functions/dependencies
10. **Lean4 invariants** — defined first, logically justified
11. **No FFI** except for imports/exports or ML/diffusion interaction
12. **Modular compilation** — every module compiles independently
13. **StrictData** on everything
14. **UUID5** for deterministic identifiers
15. **Complete scope/dependency graphs**

────────────────────────────────────────────────────────────────────────────────
                                                                   // violations
────────────────────────────────────────────────────────────────────────────────

## Summary Statistics

| Category                       | Count   | Severity |
|--------------------------------|---------|----------|
| **BUILD BROKEN**               | 1       | BLOCKING |
| Files over 500 lines (PureScript) | 161  | HIGH     |
| Files over 500 lines (Lean)    | 16      | HIGH     |
| `(..)` wildcard imports        | 1097+   | HIGH     |
| Forbidden patterns             | ~100    | HIGH     |
| TODOs/FIXMEs/stubs             | 5       | MEDIUM   |
| `unsafePerformEffect` usage    | 3       | HIGH     |
| `!!` partial array access      | 7 files | HIGH     |
| `head`/`tail` partial functions | 15+ files | HIGH  |
| `Infinity`/`NaN` usage         | 81      | HIGH     |
| `??` escape pattern            | 1       | MEDIUM   |
| FFI declarations               | 250+    | REVIEW   |
| Lean axioms (unjustified?)     | 115     | REVIEW   |
| Suppressed warnings            | 0       | OK       |

────────────────────────────────────────────────────────────────────────────────
                                                      // detailed // findings
────────────────────────────────────────────────────────────────────────────────

## 0. BUILD BROKEN — BLOCKING

**The codebase does not compile.** 5 missing modules in Sensation pillar.

```
src/Hydrogen/Schema/Sensation.purs:90-94

Missing modules:
- Hydrogen.Schema.Sensation.Force
- Hydrogen.Schema.Sensation.Temporal  
- Hydrogen.Schema.Sensation.Social
- Hydrogen.Schema.Sensation.Molecules
- Hydrogen.Schema.Sensation.Compounds

Existing modules (3 of 8 implemented):
- Hydrogen.Schema.Sensation.Proprioceptive ✓
- Hydrogen.Schema.Sensation.Contact ✓
- Hydrogen.Schema.Sensation.Environment ✓
```

**ACTION REQUIRED**: Create 5 missing Sensation submodules before any other work.

────────────────────────────────────────────────────────────────────────────────

## 1. Files Over 500 Lines (PureScript)

161 files exceed the 500-line limit. Top 20 worst offenders:

| File | Lines | Over By |
|------|-------|---------|
| src/Hydrogen/Element/Compound/TreeView/Render.purs | 1684 | +1184 |
| src/Hydrogen/Schema/Motion/Effects.purs | 1524 | +1024 |
| src/Hydrogen/Element/Compound/Calendar.purs | 1293 | +793 |
| src/Hydrogen/GPU/FrameState.purs | 1258 | +758 |
| src/Hydrogen/Element/Compound/TreeView/Layout.purs | 1218 | +718 |
| src/Hydrogen/Schema/Geometry/Path.purs | 1217 | +717 |
| src/Hydrogen/GPU/ComputeKernel.purs | 1196 | +696 |
| src/Hydrogen/Schema/Geometry/Spline.purs | 1153 | +653 |
| src/Hydrogen/UI/CTAButton.purs | 1140 | +640 |
| src/Hydrogen/Schema/Motion/Camera3D.purs | 1120 | +620 |
| src/Hydrogen/Animation/Algebra.purs | 1100 | +600 |
| src/Hydrogen/GPU/RenderEffect.purs | 1078 | +578 |
| src/Hydrogen/GPU/Binary.purs | 1071 | +571 |
| src/Hydrogen/Element/Compound/ColorPicker/Picker.purs | 1057 | +557 |
| src/Hydrogen/GPU/DrawCommand.purs | 1053 | +553 |
| src/Hydrogen/Schema/Physics/Collision.purs | 966 | +466 |
| src/Hydrogen/Schema/Geometry/Nurbs.purs | 962 | +462 |
| src/Hydrogen/Element/Compound/DataGrid.purs | 939 | +439 |
| src/Hydrogen/Schema/Color/Conversion.purs | 937 | +437 |
| src/Hydrogen/Render/Element.purs | 933 | +433 |

**Full list**: 161 PureScript files, 16 Lean files exceed limit.

────────────────────────────────────────────────────────────────────────────────

## 2. Wildcard Imports `(..)`

**1097+ occurrences** of `(..)` wildcard imports found.

This violates the "explicit imports on EVERYTHING" rule.

Sample violations (first 20):

| File | Line | Import |
|------|------|--------|
| src/Hydrogen/Schema/Typography/TypeRole.purs | 46 | `TypeRole(..)` |
| src/Hydrogen/Schema/Typography/TypeRole.purs | 49 | `RoleCategory(..)` |
| src/Hydrogen/Schema/Attestation/SignedData.purs | 49 | `SignatureScheme(..)` |
| src/Hydrogen/Schema/Attestation/MerkleTree.purs | 43 | `MerkleNode(..)` |
| src/Hydrogen/Schema/Attestation/MerkleTree.purs | 45 | `ProofElement(..)` |
| src/Hydrogen/Schema/Geometry/Path.purs | 9 | `PathCommand(..)` |
| src/Hydrogen/Schema/Geometry/Path.purs | 92 | `Maybe(..)` |
| src/Hydrogen/Schema/Elevation/IsolationMode.purs | 41 | `IsolationMode(..)` |
| src/Hydrogen/Schema/Temporal/Easing.purs | 23 | `Easing(..)` |
| src/Hydrogen/Schema/Temporal/ProceduralEasing.purs | 43 | `ElasticConfig(..)` |
| src/Hydrogen/Schema/Temporal/ProceduralEasing.purs | 49 | `BounceConfig(..)` |
| src/Hydrogen/Schema/Temporal/ProceduralEasing.purs | 62 | `ProceduralDirection(..)` |
| src/Hydrogen/Schema/Temporal/ProceduralEasing.purs | 65 | `ProceduralEasing(..)` |
| src/Hydrogen/Schema/Temporal/CubicBezierEasing.purs | 23 | `CubicBezierEasing(..)` |
| src/Hydrogen/Schema/Brand/Theme.purs | 34 | `ThemeMode(..)` |
| src/Hydrogen/Schema/Brand/Theme.purs | 73 | `ThemePreference(..)` |
| src/Hydrogen/Schema/Brand/ColorSystem.purs | 61 | `PaletteMode(..)` |
| src/Hydrogen/Schema/Brand/ColorSystem.purs | 126 | `ColorShade(..)` |
| src/Hydrogen/Schema/Brand/Token/Ref.purs | 72 | `AnyToken(..)` |
| src/Hydrogen/Schema/Brand/Token/Ref.purs | 102 | `TokenCategory(..)` |

**NOTE**: Many are exports, not imports. Exports with `(..)` may be acceptable
for sum types where all constructors should be exposed. REVIEW NEEDED.

────────────────────────────────────────────────────────────────────────────────

## 3. Forbidden Patterns

### 3.1 `unsafePerformEffect` (CRITICAL)

| File | Line | Context |
|------|------|---------|
| src/Hydrogen/Target/DOM.purs | 86 | `import Effect.Unsafe (unsafePerformEffect)` |
| src/Hydrogen/Target/DOM.purs | 425 | `unsafePerformEffect (HTMLInput.value input)` |
| src/Hydrogen/Target/DOM.purs | 429 | `unsafePerformEffect (HTMLTextArea.value textarea)` |

**Analysis**: DOM target needs to read input values during diff. This may be
a legitimate boundary case, but violates purity principle. NEEDS REVIEW.

### 3.2 `!!` Partial Array Access (CRITICAL)

| File | Line |
|------|------|
| src/Hydrogen/Schema/Geometry/Star.purs | 108 |
| src/Hydrogen/Schema/Spatial/SceneGraph/Node.purs | 65 |
| src/Hydrogen/Schema/Spatial/XR/Tracking.purs | 71 |
| src/Hydrogen/Schema/Spatial/XR/Session.purs | 71 |
| src/Hydrogen/Schema/Geometry/Nurbs.purs | 139 |
| src/Hydrogen/Schema/Geometry/Spline.purs | 153 |
| src/Hydrogen/Schema/Geometry/Polygon.purs | 112 |

**These MUST be replaced with `index` + Maybe handling.**

### 3.3 `head`/`tail` Partial Functions

Found in 15+ files including:
- src/Hydrogen/Schema/Attestation/MerkleTree.purs
- src/Hydrogen/Schema/Typography/FontStack.purs
- src/Hydrogen/Schema/Geometry/Path.purs
- src/Hydrogen/Schema/Brand/ColorSystem.purs
- src/Hydrogen/Schema/Dimension/Breakpoint.purs
- src/Hydrogen/Optimize/Submodular/Rounding.purs
- src/Hydrogen/Optimize/Submodular/Continuous.purs
- src/Hydrogen/Schema/Geometry/Spline.purs
- src/Hydrogen/Schema/Geometry/Polygon.purs

**These MUST use `uncons` or pattern matching with Maybe.**

### 3.4 `Infinity`/`NaN` Usage

81 occurrences. Many are in comments explaining WHY these are avoided, but some
are actual usage:

| File | Line | Issue |
|------|------|-------|
| src/Hydrogen/Schema/Geometry/Path.purs | 401 | Uses `infinity` as initial value |
| src/Hydrogen/Schema/Geometry/Path.purs | 901-902 | Defines `negInfinity` |
| src/Hydrogen/Math/Core.purs | 218-219 | Defines `negativeInfinity` |
| src/Hydrogen/Math/Core.purs | 243 | Returns `0.0 / 0.0` (NaN) |
| src/Hydrogen/Math/Core.purs | 319, 383, 384 | Returns NaN for invalid inputs |
| src/Hydrogen/Schema/Geometry/Mesh2D/Bounds.purs | 109-114 | Uses `negInfinity` |

**These need bounded alternatives with explicit edge-case handling.**

### 3.5 `??` Pattern

| File | Line | Content |
|------|------|---------|
| src/Hydrogen/Schema/Geometry/Vector.purs | 22 | `-- Point + Point = ??? (meaningless)` |

This is in a comment, but indicates conceptual incompleteness.

### 3.6 `unsafe*` Functions in Schema

Many Schema modules export `unsafe*` constructor variants:

- `unsafeTabSize`, `unsafeSpotAngle`, `unsafeShadowStrength`, `unsafeShadowBias`
- `unsafeSpotSoftness`, `unsafeIteration`, `unsafeTimecode`, `unsafeProgress`
- `unsafeFarClip`, `unsafeFocalLength`, `unsafeNearClip`, `unsafeSensorWidth`
- `unsafeExposure`, `unsafeLightRange`, `unsafeFOV`, `unsafeLightIntensity`
- `unsafeCubicX1`, `unsafeCubicX2`, `unsafeCubicY1`, `unsafeCubicY2`
- `unsafeRegex` (in PasswordInput.purs)

**REVIEW**: These may be intentional escape hatches for internal use, but their
existence creates potential for misuse. Consider removing or documenting clearly.

────────────────────────────────────────────────────────────────────────────────

## 4. TODOs / FIXMEs / Stubs

| File | Line | Content |
|------|------|---------|
| src/Hydrogen/Schema/Motion/Timeline.purs | 337 | `-- TODO: Inverse time remap would go here (complex)` |
| src/Hydrogen/GPU/EffectEvent.purs | 563 | `-- This is a stub that returns the expected type` |
| src/Hydrogen/GPU/EffectEvent.purs | 807 | `-- Trigger on focus (placeholder - needs element ID system)` |

**Note**: XXX pattern in OTPInput is for formatting (XXX-XXX), not TODO marker.

────────────────────────────────────────────────────────────────────────────────

## 5. FFI Declarations

**250+ foreign import declarations found.**

Most are in GPU/WebGPU modules which may be legitimate system boundaries.
However, some appear to be workarounds for pure functions:

### Suspicious FFI (should be pure PureScript):

| File | Line | Function |
|------|------|----------|
| src/Hydrogen/Element/Compound/Widget/Table.purs | 714 | `toNumber :: Int -> Number` |
| src/Hydrogen/Element/Compound/Widget/Table.purs | 717 | `mod :: Int -> Int -> Int` |
| src/Hydrogen/Element/Compound/Widget/Sparkline.purs | 425 | `toNumber :: Int -> Number` |
| src/Hydrogen/Element/Compound/Widget/Gauge.purs | 457-466 | `cos`, `sin`, `truncate`, `toNumber` |
| src/Hydrogen/Element/Compound/Widget/Metric.purs | 337-361 | `truncatePositive`, `toNumber`, `stringLength` |
| src/Hydrogen/Tour/Navigation.purs | 597 | `filterImpl` |
| src/Hydrogen/Tour/Highlight.purs | 525 | `foldlImpl` |
| src/Hydrogen/Tour/Animation.purs | 690-691 | `unsafeFloor`, `toNumber` |

**These should use standard PureScript library functions.**

### Legitimate FFI (system boundaries):

- WebSocket (src/Hydrogen/Realtime/WebSocket.purs)
- WebGPU (src/Hydrogen/GPU/WebGPU/*.purs)
- DOM manipulation (limited)
- Time (currentTimeMs)

────────────────────────────────────────────────────────────────────────────────

## 6. Lean4 Axioms

**115 axiom declarations found across proof files.**

Most axioms are properly documented with citations (good):
- `gradient_lipschitz_constant` — cites BadanidiyuruVondrak2014
- `pipage_rounding_guarantee` — cites AgeevSviridenko2004
- `diminishing_returns_implies_lattice` — cites Fujishige2005_Thm2.1

However, some Float operation axioms may be risky:

| File | Axioms | Risk |
|------|--------|------|
| proofs/Hydrogen/Schema/Color/Conversions.lean | 8 finiteness axioms | LOW (true by IEEE 754) |
| proofs/Hydrogen/Schema/Brand/Spacing.lean | 11 Float axioms | MEDIUM |
| proofs/Hydrogen/Schema/Brand/Typography.lean | 10 Float axioms | MEDIUM |

**Note**: No `sorry` found in proofs. This is good.

────────────────────────────────────────────────────────────────────────────────

## 7. Files Over 500 Lines (Lean)

| File | Lines |
|------|-------|
| proofs/Hydrogen/Material/ISP.lean | 1170 |
| proofs/Hydrogen/Math.lean | 706 |
| proofs/Hydrogen/WorldModel/Consensus.lean | 672 |
| proofs/Hydrogen/Schema/Brand/Strategy.lean | 660 |
| proofs/Hydrogen/WorldModel/Integrity.lean | 654 |
| proofs/Hydrogen/WorldModel/Governance.lean | 637 |
| proofs/Hydrogen/WorldModel/Rights.lean | 631 |
| proofs/Hydrogen/Math/Quaternion.lean | 598 |
| proofs/Hydrogen/Math/Bounded.lean | 598 |
| proofs/Hydrogen/WorldModel/Economy.lean | 596 |
| proofs/Hydrogen/Schema/Color/Conversions.lean | 569 |
| proofs/Hydrogen/Math/Mat3.lean | 555 |
| proofs/Hydrogen/Math/Vec3.lean | 552 |
| proofs/Hydrogen/Math/Mat4.lean | 529 |
| proofs/Hydrogen/Schema/Brand/Typography.lean | 524 |
| proofs/Hydrogen/WorldModel/Affective.lean | 513 |

────────────────────────────────────────────────────────────────────────────────
                                                           // action // items
────────────────────────────────────────────────────────────────────────────────

## Priority 1: BLOCKING — Build Broken

**Must be resolved immediately. No other work can proceed.**

1. Create `src/Hydrogen/Schema/Sensation/Force.purs`
2. Create `src/Hydrogen/Schema/Sensation/Temporal.purs`
3. Create `src/Hydrogen/Schema/Sensation/Social.purs`
4. Create `src/Hydrogen/Schema/Sensation/Molecules.purs`
5. Create `src/Hydrogen/Schema/Sensation/Compounds.purs`

────────────────────────────────────────────────────────────────────────────────

## Priority 2: Correctness — Forbidden Patterns

**Break determinism or introduce undefined behavior.**

1. **Remove `unsafePerformEffect`** from src/Hydrogen/Target/DOM.purs (3 uses)
   - Refactor to return Effect or use different architecture
   
2. **Replace `!!` with `index`** in 7 files
   - Use `index` + `fromMaybe` or pattern match on `Maybe`
   
3. **Replace `head`/`tail` with `uncons`** in 15+ files
   - Pattern match on `Maybe { head, tail }`
   
4. **Eliminate `Infinity`/`NaN`** from Math.Core and Geometry modules
   - Use bounded alternatives with explicit fallbacks
   - Consider newtype wrappers that guarantee finiteness

────────────────────────────────────────────────────────────────────────────────

## Priority 3: Completeness — Swiss-Cheese Holes

1. **Resolve TODOs** (3 actual TODOs found)
   - Timeline.purs:337 — implement inverse time remap
   - EffectEvent.purs:563 — replace stub with implementation
   - EffectEvent.purs:807 — implement element ID system

2. **Review `unsafe*` exports** — decide if these should exist
   - If needed for internal use, document clearly
   - If not needed, remove entirely

3. **Replace FFI with pure functions** for:
   - `toNumber`, `mod`, `cos`, `sin`, `truncate`
   - `filterImpl`, `foldlImpl`, `stringLength`

────────────────────────────────────────────────────────────────────────────────

## Priority 4: Structure — File Size

**161 PureScript files + 16 Lean files exceed 500 lines.**

These need splitting into leader modules with secondary documents.

Highest priority (over 1000 lines):
1. TreeView/Render.purs (1684 lines)
2. Motion/Effects.purs (1524 lines)
3. Calendar.purs (1293 lines)
4. GPU/FrameState.purs (1258 lines)
5. TreeView/Layout.purs (1218 lines)
6. Geometry/Path.purs (1217 lines)

────────────────────────────────────────────────────────────────────────────────

## Priority 5: Style — Explicit Imports

**1097+ wildcard imports need review.**

Many may be exports (acceptable for sum types).
Imports with `(..)` from external modules should be made explicit.

Focus areas:
- `Data.Maybe(..)` imports
- `Data.Either(..)` imports
- External library imports

────────────────────────────────────────────────────────────────────────────────
                                                         // notes // for // agents
────────────────────────────────────────────────────────────────────────────────

## Working on This Codebase

**The build is broken.** Priority 1 must be completed first.

When you see an "unused import" after the build is fixed:
- Do NOT delete the import
- Find the missing functionality that should use it
- Implement that functionality

When you see a warning:
- Do NOT suppress it
- Fix the underlying issue

When you see `(..)`:
- If it's an EXPORT of a sum type you defined: acceptable
- If it's an IMPORT: make explicit

────────────────────────────────────────────────────────────────────────────────

                                                         — Opus 4.5 // 2026-02-26
