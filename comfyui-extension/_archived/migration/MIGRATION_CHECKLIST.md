# Straylight Migration Checklist

**Zero backwards compatibility. Full PureScript/Haskell/Lean4 migration.**

**Philosophy: SUCCESS = ACCURACY. SPEED = BAD.**

This is a multi-month systematic migration. Every step must be perfect.

---

## Scope Reality

| Layer | Current Lines | Migrated | Remaining | % Complete |
|-------|---------------|----------|-----------|------------|
| TypeScript/Vue | ~265,000 | 0 | ~265,000 | 0% |
| Python Backend | ~11,000 | 0 | ~11,000 | 0% |
| PureScript Types | ~10,000 | ~10,000 | - | 100% (types only) |
| Haskell Utils | ~5,000 | ~5,000 | - | 100% (utils only) |
| Lean4 Proofs | ~2,000 | ~2,000 | - | 100% (proofs only) |

**Overall: ~5% complete** (foundations laid, implementation remains)

---

## Current State Assessment

### Lean4 Infrastructure (leancomfy/lean/)
- [x] TensorCore/Basic.lean - DType, Shape
- [x] TensorCore/Tensor.lean - Dependent tensor types
- [x] TensorCore/Ops.lean - Type-safe operations
- [x] TensorCore/Geometry.lean - 3D primitives (Vec3, Point3, ColorRGB)
- [x] TensorCore/Extract.lean - Extractable typeclass + roundtrip proofs
- [x] TensorCore/VerifiedOps.lean - **FIXED 2026-01-26: replaced native_decide with explicit axioms**

### PureScript Infrastructure (leancomfy/purescript/Lattice/)
- [x] Effects.purs - Complete effect types with refined primitives
- [x] Project.purs
- [x] Physics.purs
- [x] Shapes.purs
- [x] LayerStyles.purs
- [x] Transform.purs
- [x] Particles.purs
- [x] Animation.purs
- [x] BlendModes.purs
- [x] Camera.purs
- [x] Assets.purs
- [x] Text.purs
- [x] Spline.purs
- [x] Masks.purs
- [x] MeshWarp.purs
- [x] Utils/* (NumericSafety, Validation, TypeGuards, etc.)
- [x] Schemas/* (complete schema definitions)
- [x] Services/* (Easing, Math3D, BlendModes, Particles, Interpolation)

### Haskell Infrastructure (src/lattice/)
- [x] Utils/* (NumericSafety, Easing, TypeGuards, FpsUtils, Validation, etc.)
- [x] Services/* (Expressions, VectorMath, CoordinateConversion, etc.)
- [x] FFI/* (bridges to PureScript/TypeScript)
- [x] State/* (Composition, History, Marker, Theme, UI, Camera, etc.)
- [x] Database/DuckDB.hs - **Placeholder only, needs implementation**

### Violations Found & Status

**Total `native_decide` violations in our Lean4 code: 88** (excluding dependencies)

| File | Count | Status | Date |
|------|-------|--------|------|
| `leancomfy/lean/TensorCore/VerifiedOps.lean` | 15→1 | FIXED | 2026-01-26 |
| `leancomfy/lean/Lattice/Physics/Space.lean` | 14 | PENDING | - |
| `leancomfy/lean/Lattice/Physics/Core.lean` | 10 | PENDING | - |
| `leancomfy/lean/Lattice/Effects/Presets.lean` | 8 | PENDING | - |
| `leancomfy/lean/Lattice/Shapes/Primitives.lean` | 6 | PENDING | - |
| `leancomfy/lean/Lattice/Effects/Parameters.lean` | 4 | PENDING | - |
| `leancomfy/lean/Lattice/Services/Particles/Emitter.lean` | 4 | PENDING | - |
| `leancomfy/lean/Lattice/Text.lean` | 4 | PENDING | - |
| `leancomfy/lean/Lattice/Masks.lean` | 4 | PENDING | - |
| `leancomfy/lean/Interpolation/Interpolation.lean` | 3 | PENDING | - |
| `leancomfy/lean/Lattice/Services/Particles/Modulation.lean` | 3 | PENDING | - |
| *(17 more files with 1-2 each)* | ~17 | PENDING | - |

**Haskell violations:**
| File | Violation | Status | Date |
|------|-----------|--------|------|
| `src/lattice/Database/DuckDB.hs` | unused `unsafePerformIO` import | FIXED | 2026-01-26 |

---

## Phase 1: Fix Lean4 Violations (CRITICAL)

- [ ] Replace all `native_decide` in VerifiedOps.lean with structural proofs
- [ ] Ensure no `sorry`, `partial def`, `panic!`, `unreachable!`
- [ ] Run `lake build` to verify all proofs complete

### Theorems Requiring Rewrite:
1. `vadd_comm` - Vector addition commutativity
2. `vadd_assoc` - Vector addition associativity
3. `vadd_zero` - Zero identity for addition
4. `zero_vadd` - Zero identity for addition (left)
5. `vadd_neg` - Additive inverse
6. `vscale_vadd` - Scalar multiplication distributivity
7. `vdot_comm` - Dot product commutativity
8. `vdot_vadd_left` - Dot product bilinearity
9. `vcross_anticomm` - Cross product anticommutativity
10. `vcross_self` - Cross product with self
11. `translate_compose` - Translation composition

---

## Phase 2: Complete TypeScript → PureScript Migration

### Types Still in TypeScript (ui/src/types/)
- [ ] effects.ts (3,338 lines) → Verify full coverage in Effects.purs
- [ ] project.ts (2,203 lines) → Verify full coverage in Project.purs
- [ ] physics.ts (990 lines) → Verify full coverage in Physics.purs
- [ ] shapes.ts (848 lines) → Verify full coverage in Shapes.purs
- [ ] presets.ts (830 lines) → Verify full coverage in Presets.purs
- [ ] layerStyles.ts (721 lines) → Verify full coverage in LayerStyles.purs
- [ ] transform.ts (689 lines) → Verify full coverage in Transform.purs
- [ ] particles.ts (643 lines) → Verify full coverage in Particles.purs
- [ ] layerData.ts (565 lines) → Verify full coverage in LayerData.purs

---

## Phase 3: Implement DuckDB Bindings

- [ ] Choose binding approach: duckdb-haskell package vs FFI
- [ ] Implement type-safe query builder (no raw SQL strings)
- [ ] Implement connection pooling
- [ ] Implement transaction support
- [ ] Write comprehensive tests
- [ ] Zero `unsafePerformIO` usage

---

## Phase 4: Complete Store Migration

### Stores to Migrate (ui/src/stores/)
- [ ] assetStore.ts (1,104 lines) → Haskell state module
- [ ] projectStore.ts (930 lines) → Haskell state module
- [ ] compositorStore.ts (867 lines) → Haskell state module
- [ ] timelineStore.ts (746 lines) → Haskell state module
- [ ] exportStore.ts (681 lines) → Haskell state module
- [ ] particleStore.ts (636 lines) → Haskell state module
- [ ] curveEditorStore.ts (600 lines) → Haskell state module
- [ ] keyframeStore.ts (596 lines) → Haskell state module
- [ ] selectionStore.ts (564 lines) → Haskell state module

---

## Phase 5: Python Backend → Haskell

- [ ] compositor_node.py (1,877 lines) → Servant API
- [ ] HTTP routes → Servant routes
- [ ] Validation logic → Haskell validators
- [ ] ComfyUI integration → FFI or subprocess

---

## Verification Commands

```bash
# Lean4 proofs
cd leancomfy/lean && lake build

# PureScript
cd leancomfy/purescript && spago build --pedantic-packages

# Haskell
cd src/lattice && cabal build -Wall -Werror

# Check banned constructs
scripts/check-formal-escapes.sh

# TypeScript (until fully migrated)
npx tsc --noEmit
npm test
```

---

## Success Criteria

- [ ] All Lean4 files: ZERO `sorry`, `native_decide`, `partial def`, `panic!`
- [ ] All Haskell files: ZERO `undefined`, `error`, `unsafeCoerce`, `unsafePerformIO`
- [ ] All PureScript files: ZERO `unsafePartial`, `unsafeCoerce`, `undefined`
- [ ] All proofs complete (`lake build` succeeds)
- [ ] All tests pass
- [ ] DuckDB files preserved and functional

---

*Last Updated: 2026-01-26*
