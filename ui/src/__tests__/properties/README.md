# Property-Based Tests

This directory contains **property-based tests** using [fast-check](https://github.com/dubzzz/fast-check).

## Philosophy

Unlike example-based tests that verify specific inputs produce expected outputs, property-based tests verify **invariants that must hold for ALL possible inputs**.

## Properties Tested

### 1. DETERMINISM (`determinism.property.ts`)
The most critical property for a motion compositor:
```
∀ frame, layer: evaluate(layer, frame) === evaluate(layer, frame)
```
Evaluating the same frame twice MUST return identical results.

### 2. INTERPOLATION (`interpolation.property.ts`)
Mathematical properties of keyframe interpolation:
- **Boundary**: `interpolate(0) === firstKeyframe.value`
- **Boundary**: `interpolate(1) === lastKeyframe.value`
- **Monotonicity**: For linear interpolation, if t1 < t2 then value(t1) ≤ value(t2)
- **Bounds** (linear): `min(v1, v2) ≤ interpolate(t) ≤ max(v1, v2)`

### 3. TRANSFORMS (`transforms.property.ts`)
Matrix/transform composition properties:
- **Identity**: `transform(identity, point) === point`
- **Associativity**: `(A * B) * C === A * (B * C)`
- **Inverse**: `transform(inverse(M), transform(M, point)) === point`

### 4. EXPRESSIONS (`expressions.property.ts`)
Expression evaluation invariants:
- **Purity**: Same expression + same context = same result
- **Bounds**: `wiggle()` respects amplitude bounds
- **Continuity**: Expression results change smoothly

### 5. BLEND MODES (`blendModes.property.ts`)
Compositing invariants:
- **Identity**: `blend(image, transparent, 'normal') === image`
- **Commutativity** (where applicable): `add(A, B) === add(B, A)`

### 6. SERIALIZATION (`serialization.property.ts`)
Project format invariants:
- **Roundtrip**: `deserialize(serialize(project)) === project`
- **Idempotence**: `serialize(deserialize(serialize(p))) === serialize(p)`

### 7. UNDO/REDO (`undoRedo.property.ts`)
State mutation invariants:
- **Symmetry**: `undo(redo(state)) === state`
- **Idempotence**: `undo(undo(state))` has no effect after single action

## Running Property Tests

```bash
# Run all property tests
npm run test -- --grep "property"

# Run specific property test
npm run test -- src/__tests__/properties/interpolation.property.ts

# Run with verbose output (shows shrunk failing cases)
npm run test -- --reporter=verbose src/__tests__/properties/
```

## Understanding Failures

When a property test fails, fast-check will:
1. Show the failing input
2. **Shrink** it to the minimal failing case
3. Display the seed for reproducibility

Example output:
```
Property failed after 42 tests
Counterexample: [frame: 50, keyframes: [{frame: 0, value: 100}, {frame: 100, value: 0}]]
Shrunk 5 times
Seed: 1234567890
```

To reproduce:
```typescript
fc.assert(myProperty, { seed: 1234567890 })
```

## Writing New Properties

```typescript
import { fc, test } from '@fast-check/vitest';

test.prop([fc.integer(), fc.integer()])('addition is commutative', (a, b) => {
  return a + b === b + a;
});
```

## Coverage Goals

- [ ] All pure functions in `services/interpolation.ts`
- [ ] All easing functions in `services/easing.ts`
- [ ] All expression evaluators in `services/expressions.ts`
- [ ] All blend mode functions in `types/blendModes.ts`
- [ ] All transform utilities in `types/transform.ts`
- [ ] Project serialization roundtrip
- [ ] Store action undo/redo symmetry
