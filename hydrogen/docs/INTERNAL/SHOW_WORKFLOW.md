━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                         // show // audit // workflow
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

   "At billion-agent scale, consistent debugging infrastructure is the
    difference between diagnosable systems and chaos."

                                                                    — principle

# SHOW AUDIT WORKFLOW

This document provides a systematic workflow for auditing and fixing Show
instances across the Hydrogen codebase. Follow these steps exactly.

## Purpose

The `Show` type class in Hydrogen serves as **structured debugging infrastructure**.
Every Schema atom must implement Show in a parseable, deterministic format that
enables:

1. Runtime introspection by agents
2. Debug feature flags without recompilation
3. Graph visualization of co-effects
4. Reproducible bug reports

See `docs/SHOW_DEBUG_CONVENTION.md` for the full rationale.

## The Convention

### Format Rules

```
(TypeName field1:value1 field2:value2)
```

1. **Parentheses** wrap the entire output
2. **Type name** comes first, exactly matching the constructor
3. **Named fields** use `fieldName:value` format (colon, no space after)
4. **Spaces** separate fields (not commas)
5. **Nested types** are shown recursively (parens nest naturally)

### Pattern: Compound Types (records/newtypes with fields)

```purescript
-- Type with named fields
newtype Box3 = Box3 (Vec3 Number) (Vec3 Number)

instance showBox3 :: Show Box3 where
  show (Box3 minV maxV) =
    "(Box3 min:" <> show minV <> " max:" <> show maxV <> ")"

-- Output: "(Box3 min:(Vec3 1.0 2.0 3.0) max:(Vec3 4.0 5.0 6.0))"
```

### Pattern: Simple Types (2-3 obvious positional values)

```purescript
-- Type where field meaning is obvious from position
newtype Point2D = Point2D { x :: Number, y :: Number }

instance showPoint2D :: Show Point2D where
  show (Point2D p) = "(Point2D " <> show p.x <> " " <> show p.y <> ")"

-- Output: "(Point2D 100.0 50.0)"
```

### Pattern: Sum Types (enums with constructors)

```purescript
-- Enum-like constructors without fields: bare name
data Chirality = Chiral | Achiral

instance showChirality :: Show Chirality where
  show Chiral = "Chiral"
  show Achiral = "Achiral"

-- Constructors with fields: wrap in parens
data BorderEffect
  = EffectGradient GradientStroke
  | EffectNone

instance showBorderEffect :: Show BorderEffect where
  show (EffectGradient gs) = "(EffectGradient " <> show gs <> ")"
  show EffectNone = "EffectNone"
```

### Pattern: Unit-Suffixed Values (acceptable exception)

```purescript
-- Angles with unit suffix are acceptable (unambiguous, parseable)
instance showDegrees :: Show Degrees where
  show (Degrees d) = show d <> "deg"

-- Output: "45.0deg"
```

## Workflow Steps

### Step 1: Identify Target Pillar

Choose a Schema pillar to audit:

```
src/Hydrogen/Schema/
├── Color/          -- Color spaces, channels, gradients
├── Dimension/      -- Units, vectors, spacing
├── Geometry/       -- Shapes, transforms, primitives  [COMPLETED]
├── Typography/     -- Fonts, text, metrics
├── Material/       -- Filters, noise, borders
├── Elevation/      -- Shadows, z-index
├── Temporal/       -- Time, duration, animation
├── Reactive/       -- State, validation
├── Gestural/       -- Input, pointers
├── Spatial/        -- 3D, PBR, XR
└── ...
```

### Step 2: List All Files

```bash
# Find all PureScript files in the pillar
find src/Hydrogen/Schema/[Pillar] -name "*.purs" | sort
```

### Step 3: For Each File

#### 3a. Read the entire file first

Never edit without reading. Understand:
- What types are defined
- What Show instances exist
- What the current format is

#### 3b. Identify all Show instances

Search for `instance show` in the file. Note each one.

#### 3c. Check each instance against the convention

**Wrong patterns to fix:**

```purescript
-- WRONG: CSS-like format
show (GradientLinear angle) = "linear(" <> show angle <> "deg)"
-- RIGHT:
show (GradientLinear angle) = "(GradientLinear " <> show angle <> ")"

-- WRONG: Braces and commas
show (Box b) = "Box { min: " <> show b.min <> ", max: " <> show b.max <> " }"
-- RIGHT:
show (Box b) = "(Box min:" <> show b.min <> " max:" <> show b.max <> ")"

-- WRONG: Bare values without type name
show (VertexIndex i) = show i
-- RIGHT:
show (VertexIndex i) = "(VertexIndex " <> show i <> ")"

-- WRONG: Human-readable but unparseable
show (RotationalSymmetry r) = "RotationalSymmetry(" <> show r.folds <> "-fold)"
-- RIGHT:
show (RotationalSymmetry r) = "(RotationalSymmetry folds:" <> show r.folds <> ")"
```

#### 3d. Fix each instance

Edit one instance at a time. Verify the file still compiles after each change.

#### 3e. Build and verify

```bash
nix develop --command spago build
```

Must show 0 errors. Warnings are acceptable but note them.

### Step 4: Update Todo List

Track progress with the TodoWrite tool:
- Mark completed files
- Note any issues discovered
- Track remaining files

### Step 5: Document Completion

When a pillar is complete:
1. Verify full build passes
2. Update this workflow with any pillar-specific notes
3. Note the pillar as complete in session handoff

## Pillar Status

| Pillar      | Status      | Notes                                    |
|-------------|-------------|------------------------------------------|
| Geometry    | ✅ COMPLETE | Show audit done, build clean             |
| Color       | NOT STARTED |                                          |
| Dimension   | NOT STARTED |                                          |
| Typography  | NOT STARTED |                                          |
| Material    | NOT STARTED |                                          |
| Elevation   | NOT STARTED |                                          |
| Temporal    | NOT STARTED |                                          |
| Reactive    | NOT STARTED |                                          |
| Gestural    | NOT STARTED |                                          |
| Spatial     | NOT STARTED |                                          |

## Common Issues

### Issue: Circular Show Dependencies

If type A shows type B and type B shows type A:
- Ensure both follow the convention
- The nesting will work naturally: `(A inner:(B ...))`

### Issue: Array/Collection Types

For arrays, use standard Show for Array which gives `[item1, item2]`:

```purescript
show (Mesh m) = "(Mesh vertices:" <> show (length m.vertices) <> ")"
-- Show count, not full array (for large collections)
```

### Issue: Maybe Types

Use a helper or inline:

```purescript
showMaybe :: forall a. Show a => Maybe a -> String
showMaybe Nothing = "Nothing"
showMaybe (Just a) = "(Just " <> show a <> ")"
```

### Issue: Function Fields

Functions cannot be shown. Use a placeholder or omit:

```purescript
show (Config c) = "(Config name:" <> show c.name <> " callback:<fn>)"
```

## Verification Checklist

Before marking a pillar complete:

- [ ] All files in pillar read fully before editing
- [ ] All Show instances follow the convention
- [ ] Build passes with 0 errors
- [ ] No Show instances deleted (only modified)
- [ ] Nested types show correctly (test with complex values)

## Reference Files

Completed examples to use as reference:

- `src/Hydrogen/Schema/Geometry/Point.purs` — Simple positional pattern
- `src/Hydrogen/Schema/Geometry/Box3.purs` — Named fields pattern
- `src/Hydrogen/Schema/Geometry/Symmetry.purs` — Complex sum types
- `src/Hydrogen/Schema/Geometry/AnimatedBorder.purs` — Many instance types

────────────────────────────────────────────────────────────────────────────────

                                                         — Opus 4.5 // 2026-02-25

