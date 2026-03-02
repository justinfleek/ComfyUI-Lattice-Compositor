━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                            // schema // foundation // analysis
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# SCHEMA FOUNDATION ANALYSIS

## Purpose

This document analyzes the current Schema foundation and identifies what needs
to be modified or strengthened before future sessions build on top of it.

The goal: **A rock-solid 2D/3D coordinate and transform system that every
pillar can depend on without ambiguity.**

## Current State Assessment

After examining:
- `Bounded.purs` — Foundation for bounded numeric types
- `Geometry/Point.purs` — Point2D, Point3D with operations
- `Geometry/Vector.purs` — Vector2D, Vector3D with full algebra
- `Geometry/Transform.purs` — 2D transforms (scale, rotate, translate, skew)
- `Geometry/Shape.purs` — Shape primitives and boolean operations
- `Dimension/Device.purs` — Pixel types and device units

### What Exists and Works Well

**1. Point2D / Point3D (Geometry/Point.purs) — SOLID**
- Clear distinction: Point = position, not displacement
- Full operations: translate, midpoint, distance, lerp, reflect
- Coordinate system documented (right-handed for 3D)
- Proper Eq, Ord, Show instances
- 472 lines, complete

**2. Vector2D / Vector3D (Geometry/Vector.purs) — SOLID**
- Clear distinction from Point (displacement, not position)
- Full algebra: add, sub, scale, negate, dot, cross, normalize
- Point-Vector operations: translatePoint, pointDiff, directionTo
- Semiring/Ring instances for algebraic composition
- 624 lines, complete

**3. Bounded.purs — SOLID FOUNDATION**
- `clampInt`, `clampNumber` for safe bounds
- `ensureFinite` blocks NaN/Infinity propagation
- Common bounds: percent, unit, byte, degrees, normalized
- Documentation for agent understanding

**4. Transform.purs (2D) — SOLID**
- Scale bounded (-10 to 10)
- Skew bounded (-89 to 89 degrees)
- Rotation uses Degrees type (auto-normalized)
- Composed Transform2D with proper ordering
- 595 lines, complete

**5. Device.purs — SOLID**
- Multiple pixel types: Pixel, DevicePixel, CSSPixel, dp, sp
- PPI and DPR types for conversion context
- Semiring/Ring instances for Pixel arithmetic

### What Needs Strengthening

**1. Point2D uses unbounded Number — CONCERN**

```purescript
-- Current (Point.purs line 140)
newtype Point2D = Point2D { x :: Number, y :: Number }
```

Points can be at `Infinity` or `NaN` positions. For agent embodiment at scale,
this allows invalid states.

**Recommendation:** Add `ensureFinite` in constructors, or define bounded
world coordinates.

**2. Transform3D is separate and incomplete**

`Transform.purs` handles 2D beautifully, but 3D transforms are in a separate
`Transform3D.purs` that may not have the same rigor.

**Recommendation:** Audit Transform3D.purs for same bounded/safe patterns.

**3. Shape.purs redefines Point2D locally**

```purescript
-- Shape.purs line 39-41
, Point2D
, point2D
, origin
```

This creates potential confusion — which Point2D should code use?

**Recommendation:** Shape should import from Geometry/Point, not redefine.

**4. Geometry.purs only re-exports Radius**

```purescript
-- Geometry.purs line 26-30
module Hydrogen.Schema.Geometry
  ( module Hydrogen.Schema.Geometry.Radius
  ) where
import Hydrogen.Schema.Geometry.Radius
```

The main Geometry module should re-export Point, Vector, Transform, Shape.

**Recommendation:** Expand Geometry.purs to be the single entry point.

**5. No Matrix type**

Transforms are represented as composed operations, not as matrices. This is
fine for simple cases but insufficient for:
- Arbitrary affine transforms
- 3D projection matrices
- Camera transforms
- Skeletal animation

**Recommendation:** Add Matrix3x3 (2D affine) and Matrix4x4 (3D affine).

### What's Missing

**1. BoundingBox type**

We have Point and Size concepts but no unified BoundingBox:

```purescript
-- Needed
type BoundingBox2D = { min :: Point2D, max :: Point2D }
type BoundingBox3D = { min :: Point3D, max :: Point3D }

-- Operations
contains :: Point2D -> BoundingBox2D -> Boolean
overlaps :: BoundingBox2D -> BoundingBox2D -> Boolean
union :: BoundingBox2D -> BoundingBox2D -> BoundingBox2D
intersection :: BoundingBox2D -> BoundingBox2D -> Maybe BoundingBox2D
```

**2. Size2D / Size3D types**

Dimensions (width × height) vs Points (x, y) should be distinct:

```purescript
newtype Size2D = Size2D { width :: Number, height :: Number }
newtype Size3D = Size3D { width :: Number, height :: Number, depth :: Number }
```

**3. Matrix types**

```purescript
-- 2D affine (3×3 homogeneous)
type Matrix3 = 
  { m00 :: Number, m01 :: Number, m02 :: Number
  , m10 :: Number, m11 :: Number, m12 :: Number
  , m20 :: Number, m21 :: Number, m22 :: Number
  }

-- 3D affine (4×4 homogeneous)
type Matrix4 = { ... 16 elements ... }

-- Operations
multiply :: Matrix4 -> Matrix4 -> Matrix4
inverse :: Matrix4 -> Maybe Matrix4
transformPoint :: Matrix4 -> Point3D -> Point3D
transformVector :: Matrix4 -> Vector3D -> Vector3D
```

**4. Quaternion for 3D rotation**

Euler angles have gimbal lock. Quaternions don't:

```purescript
type Quaternion = { w :: Number, x :: Number, y :: Number, z :: Number }

-- Operations
fromAxisAngle :: Vector3D -> Degrees -> Quaternion
toMatrix :: Quaternion -> Matrix4
slerp :: Number -> Quaternion -> Quaternion -> Quaternion
multiply :: Quaternion -> Quaternion -> Quaternion
```

**5. Camera/Projection types**

```purescript
type PerspectiveCamera =
  { position :: Point3D
  , target :: Point3D
  , up :: Vector3D
  , fov :: Degrees
  , near :: Number
  , far :: Number
  , aspect :: Number
  }

type OrthographicCamera =
  { position :: Point3D
  , target :: Point3D
  , up :: Vector3D
  , left :: Number
  , right :: Number
  , top :: Number
  , bottom :: Number
  , near :: Number
  , far :: Number
  }
```

## The Universal Coordinate System

For agents to reason about space consistently, we need ONE coordinate system
that all pillars use.

**Current state:** Point.purs documents right-handed 3D (X right, Y up, Z toward
viewer). This is correct and matches WebGL/OpenGL conventions.

**2D convention:** X right, Y down (screen coordinates) vs Y up (math).

**The problem:** Screen Y-down vs Math Y-up creates constant confusion.

**Recommendation: Define canonical spaces**

```
WORLD SPACE (Math convention, Y-up)
- Used for: 3D scenes, physics, agent positions
- Origin: Center of world or bottom-left
- Y: Positive upward

SCREEN SPACE (Screen convention, Y-down)  
- Used for: 2D UI, DOM coordinates, mouse events
- Origin: Top-left
- Y: Positive downward

NORMALIZED DEVICE COORDINATES (NDC)
- Used for: GPU clip space
- Range: -1 to 1 in X and Y
- Origin: Center
- Y: Up (GPU convention)
```

**Conversion functions needed:**

```purescript
worldToScreen :: ViewportConfig -> Point2D -> Point2D
screenToWorld :: ViewportConfig -> Point2D -> Point2D
worldToNDC :: Camera -> Point3D -> Point2D
ndcToScreen :: ViewportConfig -> Point2D -> Point2D
```

## The Universal Unit System

Units are the atoms of measurement. Every dimension must have explicit units.

**Current state:** Device.purs has excellent pixel types (Pixel, DevicePixel,
CSSPixel, dp, sp). But we lack units for:
- Absolute length (mm, cm, inch, point)
- Relative length (em, rem, vh, vw, %)
- Time (ms, s, frames)
- Angle (deg, rad, turns) — Degrees exists but not Radians/Turns

**Recommendation: Extend the unit system**

```purescript
-- Absolute length units
newtype Millimeter = Millimeter Number
newtype Centimeter = Centimeter Number  
newtype Inch = Inch Number
newtype Point = Point Number  -- 1/72 inch (typography)
newtype Pica = Pica Number    -- 12 points

-- Relative length units
newtype Em = Em Number        -- relative to font size
newtype Rem = Rem Number      -- relative to root font size
newtype ViewportWidth = ViewportWidth Number   -- % of viewport width
newtype ViewportHeight = ViewportHeight Number -- % of viewport height
newtype Percent = Percent Number

-- Time units
newtype Milliseconds = Milliseconds Number
newtype Seconds = Seconds Number
newtype Frames = Frames Int   -- discrete frame count

-- Angle units (complement existing Degrees)
newtype Radians = Radians Number
newtype Turns = Turns Number  -- 1 turn = 360 degrees
```

**Conversion type class:**

```purescript
class ConvertUnit a b where
  convert :: a -> b

instance inchToMm :: ConvertUnit Inch Millimeter where
  convert (Inch i) = Millimeter (i * 25.4)

instance degreesToRadians :: ConvertUnit Degrees Radians where
  convert (Degrees d) = Radians (d * pi / 180.0)
```

**Why this matters for agents:**

At billion-agent scale, unit confusion causes cascading failures. If one agent
outputs pixels and another expects millimeters, the composition breaks silently.
Explicit unit types make this a compile-time error, not a runtime disaster.

## The Transform Stack

Transforms compose hierarchically. A button inside a card inside a page has
three transforms applied: button-local → card-local → page-local → world.

**Current state:** Transform.purs composes 2D transforms beautifully with
`composeTransforms`. But we lack:
- A transform stack data structure
- Push/pop operations
- Current transformation matrix (CTM) concept
- 3D transform composition

**Recommendation: Transform context system**

```purescript
-- Transform stack for hierarchical composition
newtype TransformStack2D = TransformStack2D (Array Matrix3)
newtype TransformStack3D = TransformStack3D (Array Matrix4)

-- Operations
pushTransform :: Matrix3 -> TransformStack2D -> TransformStack2D
popTransform :: TransformStack2D -> TransformStack2D
currentTransform :: TransformStack2D -> Matrix3  -- multiply all
transformPoint :: TransformStack2D -> Point2D -> Point2D

-- Named coordinate spaces
data CoordinateSpace
  = LocalSpace      -- relative to parent
  | WorldSpace      -- absolute world position
  | ScreenSpace     -- screen pixels
  | ClipSpace       -- GPU NDC (-1 to 1)
  | TextureSpace    -- UV coordinates (0 to 1)

-- Transform between spaces
transformBetween :: CoordinateSpace -> CoordinateSpace -> RenderContext -> Matrix4
```

**The transform application order:**

```
Point in local space
    ↓ Model transform (object → world)
Point in world space
    ↓ View transform (world → camera)
Point in view/eye space
    ↓ Projection transform (camera → clip)
Point in clip space
    ↓ Viewport transform (clip → screen)
Point in screen space
```

Each stage must be explicit. Agents need to know WHICH space they're in.

## Recommendations for Next Sessions

### Immediate (Before building more pillars)

1. **Fix Shape.purs Point2D duplication**
   - Shape should `import Hydrogen.Schema.Geometry.Point (Point2D, point2D)`
   - Remove local redefinition
   - Verify build passes

2. **Expand Geometry.purs exports**
   - Add: `module Hydrogen.Schema.Geometry.Point`
   - Add: `module Hydrogen.Schema.Geometry.Vector`
   - Add: `module Hydrogen.Schema.Geometry.Transform`
   - Add: `module Hydrogen.Schema.Geometry.Shape`
   - Single import for all geometry needs

3. **Add bounded Point constructors**
   - `safePoint2D :: Number -> Number -> Maybe Point2D` (rejects NaN/Infinity)
   - `boundedPoint2D :: Number -> Number -> Point2D` (clamps to world bounds)
   - Define world bounds constant (e.g., ±1e10)

### Short-term (Next 2-3 sessions)

4. **Create BoundingBox2D / BoundingBox3D**
   - In `Geometry/BoundingBox.purs`
   - Operations: contains, overlaps, union, intersection, expand, center
   - Used by: hit testing, culling, layout

5. **Create Size2D / Size3D**
   - In `Geometry/Size.purs`  
   - Distinct from Point (dimensions vs position)
   - Used by: layout, viewports, textures

6. **Create Matrix3 / Matrix4**
   - In `Geometry/Matrix.purs`
   - Full matrix operations: multiply, inverse, transpose, determinant
   - Conversion: Transform2D → Matrix3, Transform3D → Matrix4

### Medium-term (Foundation for 3D and animation)

7. **Create Quaternion**
   - In `Geometry/Quaternion.purs`
   - Gimbal-lock-free rotation for 3D
   - Slerp for smooth interpolation

8. **Create Camera types**
   - In `Geometry/Camera.purs`
   - PerspectiveCamera, OrthographicCamera
   - View matrix, projection matrix generation

9. **Create coordinate space conversion**
   - In `Geometry/CoordinateSpace.purs`
   - worldToScreen, screenToWorld, etc.
   - ViewportConfig type

### Long-term (Universal unit system)

10. **Extend unit types**
    - Absolute lengths (mm, cm, inch, pt, pica)
    - Relative lengths (em, rem, vh, vw, %)
    - Time units (ms, s, frames)
    - Angle units (radians, turns)
    - ConvertUnit type class

## Priority Order

```
CRITICAL (blocks other work)
├── 1. Fix Shape.purs Point2D import
├── 2. Expand Geometry.purs re-exports
└── 3. Add bounded Point constructors

HIGH (enables major features)
├── 4. BoundingBox2D/3D
├── 5. Size2D/3D
└── 6. Matrix3/Matrix4

MEDIUM (enables advanced features)
├── 7. Quaternion
├── 8. Camera types
└── 9. Coordinate space conversion

LOW (refinement)
└── 10. Extended unit system
```

## Summary

The Schema foundation is SOLID but INCOMPLETE. The existing types (Point, Vector,
Transform, Bounded) follow correct patterns. The work needed is:

1. **Deduplication** — Remove redundant definitions (Shape.purs Point2D)
2. **Consolidation** — Make Geometry.purs the single entry point
3. **Completion** — Add missing types (BoundingBox, Size, Matrix, Quaternion)
4. **Hardening** — Add bounded constructors to prevent invalid states

Once these are complete, the Geometry pillar becomes a rock-solid foundation that
every other pillar can depend on without ambiguity.

**The goal: ANY agent can import `Hydrogen.Schema.Geometry` and have everything
they need for spatial reasoning, with zero invalid states possible.**

────────────────────────────────────────────────────────────────────────────────

                                                       — Opus 4.5 // 2026-02-25

