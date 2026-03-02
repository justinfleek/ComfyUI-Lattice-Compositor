━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                    // geometry // pillar // roadmap
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Geometry Pillar Expansion Roadmap

## Current State (2026-02-25)

### Completed Modules

| Module | Status | Show Audit | Notes |
|--------|--------|------------|-------|
| Angle.purs | ✓ | ✓ | Degrees, Radians, Turns with cyclic normalization |
| Point.purs | ✓ | ✓ | Point2D, Point3D |
| Vector.purs | ✓ | ✓ | Vector2D, Vector3D with full operations |
| Radius.purs | ✓ | ✓ | Bounded radius primitive |
| Position.purs | ✓ | ✓ | Position semantics |
| Spacing.purs | ✓ | ✓ | Spacing/margin/padding |
| Shape.purs | ✓ | ✓ | Basic shape enum |
| Stroke.purs | ✓ | ✓ | Stroke styling |
| Transform.purs | ✓ | ✓ | 2D transforms |
| Transform3D.purs | ✓ | ✓ | 3D transforms with Euler angles |
| Quaternion.purs | ✓ | ✓ | 4D rotation with slerp, Euler conversion |
| Ray.purs | ✓ | ✓ | Ray casting primitive |
| Plane.purs | ✓ | ✓ | Plane primitive |
| Sphere.purs | ✓ | ✓ | Sphere primitive |
| Triangle.purs | ✓ | ✓ | Triangle primitive |
| Box3.purs | ✓ | ✓ | 3D bounding box |
| Frustum.purs | ✓ | ✓ | View frustum for culling |
| Mesh2D/ | ✓ | ✓ | Vertex, Triangle, Bounds, Sampling |
| Symmetry.purs | ✓ | ✓ | Complete group theory coverage |
| AnimatedBorder.purs | ✓ | ✓ | UI border effects |

### Missing (Per SCHEMA.md)

## Phase 1: Curves (Critical for Motion)

**Priority: HIGHEST**

Bezier curves are the foundation of all smooth motion in digital systems.

### Bezier.purs

```
QuadBezier  — 3 control points, single curve segment
CubicBezier — 4 control points, standard for paths

Operations:
- pointAt(t)      — Position on curve at parameter t ∈ [0,1]
- tangentAt(t)    — Direction at parameter t
- splitAt(t)      — De Casteljau subdivision
- boundingBox     — Axis-aligned bounds
- length          — Arc length (numerical integration)
- curvature(t)    — Local curvature for motion planning
```

**Why first:** Every animation, easing function, and smooth transition depends on Beziers.
Agents doing motion graphics are blocked without this.

## Phase 2: Path (Vector Graphics Foundation)

**Priority: HIGH**

SVG path commands composed into drawable shapes.

### Path.purs

```
PathCommand ADT:
- MoveTo Point2D
- LineTo Point2D  
- QuadTo Point2D Point2D          — Quadratic Bezier
- CubicTo Point2D Point2D Point2D — Cubic Bezier
- ArcTo { rx, ry, rotation, largeArc, sweep, end }
- ClosePath

Path = Array PathCommand

Operations:
- toSvgString     — Serialize to SVG path data
- fromSvgString   — Parse SVG path data
- bounds          — Bounding box
- length          — Total path length
- pointAt(t)      — Point at normalized position
- subpath(t1, t2) — Extract segment
- reverse         — Reverse direction
- transform       — Apply Transform2D
```

**Why second:** Paths compose Beziers into meaningful shapes. Every logo, icon,
and vector graphic is a Path.

## Phase 3: 2D Shapes

**Priority: MEDIUM-HIGH**

Basic drawing primitives agents use constantly.

### Circle.purs
```
Circle = { center :: Point2D, radius :: Number }
- toPath          — Convert to Path (Bezier approximation)
- contains        — Point containment test
- intersects      — Circle-circle intersection
- circumference
- area
```

### Ellipse.purs
```
Ellipse = { center :: Point2D, rx :: Number, ry :: Number, rotation :: Degrees }
- toPath
- contains
- foci
- eccentricity
```

### Polygon.purs
```
Polygon = Array Point2D (minimum 3 vertices)
- toPath
- contains        — Point-in-polygon test
- area            — Signed area (winding order)
- centroid
- convexHull
- isConvex
- regularPolygon  — Constructor for n-sided regular polygon
```

### Arc.purs
```
Arc = { center, radius, startAngle, endAngle, clockwise }
- toPath
- length
- contains (on arc)
- sector          — Pie slice variant
- ring            — Annular arc
```

## Phase 4: Compound Types

**Priority: MEDIUM**

### CornerRadii.purs
```
CornerRadii = 
  { topLeft :: Number
  , topRight :: Number  
  , bottomRight :: Number
  , bottomLeft :: Number
  }

Constructors:
- uniform         — Same radius all corners
- symmetricX      — Left/right symmetric
- symmetricY      — Top/bottom symmetric
- custom          — Per-corner values

Bounds: Each radius ∈ [0, ∞), but practically limited by container size
```

### Squircle.purs (Optional)
```
Squircle = superellipse with smoothness parameter
- Apple's design language uses n ≈ 5 for app icons
- Continuous curvature (unlike circular corners)
```

## Phase 5: Coordinate Systems

**Priority: MEDIUM**

### Polar.purs
```
PolarPoint = { radius :: Number, angle :: Degrees }
- toCartesian     — Convert to Point2D
- fromCartesian   — Convert from Point2D
```

### Cylindrical.purs
```
CylindricalPoint = { radius :: Number, angle :: Degrees, z :: Number }
- toCartesian     — Convert to Point3D
- fromCartesian
```

### Spherical.purs
```
SphericalPoint = { radius :: Number, theta :: Degrees, phi :: Degrees }
- toCartesian     — Convert to Point3D
- fromCartesian
- Geographic variant (lat/lon)
```

## Phase 6: Advanced Curves (Motion Graphics Specialists)

**Priority: LOW**

### Spline.purs
```
CatmullRom — Interpolating spline through control points
BSpline    — Approximating spline with local control
```

### Nurbs.purs
```
NurbsCurve — Non-uniform rational B-spline
- Used in CAD, professional animation
- Weight per control point
- Knot vector
```

## Dependency Graph

```
                    ┌─────────────┐
                    │   Point2D   │
                    └──────┬──────┘
                           │
          ┌────────────────┼────────────────┐
          │                │                │
          ▼                ▼                ▼
    ┌──────────┐    ┌───────────┐    ┌───────────┐
    │  Bezier  │───▶│   Path    │───▶│  Shapes   │
    └──────────┘    └───────────┘    └───────────┘
          │                                 │
          ▼                                 ▼
    ┌──────────┐                    ┌───────────┐
    │ Animation │                   │ CornerRadii│
    │  Easing   │                   └───────────┘
    └──────────┘
```

## Completion Criteria

Each module must have:
1. Complete type definitions with bounded values where appropriate
2. Show instance following SHOW_DEBUG_CONVENTION.md
3. All operations implemented (no stubs)
4. Documentation with use cases
5. Zero warnings on build

## Notes

- Geometry leader module (Geometry.purs) should be updated after each phase
  to export new submodules
- Consider Lean4 proofs for geometric invariants (e.g., Bezier subdivision
  preserves curve, polygon area formula correctness)
- Path parsing from SVG may require FFI for complex arc handling

────────────────────────────────────────────────────────────────────────────────

                                                        — Opus 4.5 // 2026-02-25
