━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                       // session // handoff
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Session Handoff — 2026-02-25

## Context

This document provides clear instructions for the next AI session continuing
work on the Hydrogen Geometry pillar and related infrastructure.

**Read before starting:**
- CLAUDE.md (project rules, attestation, conventions)
- docs/CONTINUITY_VISION.md (why correctness matters)
- docs/SHOW_DEBUG_CONVENTION.md (Show instance requirements)
- docs/GEOMETRY_ROADMAP.md (detailed Geometry expansion plan)

## Completed This Session

### Geometry Pillar

| Module | Status | Lines | Description |
|--------|--------|-------|-------------|
| Quaternion.purs | ✓ Complete | ~324 | 4D rotation, slerp, Euler conversion, rotateVector |
| Bezier.purs | ✓ Complete | ~500+ | QuadBezier, CubicBezier, De Casteljau, bounding, length, curvature, hit testing |
| Path.purs | ✓ Complete | ~700+ | SVG commands, serialization, geometry, transforms, flatten |

### Documentation

| Document | Status | Description |
|----------|--------|-------------|
| GEOMETRY_ROADMAP.md | ✓ Created | Full expansion plan with phases and dependencies |
| SESSION_HANDOFF.md | ✓ Created | This document |

## Next Priorities (In Order)

### Priority 1: 2D Shapes
**Location:** `src/Hydrogen/Schema/Geometry/`

Create these modules:

1. **Circle.purs**
   - `Circle = { center :: Point2D, radius :: Number }`
   - `toPath` — Convert to Path (Bezier approximation)
   - `contains` — Point containment test
   - `intersectsCircle` — Circle-circle intersection
   - `circumference`, `area`
   - `tangentAt` — Tangent at angle

2. **Ellipse.purs**
   - `Ellipse = { center :: Point2D, rx :: Number, ry :: Number, rotation :: Degrees }`
   - `toPath` — Convert to Path
   - `contains` — Point containment
   - `foci` — Return both foci points
   - `eccentricity`

3. **Polygon.purs**
   - `Polygon = Array Point2D` (minimum 3 vertices)
   - `toPath` — Convert to Path
   - `contains` — Point-in-polygon test (ray casting)
   - `area` — Signed area (shoelace formula)
   - `centroid` — Geometric center
   - `isConvex` — Convexity test
   - `regularPolygon` — Constructor for n-sided regular polygon

4. **Arc.purs**
   - `Arc = { center :: Point2D, radius :: Number, startAngle :: Degrees, endAngle :: Degrees, clockwise :: Boolean }`
   - `toPath` — Convert to Path
   - `length` — Arc length
   - `sector` — Pie slice variant (includes center)
   - `pointAtAngle` — Point on arc at given angle

### Priority 2: CornerRadii Compound Type
**Location:** `src/Hydrogen/Schema/Geometry/CornerRadii.purs`

```
CornerRadii = 
  { topLeft :: Number
  , topRight :: Number  
  , bottomRight :: Number
  , bottomLeft :: Number
  }
```

Required functions:
- `uniform` — Same radius all corners
- `symmetricX` — Left/right symmetric
- `symmetricY` — Top/bottom symmetric
- `custom` — Per-corner values
- `toPath` — Generate rounded rectangle path
- `clamp` — Ensure radii don't exceed half of width/height

### Priority 3: Coordinate Systems
**Location:** `src/Hydrogen/Schema/Geometry/`

1. **Polar.purs**
   - `PolarPoint = { radius :: Number, angle :: Degrees }`
   - `toCartesian :: PolarPoint -> Point2D`
   - `fromCartesian :: Point2D -> PolarPoint`

2. **Cylindrical.purs**
   - `CylindricalPoint = { radius :: Number, angle :: Degrees, z :: Number }`
   - `toCartesian :: CylindricalPoint -> Point3D`
   - `fromCartesian :: Point3D -> CylindricalPoint`

3. **Spherical.purs**
   - `SphericalPoint = { radius :: Number, theta :: Degrees, phi :: Degrees }`
   - `toCartesian :: SphericalPoint -> Point3D`
   - `fromCartesian :: Point3D -> SphericalPoint`

### Priority 4: Wire Geometry Leader Module
**Location:** `src/Hydrogen/Schema/Geometry.purs`

Currently only exports `Radius`. Update to re-export all Geometry submodules:
- Angle, Point, Vector, Radius
- Transform, Transform3D, Quaternion
- Shape, Stroke, Position, Spacing
- Bezier, Path
- Circle, Ellipse, Polygon, Arc
- CornerRadii
- Polar, Cylindrical, Spherical
- Ray, Plane, Sphere, Triangle, Box3, Frustum
- Mesh2D, Symmetry, AnimatedBorder

## Known Blockers

### Brand.purs Missing Sub-Modules

`src/Hydrogen/Schema/Brand/Brand.purs` imports 6 modules that don't exist:

1. `Hydrogen.Schema.Brand.Identity` — BrandIdentity, BrandName, Domain, UUID
2. `Hydrogen.Schema.Brand.Palette` — OKLCH colors, semantic roles
3. `Hydrogen.Schema.Brand.Typography` — Font families, weights, scales
4. `Hydrogen.Schema.Brand.Spacing` — Grid systems, spacing units
5. `Hydrogen.Schema.Brand.Voice` — Tone, personality traits
6. `Hydrogen.Schema.Brand.Provenance` — Content hashing, timestamps

**Impact:** Full `spago build` fails with 6 ModuleNotFound errors.

**Workaround:** Temporarily rename Brand.purs to Brand.purs.disabled when testing other modules:
```bash
mv src/Hydrogen/Schema/Brand/Brand.purs src/Hydrogen/Schema/Brand/Brand.purs.disabled
# ... build/test ...
mv src/Hydrogen/Schema/Brand/Brand.purs.disabled src/Hydrogen/Schema/Brand/Brand.purs
```

**Future work:** Create all 6 Brand sub-modules to unblock full build.

## Build Commands

```bash
# Enter dev environment
nix develop

# Build (will fail on Brand until sub-modules exist)
spago build

# Build with Brand disabled (workaround)
mv src/Hydrogen/Schema/Brand/Brand.purs src/Hydrogen/Schema/Brand/Brand.purs.disabled
spago build
mv src/Hydrogen/Schema/Brand/Brand.purs.disabled src/Hydrogen/Schema/Brand/Brand.purs
```

## Development Process Reminders

From CLAUDE.md:

1. **Never write large files in a single operation** — Create minimal headers, then edit incrementally
2. **Never delete code to fix warnings** — "Unused" means incomplete, not unnecessary
3. **Never remove imports to silence warnings** — Imports define module's semantic scope
4. **Explicit imports on EVERYTHING** — No `(..)` canaries
5. **Show instances follow SHOW_DEBUG_CONVENTION.md** — Parseable, type-prefixed output
6. **No stubs, no TODOs** — Complete implementations only
7. **Verify build after each significant change**

## File Structure Reference

```
src/Hydrogen/Schema/Geometry/
├── Angle.purs          ✓ Complete
├── AnimatedBorder.purs ✓ Complete
├── Bezier.purs         ✓ Complete (this session)
├── Box3.purs           ✓ Complete
├── Frustum.purs        ✓ Complete
├── Mesh2D.purs         ✓ Complete
├── Mesh2D/
│   ├── Bounds.purs     ✓ Complete
│   ├── Sampling.purs   ✓ Complete
│   ├── Triangle.purs   ✓ Complete
│   └── Vertex.purs     ✓ Complete
├── Path.purs           ✓ Complete (this session)
├── Plane.purs          ✓ Complete
├── Point.purs          ✓ Complete
├── Position.purs       ✓ Complete
├── Quaternion.purs     ✓ Complete (this session)
├── Radius.purs         ✓ Complete
├── Ray.purs            ✓ Complete
├── Shape.purs          ✓ Complete
├── Spacing.purs        ✓ Complete
├── Sphere.purs         ✓ Complete
├── Stroke.purs         ✓ Complete
├── Symmetry.purs       ✓ Complete
├── Transform.purs      ✓ Complete
├── Transform3D.purs    ✓ Complete
├── Triangle.purs       ✓ Complete
├── Vector.purs         ✓ Complete
├── Arc.purs            ○ TODO
├── Circle.purs         ○ TODO
├── CornerRadii.purs    ○ TODO
├── Cylindrical.purs    ○ TODO
├── Ellipse.purs        ○ TODO
├── Polar.purs          ○ TODO
├── Polygon.purs        ○ TODO
└── Spherical.purs      ○ TODO
```

## Notes for Next Session

- The project is committed to completeness over speed
- Ask before removing any "unused" imports or code
- Read files fully before editing
- Small incremental edits prevent large breakages
- This is infrastructure for autonomous AI agents — correctness is non-negotiable

────────────────────────────────────────────────────────────────────────────────

                                                        — Opus 4.5 // 2026-02-25
