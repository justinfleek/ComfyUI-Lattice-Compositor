# Spatial Vocabulary — Complete Enumeration

**Purpose:** Exhaustive catalog of spatial concepts that billion-agent swarms need to express when communicating with humans and each other.

**Status:** Complete - 60 sections covering all spatial domains

**Last Updated:** 2026-02-24

---

## Overview

This document catalogs every spatial concept, direction, transformation, and relationship needed for AI agents to express spatial information to humans. The goal is completeness - if an agent needs to describe something spatial, the vocabulary should exist here.

## Catalog Structure

Each section includes:
- **Atoms**: Primitive spatial values (bounded types)
- **Molecules**: Compositions of atoms
- **Compounds**: High-level spatial abstractions
- **Verbs**: Actions/transformations
- **Adjectives**: States/properties

---

## Implementation Status

Legend: [x] = Implemented in Hydrogen Schema | [~] = Partial | [ ] = Not yet

| # | Section | Status | Hydrogen Modules |
|---|---------|--------|------------------|
| 1 | Cardinal Directions | [~] | `Geometry.Position`, `Dimension.Vector` |
| 2 | Relative Directions | [~] | `Geometry.Position` |
| 3 | Positional Relations | [~] | `Geometry.Point`, `Geometry.Shape` |
| 4 | Transformations | [x] | `Geometry.Transform`, `Geometry.Transform3D`, `Motion.Transform` |
| 5 | Deformations | [~] | `Motion.MeshWarp`, `Motion.Effects` |
| 6 | Geometric Primitives | [x] | `Geometry.Shape`, `Geometry.Point`, `Dimension.Vector.*` |
| 7 | Boundary & Topology | [~] | `Geometry.Border`, `Geometry.Stroke` |
| 8 | Coordinate Systems | [x] | `Geometry.Point`, `Dimension.Vector.Vec2/3/4` |
| 9 | Orientation & Alignment | [~] | `Geometry.Transform`, `Reactive.FocusManagement` |
| 10 | Symmetry | [x] | `Geometry.Symmetry` |
| 11 | Distribution & Arrangement | [~] | `Graph.Layout`, `Dimension.Spacing` |
| 12 | Motion & Kinematics | [x] | `Motion.*`, `Gestural.Motion`, `Animation.*` |
| 13 | Fields & Gradients | [~] | `Color.Gradient`, `Material.Noise*` |
| 14 | Projections | [~] | `Dimension.Camera`, `Motion.Camera3D` |
| 15 | Measurement & Metrics | [x] | `Dimension.*`, `Geometry.Angle`, `Geometry.Radius` |
| 16 | Compositional Ops (CSG) | [~] | `Geometry.Shape` (PathCommand) |
| 17 | Nesting & Hierarchy | [~] | `Graph.*`, `Reactive.*` |
| 18 | Temporal-Spatial (4D) | [~] | `Motion.Keyframe`, `Motion.TimeRange`, `Dimension.Temporal` |
| 19 | Perceptual/Cognitive | [ ] | — |
| 20 | Spatial Verbs | [~] | Various (transform, translate, etc.) |
| 21 | Spatial Adjectives | [~] | Various (bounded, active, etc.) |
| 22 | Fractal & Recursive | [~] | `Material.Noise*` (octaves, lacunarity) |
| 23 | Non-Euclidean | [ ] | — |
| 24 | Gesture & Touch | [x] | `Gestural.*`, `Gestural.Gesture.*` |
| 25 | Gaze & Attention | [ ] | — |
| 26 | Deictic (Pointing) | [ ] | — |
| 27 | Proxemics | [ ] | — |
| 28 | Wayfinding & Navigation | [~] | `Navigation.*`, `Router` |
| 29 | Architectural/Environmental | [ ] | — |
| 30 | Terrain & Landscape | [ ] | — |
| 31 | Fluid & Flow | [ ] | — |
| 32 | Particle & Swarm | [ ] | — |
| 33 | Light & Shadow | [~] | `Elevation.Shadow`, `Spatial.*` (PBR materials) |
| 34 | Acoustic/Sound Spatial | [~] | `Audio.*` |
| 35 | UI/UX Layout | [x] | `Dimension.Flex`, `Dimension.Spacing`, `Geometry.Spacing` |
| 36 | Stacking & Layering | [x] | `Elevation.ZIndex`, `Motion.Layer` |
| 37 | Selection & Focus | [x] | `Reactive.SelectionState`, `Gestural.Focus`, `Gestural.Selection` |
| 38 | Data Visualization | [~] | `Graph.*` |
| 39 | Network/Graph | [x] | `Graph.Layout`, `Graph.Connection`, `Graph.NodeContent` |
| 40 | Physics & Forces | [x] | `Physics.Force` |
| 41 | Collision & Contact | [x] | `Physics.Collision` |
| 42 | Constraints & Joints | [ ] | — |
| 43 | Skeleton & Rigging | [ ] | — |
| 44 | Procedural & Generative | [~] | `Material.Noise*` |
| 45 | Level of Detail (LOD) | [ ] | — |
| 46 | Wrap & Boundary Modes | [ ] | — |
| 47 | Interpolation & Sampling | [x] | `Motion.Interpolation`, `Motion.Easing` |
| 48 | Quantifiers & Comparatives | [ ] | — |
| 49 | Temporal-Spatial Events | [~] | `Gestural.Trigger`, `Reactive.*` |
| 50 | Multi-Agent / Swarm | [ ] | — |
| 51 | Semantic/Conceptual | [ ] | — |
| 52 | Emotional/Affective | [ ] | — |
| 53 | Camera & Cinematography | [x] | `Dimension.Camera`, `Motion.Camera3D` |
| 54 | VR/AR/XR Spatial | [ ] | — |
| 55 | Accessibility Spatial | [~] | `Reactive.FocusManagement`, A11y in components |
| 56 | Print & Publishing | [ ] | — |
| 57 | Color as Spatial | [x] | `Color.*` (full color system) |
| 58 | Mathematical Spatial | [~] | `Dimension.Vector.*`, `Geometry.*` |
| 59 | Quantum Spatial | [ ] | — |
| 60 | Domain-Specific | [~] | Medical terms in `Geometry.Position` |

**Summary:** 14 fully implemented [x], 24 partial [~], 22 not yet started [ ]

---

## 1. CARDINAL DIRECTIONS (Absolute Axes) [~]

### 1D (Linear)

- forward, backward
- ahead, behind
- positive, negative
- plus, minus

### 2D (Planar)

- up, down
- left, right
- north, south, east, west
- horizontal, vertical

### 3D (Volumetric)

- up, down, left, right, forward, backward
- above, below
- in, out
- depth, height, width

### 4D+ (Temporal/Hyper)

- ana, kata (4D directions)
- before, after (temporal)
- past, future
- inward, outward (through dimensions)

---

## 2. RELATIVE DIRECTIONS (Observer-Dependent) [~]

- front, back
- top, bottom
- side
- near, far
- close, distant
- proximal, distal
- medial, lateral
- dorsal, ventral
- anterior, posterior
- superior, inferior
- ipsilateral, contralateral
- clockwise, counterclockwise (widdershins)
- sunwise, antisunwise
- leeward, windward
- upstream, downstream
- uphill, downhill
- inboard, outboard

---

## 3. POSITIONAL RELATIONS [~]

### Containment

- inside, outside
- within, without
- internal, external
- interior, exterior
- enclosed, exposed
- contained, containing
- nested, enclosing
- surrounded, surrounding
- embedded, embedding
- immersed, submerged
- permeated, pervaded
- full, empty
- hollow, solid

### Adjacency

- adjacent, neighboring
- beside, alongside
- next to, by
- abutting, bordering
- flanking, straddling
- tangent, touching
- contiguous, continuous
- joined, connected
- attached, detached
- linked, unlinked
- coupled, decoupled
- docked, undocked

### Intersection

- intersecting, crossing
- overlapping, overlaid
- penetrating, piercing
- transecting, bisecting
- clipping, masked
- occluding, occluded
- coincident, congruent
- coplanar, collinear
- coaxial, concentric
- superimposed, layered

### Between/Among

- between, among
- amid, amidst
- intermediate, interstitial
- interspersed, scattered
- sandwiched, wedged
- interleaved, alternating
- spanning, bridging
- connecting, separating
- median, midway
- central, peripheral

### Alignment Relations

- aligned, misaligned
- flush, offset
- centered, off-center
- registered, unregistered
- snapped, floating
- anchored, free
- pinned, unpinned
- locked, unlocked
- constrained, unconstrained

---

## 4. TRANSFORMATIONS [x]

### Translation

- move, shift, slide
- translate, displace
- pan, scroll
- drag, push, pull
- nudge, inch
- glide, drift
- offset, relocate
- reposition, transfer

### Rotation

- rotate, spin, turn
- revolve, orbit
- pivot, swivel
- roll, pitch, yaw
- twist, wind, unwind
- coil, spiral
- tumble, somersault
- flip, invert
- gyrate, precess

### Scaling

- scale, resize
- enlarge, shrink
- expand, contract
- grow, diminish
- magnify, minify
- zoom, stretch
- compress, compact
- dilate, constrict
- uniform scale, non-uniform scale
- isotropic, anisotropic

### Reflection

- reflect, mirror
- flip horizontal, flip vertical
- invert, reverse
- transpose, permute
- symmetric, antisymmetric

### Shear

- shear, skew
- slant, tilt
- lean, incline
- oblique, distort
- parallelogram transform

### Compound Transforms

- affine, projective
- perspective, orthographic
- rigid (isometry)
- similarity
- conformal
- homeomorphism
- diffeomorphism
- matrix transform
- quaternion rotation

---

## 5. DEFORMATIONS [~]

### Bending

- bend, curve
- bow, arc
- flex, deflect
- warp, buckle
- crease, fold
- crimp, corrugate

### Twisting

- twist, torsion
- coil, helix
- corkscrew, spiral
- wring, contort

### Stretching

- stretch, elongate
- extend, lengthen
- expand, distend
- tense, taut
- elastic, plastic

### Compression

- compress, squeeze
- compact, condense
- crush, flatten
- crumple, collapse

### Morphing

- morph, metamorphose
- transform, transmute
- blend, interpolate
- tween, keyframe
- shape-shift

### Topology Changes

- punch, extrude
- boolean (union, difference, intersection)
- split, merge
- subdivide, tessellate
- bridge, fill
- inset, outset
- bevel, chamfer

---

## 6. GEOMETRIC PRIMITIVES [x]

### 0D (Points)

- point, vertex
- node, junction
- locus, position
- origin, centroid
- barycenter, circumcenter
- incenter, orthocenter
- focus, pole
- singularity, discontinuity

### 1D (Lines/Curves)

- line, ray, segment
- curve, arc
- edge, stroke
- path, trajectory
- axis, vector
- chord, tangent
- secant, normal
- asymptote, directrix
- geodesic, great circle
- Bezier, B-spline, NURBS
- helix, spiral
- catenary, parabola
- ellipse, hyperbola
- sine curve, cosine curve
- cycloid, epicycloid, hypocycloid
- Lissajous, parametric

### 2D (Surfaces)

- plane, face
- polygon, region
- disk, annulus
- triangle, quadrilateral
- pentagon, hexagon, heptagon, octagon
- regular polygon, irregular polygon
- convex, concave
- star polygon
- circle, ellipse
- sector, segment (arc)
- strip, ribbon
- mesh, grid
- surface patch
- ruled surface
- developable surface
- minimal surface
- Mobius strip, Klein bottle
- torus surface, sphere surface

### 3D (Volumes)

- cube, box, prism
- sphere, ellipsoid
- cylinder, cone
- pyramid, tetrahedron
- octahedron, dodecahedron, icosahedron
- frustum, capsule
- torus, toroid
- wedge, ramp
- convex hull, bounding box
- voxel, cell
- mesh volume, solid
- manifold, non-manifold
- watertight, open

### 4D+ (Hypersolids)

- tesseract, hypercube
- hypersphere, n-sphere
- simplex, n-simplex
- hyperprism, hyperfrustum
- cross-polytope
- 120-cell, 600-cell
- higher-dimensional polytopes

---

## 7. BOUNDARY & TOPOLOGY [~]

### Boundaries

- boundary, edge
- border, perimeter
- outline, contour
- rim, margin
- frame, fringe
- silhouette, profile
- hull, envelope
- skin, shell
- crust, rind
- membrane, film

### Topological Properties

- connected, disconnected
- simply connected, multiply connected
- genus (number of holes)
- orientable, non-orientable
- bounded, unbounded
- compact, open
- closed, clopen
- dense, sparse
- continuous, discontinuous
- manifold, non-manifold
- smooth, rough

### Topological Features

- hole, cavity
- tunnel, handle
- void, pocket
- island, peninsula
- isthmus, strait
- bridge, neck
- branch, fork
- loop, cycle
- tree, graph

---

## 8. COORDINATE SYSTEMS [x]

### Cartesian

- x, y, z axes
- origin
- unit vectors (i, j, k)
- quadrant, octant
- positive, negative direction

### Polar/Cylindrical/Spherical

- radius, angle
- theta, phi
- azimuth, elevation
- zenith, nadir
- latitude, longitude
- altitude, depth

### Specialized Systems

- barycentric, trilinear
- homogeneous, projective
- screen space, world space
- local space, object space
- view space, camera space
- NDC (normalized device coordinates)
- UV coordinates, texture space
- parametric (u, v, w)
- curvilinear coordinates
- Frenet-Serret frame

### Handedness

- right-handed, left-handed
- Y-up, Z-up
- clockwise, counter-clockwise winding

---

## 9. ORIENTATION & ALIGNMENT [~]

### Cardinal Orientation

- facing, pointing
- oriented, directed
- aimed, targeted
- headed, bound

### Alignment States

- aligned, misaligned
- parallel, perpendicular
- orthogonal, oblique
- collinear, coplanar
- concentric, eccentric
- tangent, secant
- normal, binormal

### Relative Orientation

- same direction, opposite direction
- facing each other, facing away
- side by side, back to back
- head to tail, end to end
- upright, inverted
- prone, supine
- portrait, landscape

### Angular Alignment

- level, tilted
- plumb, vertical
- horizontal, diagonal
- inclined, declined
- canted, askew
- square, true
- skewed, warped

---

## 10. SYMMETRY [x]

### Reflection Symmetry

- bilateral, mirror
- line symmetry, plane symmetry
- left-right symmetric, top-bottom symmetric
- radial symmetry, point symmetry

### Rotational Symmetry

- n-fold rotational (2-fold, 3-fold, 4-fold, 6-fold)
- cyclic symmetry
- dihedral symmetry
- continuous rotational symmetry (circular)

### Translational Symmetry

- periodic, repeating
- tiled, tessellated
- lattice, grid
- frieze, wallpaper

### Other Symmetries

- glide reflection
- screw symmetry
- helical symmetry
- scale symmetry (self-similar)
- conformal symmetry
- chiral, achiral
- enantiomer, mirror image

### Symmetry Breaking

- asymmetric, irregular
- broken symmetry
- perturbed, distorted
- spontaneous symmetry breaking

---

## 11. DISTRIBUTION & ARRANGEMENT [~]

### Regular Patterns

- uniform, evenly spaced
- regular, periodic
- grid, matrix
- lattice, array
- row, column
- stacked, layered
- tiled, tessellated

### Irregular Patterns

- random, scattered
- irregular, aperiodic
- clustered, clumped
- sparse, dense
- patchy, mottled
- dispersed, distributed

### Clustering

- grouped, clustered
- aggregated, collected
- concentrated, focal
- centered, peripheral
- core, fringe
- nucleus, satellite

### Spacing

- spaced, gapped
- touching, overlapping
- crowded, uncrowded
- packed, loose
- tight, slack
- margin, padding
- gutter, alley

### Arrangement Patterns

- radial, concentric
- spiral, helical
- branching, dendritic
- network, web
- chain, sequence
- ring, loop
- star, hub-and-spoke
- tree, hierarchy
- random walk, Brownian

---

## 12. MOTION & KINEMATICS [x]

### Linear Motion

- moving, stationary
- velocity, speed
- acceleration, deceleration
- momentum, inertia
- trajectory, path
- displacement, distance
- approaching, receding
- advancing, retreating

### Rotational Motion

- rotating, spinning
- angular velocity, RPM
- torque, moment
- precession, nutation
- wobble, oscillation

### Oscillatory Motion

- vibrating, oscillating
- swinging, pendulum
- pulsing, throbbing
- bouncing, rebounding
- resonating, harmonic

### Complex Motion

- orbiting, revolving
- spiraling, helical motion
- chaotic, random
- Brownian, diffusive
- wave motion, undulation
- propagating, radiating

### Motion States

- accelerating, decelerating
- constant velocity, at rest
- free-falling, ballistic
- constrained, guided
- damped, driven
- periodic, aperiodic

### Motion Verbs

- glide, slide, slip
- roll, tumble, bounce
- float, drift, wander
- rush, dart, zoom
- creep, crawl, inch
- leap, jump, hop
- swing, sway, rock
- vibrate, shake, tremble
- pulsate, throb, beat
- flow, stream, pour

---

## 13. FIELDS & GRADIENTS [~]

### Scalar Fields

- density, concentration
- temperature, pressure
- potential, energy
- height map, elevation
- distance field, SDF
- probability, distribution

### Vector Fields

- velocity field, flow
- force field, gravitational
- electric, magnetic
- gradient, curl, divergence
- flux, circulation
- streamlines, field lines

### Gradient Properties

- gradient direction, steepest ascent
- gradient magnitude, slope
- level set, isoline, isosurface
- contour, isobar, isotherm
- saddle point, local extremum
- plateau, valley, ridge

### Field Operations

- sampling, interpolating
- integrating, differentiating
- convolving, filtering
- advecting, transporting
- diffusing, dissipating

---

## 14. PROJECTIONS [~]

### Parallel Projections

- orthographic, orthogonal
- top view, front view, side view
- plan, elevation, section
- isometric, dimetric, trimetric
- axonometric, cabinet, cavalier

### Perspective Projections

- one-point, two-point, three-point
- vanishing point, horizon line
- foreshortening, convergence
- field of view, focal length
- near plane, far plane

### Map Projections

- Mercator, equirectangular
- stereographic, gnomonic
- conic, cylindrical, azimuthal
- conformal, equal-area
- compromise projection

### Other Projections

- fisheye, barrel
- spherical, cubemap
- panoramic, 360-degree
- shadow projection, silhouette
- flattening, unfolding

---

## 15. MEASUREMENT & METRICS [x]

### Linear Measures

- length, width, height
- depth, thickness
- radius, diameter
- circumference, perimeter
- distance, span
- gap, clearance

### Area Measures

- area, surface area
- cross-section, footprint
- coverage, extent
- acreage, square footage

### Volume Measures

- volume, capacity
- displacement, bulk
- cubic content

### Angular Measures

- angle, degree, radian
- steradian (solid angle)
- arc length, arc measure
- bearing, heading
- pitch, roll, yaw
- inclination, declination

### Derived Measures

- aspect ratio
- curvature, radius of curvature
- torsion, twist rate
- slope, grade, pitch
- density, concentration
- resolution, granularity

### Comparison Metrics

- ratio, proportion
- scale factor, magnification
- similarity, congruence
- deviation, error
- tolerance, precision

---

## 16. COMPOSITIONAL OPERATIONS (CSG) [~]

### Boolean Operations

- union, combine, add
- intersection, common, and
- difference, subtract, cut
- exclusive or, symmetric difference

### Blending

- blend, smooth union
- fillet, round
- chamfer, bevel
- interpolate, morph

### Decomposition

- split, divide
- partition, segment
- slice, section
- explode, disassemble
- fracture, shatter

### Assembly

- assemble, compose
- join, weld
- merge, fuse
- aggregate, collect
- nest, embed

---

## 17. NESTING & HIERARCHY [~]

### Containment Hierarchy

- parent, child
- ancestor, descendant
- root, leaf
- branch, node
- level, depth
- nested, recursive

### Grouping

- group, ungroup
- cluster, partition
- collection, set
- bundle, package
- composite, atomic

### Hierarchical Relations

- contains, contained by
- owns, owned by
- encapsulates, exposes
- inherits, overrides
- delegates, defers

### Scope

- local, global
- inner, outer
- private, public
- isolated, shared

---

## 18. TEMPORAL-SPATIAL (4D) [~]

### Time as Dimension

- world-line, history
- space-time, Minkowski
- past light cone, future light cone
- simultaneity, relativity
- proper time, coordinate time

### Temporal Evolution

- evolving, changing
- growing, shrinking
- aging, decaying
- emerging, vanishing
- appearing, disappearing

### Motion Through Time

- trajectory, orbit
- path integral, world tube
- sweep, extrusion over time
- trail, wake, trace

### Temporal Slicing

- snapshot, frame
- keyframe, in-between
- temporal slice, time-slice
- moment, instant
- duration, interval

---

## 19. PERCEPTUAL/COGNITIVE SPATIAL [ ]

### Visual Perception

- visible, invisible
- apparent, illusory
- perceived size, perceived distance
- parallax, depth cue
- occlusion, overlap
- figure-ground, gestalt

### Spatial Cognition

- mental map, cognitive map
- landmark, route, survey
- egocentric, allocentric
- viewpoint-dependent, viewpoint-invariant
- spatial memory, spatial reasoning

### Attention & Saliency

- salient, prominent
- focal, peripheral
- attended, ignored
- highlighted, dimmed
- foregrounded, backgrounded

### Spatial Language

- here, there
- this, that
- yonder, hence
- hither, thither
- whence, whither

---

## 20. SPATIAL VERBS (Actions) [~]

### Placement

- place, put, set
- position, locate
- arrange, organize
- install, mount
- deposit, lay

### Movement

- move, shift, transfer
- carry, transport
- push, pull, drag
- lift, lower, raise
- drop, release, let go

### Orientation

- orient, align, face
- point, aim, direct
- turn, rotate, pivot
- tilt, tip, lean
- level, straighten

### Transformation

- transform, modify
- reshape, reform
- deform, distort
- stretch, compress
- scale, resize

### Connection

- connect, join, link
- attach, fasten, bind
- couple, dock, mate
- anchor, fix, secure
- tether, tie, lash

### Separation

- separate, divide, split
- detach, disconnect, unlink
- cut, sever, break
- remove, extract, pull out
- peel, strip, shed

### Traversal

- traverse, cross, pass through
- enter, exit, penetrate
- climb, descend, ascend
- approach, depart, leave
- arrive, reach, attain

---

## 21. SPATIAL ADJECTIVES (States) [~]

### Size

- large, small
- big, little
- huge, tiny
- vast, minuscule
- massive, minute
- enormous, microscopic
- gigantic, diminutive

### Shape Quality

- round, angular
- curved, straight
- smooth, rough
- flat, bumpy
- regular, irregular
- uniform, varied
- symmetric, asymmetric

### Spatial Extent

- wide, narrow
- thick, thin
- long, short
- tall, squat
- deep, shallow
- broad, slim
- expansive, compact

### Position Quality

- central, peripheral
- inner, outer
- upper, lower
- front, rear
- left, right
- near, far
- high, low

### Arrangement Quality

- ordered, disordered
- organized, chaotic
- neat, messy
- aligned, scattered
- structured, amorphous
- patterned, random

### Boundary Quality

- open, closed
- bounded, unbounded
- enclosed, exposed
- sealed, porous
- solid, hollow

---

## 22. FRACTAL & RECURSIVE SPATIAL [~]

### Self-Similarity

- self-similar, fractal
- recursive, nested
- hierarchical, multi-scale
- scale-invariant, power-law
- iterated, repeated

### Fractal Structures

- Mandelbrot, Julia set
- Sierpinski (triangle, carpet, gasket)
- Koch (snowflake, curve)
- Cantor (set, dust)
- Menger sponge
- dragon curve
- Hilbert curve, Peano curve
- L-system, Lindenmayer

### Fractal Properties

- fractal dimension, Hausdorff dimension
- lacunarity, gaps
- roughness, complexity
- branching ratio, bifurcation
- infinite detail, finite area

---

## 23. NON-EUCLIDEAN SPATIAL [ ]

### Curved Spaces

- spherical geometry, elliptic
- hyperbolic geometry, Lobachevskian
- Riemannian, curved manifold
- geodesic, shortest path
- parallel transport, holonomy

### Topological Spaces

- Mobius strip, one-sided
- Klein bottle, non-orientable
- torus, doughnut
- projective plane
- handle, cross-cap

### Unusual Geometries

- taxicab geometry, Manhattan distance
- Chebyshev distance, chessboard
- Minkowski space, spacetime
- conformal geometry, angle-preserving
- affine geometry, parallel-preserving
- projective geometry, incidence

### Warp & Distortion

- warped space, curved
- folded space, wormhole
- stretched, compressed
- twisted, knotted
- inside-out, inverted

---

## 24. GESTURE & TOUCH (Human Input) [x]

### Touch Types

- tap, touch
- press, hold
- double-tap, triple-tap
- long press, force touch
- hover, proximity

### Drag Gestures

- drag, swipe
- pan, scroll
- flick, fling
- slide, glide
- pull, push

### Multi-Touch

- pinch, spread
- zoom in, zoom out
- rotate (two-finger)
- two-finger tap
- three-finger swipe

### Complex Gestures

- draw, trace
- circle, lasso
- zigzag, wave
- shake, tilt
- throw, catch

### Touch Properties

- touch point, contact area
- pressure, force
- velocity, acceleration
- touch duration
- touch count, finger count

---

## 25. GAZE & ATTENTION [ ]

### Gaze Direction

- looking at, gazing
- staring, glancing
- fixating, scanning
- tracking, following
- averting, avoiding

### Eye Movements

- saccade, fixation
- smooth pursuit
- vergence, divergence
- blink, squint
- pupil dilation, constriction

### Attention Spatial

- attended region, focus
- peripheral awareness
- blind spot, scotoma
- visual field, field of view
- foveal, parafoveal, peripheral

### Visual Search

- searching, scanning
- finding, locating
- missing, overlooking
- noticing, detecting
- recognizing, identifying

---

## 26. DEICTIC (Pointing/Reference) [ ]

### Demonstratives

- this, that
- these, those
- here, there
- yonder, over there

### Spatial Deictics

- hither, thither
- hence, thence
- whence, whither
- herein, therein

### Relational Reference

- the one on the left
- the one above
- the nearest one
- the one in front
- the bigger one
- the red one (deictic + attribute)

### Pointing

- point, indicate
- gesture toward, motion to
- nod toward, look at
- reference, refer to
- designate, identify

---

## 27. PROXEMICS (Social Space) [ ]

### Personal Space Zones

- intimate distance (0-18 inches)
- personal distance (18 inches - 4 feet)
- social distance (4-12 feet)
- public distance (12+ feet)

### Social Spatial Relations

- crowded, spacious
- close, distant
- invading, respecting
- approaching, withdrawing
- encroaching, retreating

### Territorial

- territory, domain
- boundary, border
- personal space, bubble
- claimed, unclaimed
- defended, open

### Orientation (Social)

- facing, turned away
- side by side, face to face
- behind, in front of
- shoulder to shoulder
- back to back

---

## 28. WAYFINDING & NAVIGATION [~]

### Navigation Elements

- path, route
- landmark, waypoint
- destination, origin
- intersection, junction
- turn, corner
- straight, curved

### Directions (Navigation)

- turn left, turn right
- go straight, continue
- go back, return
- follow, proceed
- bear left, veer right

### Spatial Strategies

- route knowledge, turn-by-turn
- survey knowledge, map-based
- landmark navigation
- dead reckoning
- path integration

### Navigation States

- oriented, disoriented
- lost, found
- on track, off track
- arrived, en route
- approaching, departing

### Wayfinding Elements

- sign, marker
- map, compass
- beacon, guide
- trail, breadcrumb
- signpost, milestone

---

## 29. ARCHITECTURAL/ENVIRONMENTAL [ ]

### Building Elements

- wall, floor, ceiling
- roof, foundation
- door, window
- stair, ramp, elevator
- column, beam, arch

### Rooms & Spaces

- room, chamber
- hall, corridor
- lobby, foyer
- atrium, courtyard
- basement, attic

### Architectural Features

- entrance, exit
- threshold, doorway
- alcove, niche
- bay, projection
- balcony, terrace
- porch, veranda

### Spatial Qualities

- spacious, cramped
- open plan, partitioned
- high-ceilinged, low-ceilinged
- well-lit, dim
- airy, stuffy

### Urban Elements

- street, avenue, boulevard
- block, lot, parcel
- plaza, square, park
- intersection, corner
- sidewalk, curb
- alley, passage

---

## 30. TERRAIN & LANDSCAPE [ ]

### Elevation Features

- mountain, hill
- peak, summit
- ridge, crest
- valley, dale
- canyon, gorge
- cliff, escarpment
- plateau, mesa
- plain, flat

### Water Features

- river, stream, brook
- lake, pond, pool
- ocean, sea
- bay, inlet, cove
- delta, estuary
- waterfall, cascade
- spring, well

### Landforms

- island, peninsula
- isthmus, cape
- beach, shore
- dune, sandbar
- glacier, iceberg
- volcano, crater
- cave, cavern

### Vegetation Regions

- forest, woods
- jungle, rainforest
- desert, tundra
- grassland, prairie
- wetland, marsh, swamp
- meadow, field

### Terrain Properties

- steep, gentle
- rugged, smooth
- arid, lush
- barren, fertile
- rocky, sandy
- muddy, solid

---

## 31. FLUID & FLOW [ ]

### Flow Types

- laminar, turbulent
- steady, unsteady
- uniform, non-uniform
- compressible, incompressible
- viscous, inviscid

### Flow Patterns

- stream, current
- eddy, vortex
- whirlpool, maelstrom
- wake, turbulence
- jet, plume
- fountain, spray

### Flow Properties

- velocity, flow rate
- pressure, density
- viscosity, surface tension
- Reynolds number
- Mach number

### Fluid Motion Verbs

- flow, stream, pour
- gush, spurt, squirt
- drip, trickle, seep
- splash, spray, mist
- swirl, whirl, eddy
- surge, flood, cascade

### Fluid Boundaries

- surface, interface
- meniscus, droplet
- bubble, foam
- wave, ripple
- crest, trough

---

## 32. PARTICLE & SWARM [ ]

### Individual Particles

- particle, point mass
- atom, molecule
- grain, speck
- droplet, bubble
- cell, agent

### Collective Behavior

- swarm, flock
- herd, school
- cloud, cluster
- crowd, mob
- colony, population

### Swarm Patterns

- flocking, schooling
- swarming, clustering
- dispersing, scattering
- aggregating, coalescing
- migrating, streaming

### Particle Properties

- position, velocity
- mass, charge
- lifetime, age
- size, color
- spin, orientation

### Particle Systems

- emitter, source
- attractor, repeller
- force field, potential
- collision, bounce
- spawn, die

---

## 33. LIGHT & SHADOW [~]

### Light Sources

- point light, directional light
- spot light, area light
- ambient light, environment light
- emissive, luminous

### Light Properties

- brightness, intensity
- color temperature, hue
- falloff, attenuation
- beam angle, cone angle
- soft, hard

### Shadow Types

- hard shadow, soft shadow
- umbra, penumbra
- cast shadow, drop shadow
- self-shadow, contact shadow
- ambient occlusion

### Illumination

- lit, unlit
- illuminated, shaded
- highlighted, shadowed
- backlit, frontlit
- rimlit, silhouetted

### Light Interactions

- reflection, refraction
- diffuse, specular
- glossy, matte
- translucent, transparent
- caustic, subsurface scattering

### Shadow Spatial

- shadow direction, shadow length
- shadow projection
- shadowed region, light region
- penumbral gradient
- shadow boundary

---

## 34. ACOUSTIC/SOUND SPATIAL [~]

### Sound Sources

- point source, line source
- area source, volume source
- omnidirectional, directional
- near-field, far-field

### Sound Propagation

- propagating, radiating
- reflecting, absorbing
- diffracting, scattering
- attenuating, decaying
- reverberating, echoing

### Acoustic Spaces

- anechoic, reverberant
- enclosed, open
- live, dead (acoustically)
- resonant, damped

### Spatial Audio

- stereo, surround
- binaural, ambisonics
- 3D audio, spatial audio
- HRTF, head-related
- panning, positioning

### Sound Location

- sound direction, sound source location
- sound distance, loudness cue
- Doppler shift, motion cue
- interaural time difference
- interaural level difference

---

## 35. UI/UX LAYOUT [x]

### Layout Models

- flow, inline
- block, flex
- grid, table
- absolute, relative
- fixed, sticky

### Alignment

- left-aligned, right-aligned
- center-aligned, justified
- top-aligned, bottom-aligned
- baseline-aligned
- stretch, fit

### Spacing

- margin, padding
- gap, gutter
- indent, outdent
- leading, tracking
- whitespace, negative space

### Responsive

- responsive, adaptive
- fluid, fixed
- breakpoint, media query
- mobile-first, desktop-first
- collapsing, expanding

### Layout Elements

- container, wrapper
- row, column
- cell, slot
- sidebar, main content
- header, footer
- drawer, panel

---

## 36. STACKING & LAYERING (Z-Order) [x]

### Stack Order

- front, back
- top, bottom
- foreground, background
- above, below
- over, under

### Z-Index

- z-index, stacking context
- elevated, sunken
- raised, lowered
- overlapping, underlapping
- on top, beneath

### Layer Types

- base layer, overlay
- mask, clip
- blend, composite
- transparent, opaque
- visible, hidden

### Layer Operations

- bring to front, send to back
- bring forward, send backward
- stack, unstack
- flatten, merge
- isolate, group

---

## 37. SELECTION & FOCUS STATES [x]

### Selection States

- selected, unselected
- highlighted, unhighlighted
- active, inactive
- focused, unfocused
- hovered, unhovered

### Selection Modes

- single select, multi-select
- range select, lasso select
- toggle select, additive select
- exclusive select, inclusive select

### Selection Feedback

- selection indicator, highlight
- selection box, marquee
- outline, glow
- checkbox, radio
- cursor change

### Focus Spatial

- focus ring, focus indicator
- focus trap, focus scope
- tab order, focus order
- skip link, focus bypass
- roving tabindex

---

## 38. DATA VISUALIZATION SPATIAL [~]

### Chart Axes

- x-axis, y-axis, z-axis
- horizontal axis, vertical axis
- primary axis, secondary axis
- categorical, continuous
- linear, logarithmic

### Chart Elements

- plot area, chart area
- legend, title
- label, annotation
- gridline, tick mark
- axis line, baseline

### Data Points

- data point, marker
- bar, column
- slice, segment
- node, link
- bubble, dot

### Visual Encodings

- position, length
- angle, area
- color, shape
- size, texture
- orientation, curvature

### Chart Types Spatial

- scatter plot, bubble chart
- line chart, area chart
- bar chart, histogram
- pie chart, donut chart
- treemap, sunburst
- network graph, force layout
- choropleth, cartogram
- heatmap, contour plot

---

## 39. NETWORK/GRAPH SPATIAL [x]

### Graph Elements

- node, vertex
- edge, link
- cluster, community
- hub, spoke
- root, leaf

### Graph Topology

- connected, disconnected
- directed, undirected
- weighted, unweighted
- cyclic, acyclic
- tree, DAG
- bipartite, multipartite

### Graph Layout

- force-directed, spring
- hierarchical, tree layout
- circular, radial
- grid, matrix
- orthogonal, layered

### Graph Properties

- degree, centrality
- path, shortest path
- diameter, radius
- density, sparsity
- clustering coefficient

### Graph Operations

- expand, collapse
- filter, highlight
- zoom, pan
- cluster, partition
- bundle, route

---

## 40. PHYSICS & FORCES [x]

**Implemented:** `Hydrogen.Schema.Physics.Force`

### Force Types

- gravitational, electromagnetic
- contact, friction
- spring, elastic
- drag, resistance
- buoyancy, lift

### Force Properties

- magnitude, direction
- applied, resultant
- balanced, unbalanced
- attractive, repulsive
- centripetal, centrifugal

### Physical States

- static, dynamic
- equilibrium, disequilibrium
- stable, unstable
- rigid, flexible
- elastic, plastic

### Energy Spatial

- potential energy (height)
- kinetic energy (motion)
- stored, released
- transferred, dissipated
- conserved, lost

### Physical Quantities

- mass, weight
- force, torque
- momentum, impulse
- energy, work
- power, pressure

---

## 41. COLLISION & CONTACT [x]

**Implemented:** `Hydrogen.Schema.Physics.Collision`

### Collision Types

- intersection, overlap
- penetration, interpenetration
- collision, impact
- contact, touch
- separation, clearance

### Collision Response

- bounce, rebound
- slide, friction
- stick, grab
- deform, crush
- shatter, break

### Collision Geometry

- bounding box, AABB
- bounding sphere
- convex hull
- mesh collider
- capsule, cylinder

### Contact Properties

- contact point, contact normal
- contact area, contact patch
- penetration depth
- separation distance
- contact force, impulse

### Collision States

- colliding, separating
- resting, sliding
- rolling, spinning
- stuck, lodged
- free, constrained

---

## 42. CONSTRAINTS & JOINTS [ ]

### Constraint Types

- distance constraint, spring
- hinge, revolute
- ball joint, spherical
- prismatic, slider
- fixed, welded

### Constraint Properties

- limit, range
- stiffness, damping
- friction, motor
- locked, free
- breaking force

### Complex Joints

- universal joint, cardan
- cone twist
- ragdoll, character
- gear, pulley
- rack and pinion

### Constraint Behaviors

- constrained, unconstrained
- rigid, soft
- elastic, inelastic
- over-constrained, under-constrained
- satisfied, violated

---

## 43. SKELETON & RIGGING [ ]

### Skeletal Elements

- bone, joint
- root bone, end effector
- parent bone, child bone
- spine, limb
- digit, phalange

### Rigging Concepts

- bind pose, rest pose
- skinning, weighting
- deformation, influence
- blend shape, morph target
- IK (inverse kinematics), FK (forward kinematics)

### Animation Rigging

- control, handle
- driver, driven
- constraint, target
- pole vector, aim
- twist, roll

### Body Regions

- head, neck
- torso, chest, abdomen
- shoulder, arm, forearm
- hand, finger
- hip, thigh, shin
- foot, toe

---

## 44. PROCEDURAL & GENERATIVE [~]

### Generation Methods

- procedural, algorithmic
- generative, parametric
- random, stochastic
- deterministic, seeded
- rule-based, grammar

### Procedural Patterns

- noise (Perlin, Simplex, Worley)
- fractal, subdivision
- L-system, growth
- cellular automata
- Voronoi, Delaunay

### Procedural Operations

- generate, spawn
- grow, propagate
- branch, split
- mutate, vary
- iterate, recurse

### Control Parameters

- seed, randomness
- frequency, amplitude
- octaves, lacunarity
- persistence, falloff
- threshold, cutoff

---

## 45. LEVEL OF DETAIL (LOD) [ ]

### LOD Levels

- high detail, low detail
- full resolution, simplified
- near LOD, far LOD
- LOD 0, LOD 1, LOD 2, etc.

### LOD Techniques

- mesh simplification, decimation
- impostor, billboard
- mip-mapping, texture LOD
- geometric LOD, shader LOD
- HLOD (hierarchical LOD)

### LOD Transitions

- discrete LOD, pop
- continuous LOD, geomorphing
- blending, cross-fade
- hysteresis, threshold

### LOD Criteria

- distance-based, screen-size
- importance, priority
- performance budget
- error metric, fidelity

---

## 46. WRAP & BOUNDARY MODES [ ]

### Wrap Modes

- repeat, tile
- mirror, reflect
- clamp, edge
- border, constant
- wrap around

### Boundary Behaviors

- periodic, cyclic
- bounded, finite
- infinite, unbounded
- toroidal, cylindrical
- spherical, planar

### Edge Handling

- extend, extrapolate
- cut, clip
- fade, feather
- blend, smooth
- hard edge, soft edge

---

## 47. INTERPOLATION & SAMPLING [x]

### Interpolation Methods

- nearest neighbor, point
- linear, bilinear, trilinear
- cubic, bicubic, tricubic
- spline, B-spline, Catmull-Rom
- Hermite, Bezier

### Sampling

- regular, uniform
- random, stochastic
- stratified, jittered
- Poisson disk
- importance sampling

### Interpolation Properties

- continuous, discontinuous
- smooth, sharp
- C0, C1, C2 continuity
- overshoot, undershoot
- tension, bias, continuity

### Sampling Artifacts

- aliasing, moiré
- banding, quantization
- blur, sharpening
- ringing, Gibbs
- noise, grain

---

## 48. QUANTIFIERS & COMPARATIVES [ ]

### Quantifiers

- all, none, some
- every, any
- most, few
- many, several
- each, both
- neither, either

### Comparative Spatial

- larger than, smaller than
- closer than, farther than
- higher than, lower than
- wider than, narrower than
- more, less
- equal, unequal

### Superlatives

- largest, smallest
- nearest, farthest
- highest, lowest
- widest, narrowest
- most, least
- best, worst (quality)

### Approximate Quantities

- approximately, roughly
- about, around
- nearly, almost
- exactly, precisely
- somewhat, slightly

---

## 49. TEMPORAL-SPATIAL EVENTS [~]

### Event Types

- appear, disappear
- enter, exit
- arrive, depart
- start, stop
- begin, end

### Spatial Triggers

- cross boundary, enter region
- leave region, reach point
- collide, separate
- approach, recede
- intersect, overlap

### Event Timing

- instant, moment
- duration, interval
- before, after
- during, while
- simultaneous, sequential

### Event Sequences

- first, last
- next, previous
- initial, final
- intermediate, transitional
- repeating, one-time

---

## 50. MULTI-AGENT / SWARM INTELLIGENCE [ ]

### Agent Properties

- position, velocity
- heading, orientation
- state, behavior
- perception, awareness
- communication range

### Collective Behaviors

- flocking, schooling
- swarming, herding
- formation, pattern
- consensus, agreement
- emergent, self-organized

### Agent Interactions

- attraction, repulsion
- alignment, cohesion
- avoidance, separation
- following, leading
- cooperation, competition

### Swarm Patterns

- V-formation, line
- cluster, dispersed
- ring, sphere
- grid, lattice
- random, chaotic

### Agent Communication

- local, global
- broadcast, directed
- stigmergy, pheromone
- signal, message
- sensing, perceiving

---

## 51. SEMANTIC/CONCEPTUAL SPATIAL (Metaphor) [ ]

### Spatial Metaphors

- up is good, down is bad
- forward is future, backward is past
- close is similar, far is different
- high status, low status
- in-group, out-group

### Conceptual Spaces

- idea space, concept space
- solution space, search space
- parameter space, feature space
- state space, phase space
- design space, possibility space

### Abstract Position

- central idea, peripheral concern
- at the core, on the fringe
- mainstream, marginal
- inside the box, outside the box
- on track, off course

### Knowledge Geography

- domain, field, area
- frontier, boundary
- landscape, terrain (of ideas)
- map, territory
- path, journey (of learning)

---

## 52. EMOTIONAL/AFFECTIVE SPATIAL [ ]

### Emotional Distance

- close, distant (emotionally)
- connected, disconnected
- warm, cold
- open, closed
- approaching, withdrawing

### Comfort Zones

- comfort zone, stretch zone
- safe space, danger zone
- familiar, unfamiliar
- welcoming, threatening
- inclusive, exclusive

### Emotional States (Spatial)

- elevated, depressed
- expansive, constricted
- grounded, ungrounded
- centered, scattered
- balanced, off-balance

### Social-Emotional Space

- in-group, out-group
- insider, outsider
- belonging, alienation
- embrace, rejection
- acceptance, exclusion

---

## 53. CAMERA & CINEMATOGRAPHY [x]

### Camera Position

- camera position, viewpoint
- eye level, low angle, high angle
- Dutch angle, canted
- bird's eye, worm's eye
- over the shoulder, POV

### Camera Movement

- pan, tilt
- dolly, truck
- boom, crane
- zoom, push
- pull, rack focus
- handheld, steadicam

### Shot Types

- extreme close-up, close-up
- medium shot, full shot
- wide shot, extreme wide
- establishing shot
- insert, cutaway

### Framing

- centered, off-center
- rule of thirds
- headroom, lead room
- negative space
- frame within frame

### Depth of Field

- shallow DOF, deep DOF
- bokeh, blur
- in focus, out of focus
- focal plane, hyperfocal
- rack focus, pull focus

---

## 54. VR/AR/XR SPATIAL [ ]

### Virtual Spaces

- virtual environment, scene
- world space, local space
- play area, guardian boundary
- teleport, locomotion
- room-scale, seated, standing

### Presence & Immersion

- presence, immersion
- embodiment, avatar
- virtual body, virtual hand
- proprioception, body ownership
- simulation sickness, VR comfort

### AR Spatial

- anchor, world anchor
- surface detection, plane
- occlusion, depth
- spatial mapping, mesh
- marker, markerless

### XR Interaction

- ray casting, pointer
- grab, pinch, poke
- gaze cursor, head tracking
- hand tracking, gesture
- controller, haptic

### Spatial Audio (XR)

- spatialized sound, 3D audio
- head-locked, world-locked
- directional, ambient
- proximity-based
- audio occlusion

---

## 55. ACCESSIBILITY SPATIAL [~]

### Screen Reader Spatial

- reading order, focus order
- heading structure, landmark
- skip link, bypass
- breadcrumb, navigation
- alt text, description

### Magnification

- zoom level, magnification
- pan, scroll
- viewport, visible area
- target size, touch target
- spacing, minimum size

### Color & Contrast

- contrast ratio, luminance
- color blindness considerations
- pattern, texture (alternative)
- focus indicator, highlight

### Spatial Alternatives

- audio description, narration
- haptic feedback, vibration
- braille, tactile
- simplified layout
- reduced motion

### Cognitive Spatial

- clear hierarchy, organization
- consistent layout, predictable
- reduced clutter, whitespace
- chunking, grouping
- progressive disclosure

---

## 56. PRINT & PUBLISHING SPATIAL [ ]

### Page Geometry

- page size, paper size
- portrait, landscape
- bleed, trim, safe area
- gutter, spine
- margin (top, bottom, left, right)

### Typography Layout

- column, grid
- baseline grid, leading
- indent, hanging indent
- orphan, widow
- hyphenation, justification

### Print Elements

- header, footer
- page number, folio
- running head, chapter title
- footnote, endnote
- figure, caption

### Binding & Assembly

- spread, facing pages
- signature, section
- fold, crease
- perfect bound, saddle stitch
- case bound, paperback

### Color (Print)

- CMYK, spot color
- registration, knock out
- overprint, trapping
- halftone, screen
- ink coverage, density

---

## 57. COLOR AS SPATIAL [x]

### Color Position

- color wheel position, hue angle
- warm colors advance, cool colors recede
- light colors expand, dark colors contract
- saturated colors vibrate
- complementary tension

### Color Distance

- color difference, delta E
- perceptual distance, JND
- similar, contrasting
- harmonious, discordant
- gradient, transition

### Color Space (3D)

- color space, gamut
- RGB cube, HSL cylinder
- LAB, OKLCH
- color solid, color volume
- out of gamut, clipped

### Color Perception

- simultaneous contrast
- color constancy
- chromatic adaptation
- afterimage
- color illusion

---

## 58. MATHEMATICAL SPATIAL [~]

### Set Theory

- set, subset, superset
- union, intersection, complement
- element, member
- empty set, universal set
- Venn diagram, Euler diagram

### Topology

- open set, closed set
- compact, connected
- continuous, homeomorphic
- manifold, boundary
- genus, Betti numbers

### Linear Algebra

- vector space, basis
- span, subspace
- linear transformation, matrix
- eigenvalue, eigenvector
- inner product, norm

### Analysis

- neighborhood, ball, sphere
- open, closed (topology)
- limit, convergence
- continuous, differentiable
- measure, integral

### Geometry Types

- Euclidean, non-Euclidean
- affine, projective
- differential, algebraic
- computational, discrete
- convex, combinatorial

---

## 59. QUANTUM SPATIAL [ ]

### Quantum States

- superposition, entanglement
- coherent, decoherent
- localized, delocalized
- collapsed, measured
- probable, uncertain

### Quantum Geometry

- wave function, probability density
- orbital, shell
- tunneling, barrier
- quantum well, quantum dot
- band structure

### Uncertainty

- position uncertainty, momentum uncertainty
- Heisenberg principle
- measurement disturbance
- observer effect

### Quantum Phenomena

- interference, diffraction
- wave-particle duality
- zero-point, vacuum fluctuation
- Casimir effect
- quantum foam

---

## 60. DOMAIN-SPECIFIC SPATIAL [~]

### Medical/Anatomical

- anterior, posterior
- superior, inferior
- medial, lateral
- proximal, distal
- dorsal, ventral
- sagittal, coronal, transverse
- supine, prone
- ipsilateral, contralateral

### Crystallography

- lattice, unit cell
- crystal system (cubic, tetragonal, etc.)
- Miller indices
- Bravais lattice
- symmetry operations
- space group

### Astronomy

- celestial coordinates
- right ascension, declination
- azimuth, altitude
- ecliptic, equatorial
- galactic coordinates
- parallax, proper motion

### Music/Sound

- pitch space, frequency
- harmonic series
- interval, step
- register (high, low)
- stereo field, pan
- depth (reverb)

### Dance/Movement

- stage directions (upstage, downstage)
- stage left, stage right
- center stage, wings
- level (high, middle, low)
- pathway, floor pattern
- shape, body architecture

### Sports

- field of play, court, pitch
- goal, end zone
- baseline, sideline
- center court, corner
- lane, track
- formation, position

### Military

- flank, rear
- perimeter, salient
- advance, retreat
- theater, front
- high ground, terrain advantage
- enfilade, defilade

### Maritime

- port, starboard
- bow, stern
- fore, aft
- amidships
- windward, leeward
- bearing, heading

### Aviation

- pitch, roll, yaw
- attitude, heading
- altitude, flight level
- approach, departure
- runway, taxiway
- airspace, corridor

---

## Notes

This document is now complete with all 60 sections cataloging spatial vocabulary
for billion-agent communication. When implementing these as Hydrogen atoms, each
concept should receive:

- Bounded type with clear semantics
- Smart constructors with validation
- Named constants for common values
- Documentation explaining physical/perceptual meaning

Last Updated: 2026-02-24
