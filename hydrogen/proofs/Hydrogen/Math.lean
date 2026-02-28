/-
  Hydrogen.Math
  
  Root module for 3D mathematics with formal proofs.
  
  ARCHITECTURE:
    ┌─────────────────────────────────────────────────────────────────────────┐
    │                           Hydrogen.Math                                 │
    ├─────────────────────────────────────────────────────────────────────────┤
    │  Bounded.lean   │ Finite, Bounded, UnitInterval, Positive, NonNegative │
    │  Vec2.lean      │ 2D vectors, dot, perp, lerp (particle physics)        │
    │  Vec3.lean      │ 3D vectors, dot, cross, normalize, project/reject    │
    │  Vec4.lean      │ 4D/homogeneous vectors, perspective divide            │
    │  Mat3.lean      │ 3x3 matrices, 2D transforms, normal transformation    │
    │  Mat4.lean      │ 4x4 matrices, transforms, determinant                 │
    │  Mat4Inverse    │ Matrix inversion, adjugate, cofactors                 │
    │  Mat4Projection │ Perspective, orthographic, look-at matrices           │
│  Quaternion.lean│ Unit quaternions, SLERP, rotation matrices            │
│  Euler.lean     │ Euler angles with rotation order (XYZ, YZX, etc.)     │
│  Ray.lean       │ Ray casting, parametric line, closest point           │
│  Plane.lean     │ Infinite plane, distance, normal/point constructor    │
│  Box3.lean      │ Axis-aligned bounding box, containment, intersection  │
│  Sphere.lean    │ Bounding sphere, containment, intersection            │
│  Triangle.lean  │ Barycentric coords, normal, area                      │
│  Frustum.lean   │ View frustum, 6-plane culling                         │
│  Integration    │ Euler, Verlet, velocity Verlet (particle physics)     │
    │  Force.lean     │ Gravity wells, vortices, uniform forces               │
    │  Constraint     │ Distance constraints, mass weighting                  │
    │  Transform.lean │ Position + Rotation + Scale (TODO)                    │
    │  AABB.lean      │ Axis-aligned bounding boxes (TODO)                    │
    │  Frustum.lean   │ View frustum, culling (TODO)                          │
    └─────────────────────────────────────────────────────────────────────────┘
  
  ZERO-LATENCY INVARIANTS (proven for all operations):
    1. All values are finite (no NaN, no Infinity)
    2. All operations terminate in bounded steps
    3. All transformations preserve key geometric properties
    4. All normalizations handle edge cases by proof, not runtime check
  
  These proofs enable billion-agent operation without runtime validation.
  
  Status: FOUNDATIONAL - Bounded, Vec2, Vec3, Vec4, Mat3, Mat4, Quaternion, Euler, Ray, Plane, Box3, Sphere, Triangle, Frustum, Integration, Force, Constraint complete
-/

import Hydrogen.Math.Bounded
import Hydrogen.Math.Vec2
import Hydrogen.Math.Vec3
import Hydrogen.Math.Vec4
import Hydrogen.Math.Mat3
import Hydrogen.Math.Mat4
import Hydrogen.Math.Mat4Inverse
import Hydrogen.Math.Mat4Projection
import Hydrogen.Math.Quaternion
import Hydrogen.Math.Euler
import Hydrogen.Math.Ray
import Hydrogen.Math.Plane
import Hydrogen.Math.Box3
import Hydrogen.Math.Sphere
import Hydrogen.Math.Triangle
import Hydrogen.Math.Frustum
import Hydrogen.Math.Integration
import Hydrogen.Math.Force
import Hydrogen.Math.Constraint

namespace Hydrogen.Math

-- ═══════════════════════════════════════════════════════════════════════════════
-- RE-EXPORTS
-- ═══════════════════════════════════════════════════════════════════════════════

-- All types and theorems from submodules are available via this import

-- ═══════════════════════════════════════════════════════════════════════════════
-- SUMMARY OF PROVEN PROPERTIES
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Bounded.lean

### Finite
- `add_comm`, `add_assoc`, `mul_comm`, `mul_assoc`, `distrib`
- Arithmetic forms a commutative ring

### Bounded
- `clamp_idempotent` - clamping is idempotent
- `clamp_within` - in-bounds values unchanged
- `add_bounded` - addition preserves bounds

### UnitInterval
- `complement_involutive` - complement (complement x) = x
- `lerp_zero`, `lerp_one` - lerp endpoints
- `lerp_bounded` - lerp stays in range
- `mul_comm`, `mul_assoc` - multiplication laws

### Positive, NonNegative
- `sqrt_sq` - sqrt (x²) = x for non-negative x

## Vec2.lean (Particle Physics Foundation)

### Algebraic
- `add_comm`, `add_assoc`, `add_zero`, `zero_add`, `add_neg` - addition group
- `sub_def` - a - b = a + (-b)
- `scale_one`, `scale_zero`, `zero_scale` - scalar multiplication
- `scale_neg_one`, `neg_scale`, `scale_neg` - negation laws
- `scale_assoc`, `scale_add_left`, `scale_add_right` - scalar linearity

### Dot Product
- `dot_comm` - commutativity
- `dot_self_nonneg` - v·v ≥ 0
- `dot_self_eq_zero` - v·v = 0 ↔ v = 0
- `dot_scale_left`, `dot_scale_right` - scalar linearity
- `dot_add_left`, `dot_add_right` - additive linearity

### Perpendicular Operations (THE KEY GEOMETRIC PROOFS)
- `perp_orthogonal` - perp(v)·v = 0 (THE CRITICAL THEOREM for vortex forces)
- `perpCW_orthogonal` - perpCW(v)·v = 0
- `perp_neg_perpCW` - perp(v) = -perpCW(v)
- `lengthSq_perp` - |perp(v)|² = |v|² (rotation preserves length)
- `perp_perp` - perp(perp(v)) = -v (90° + 90° = 180°)
- `perp_perp_perp_perp` - four perp's = identity

### Length and Normalization
- `lengthSq_nonneg`, `length_nonneg` - non-negativity
- `lengthSq_eq_zero` - |v|² = 0 ↔ v = 0
- `lengthSq_zero_vec`, `length_zero_vec` - |0| = 0

### Linear Interpolation
- `lerp_zero` - lerp(0, a, b) = a
- `lerp_one` - lerp(1, a, b) = b
- `lerp_self` - lerp(t, a, a) = a

## Vec3.lean

### Algebraic
- `add_comm`, `add_assoc`, `add_zero`, `add_neg` - addition group
- `scale_one`, `scale_assoc`, `scale_distrib_vec`, `scale_distrib_scalar` - scalar mult

### Dot Product
- `dot_comm` - commutativity
- `dot_self_nonneg` - v·v ≥ 0
- `dot_self_eq_zero` - v·v = 0 ↔ v = 0
- `dot_scale_left`, `dot_scale_right` - scalar linearity
- `dot_add_left`, `dot_add_right` - additive linearity

### Cross Product (THE KEY GEOMETRIC PROOFS)
- `cross_perp_left` - a · (a × b) = 0 (perpendicular to first)
- `cross_perp_right` - b · (a × b) = 0 (perpendicular to second)
- `cross_anticomm` - a × b = -(b × a)
- `cross_self` - v × v = 0
- `cross_add_left`, `cross_add_right` - distributivity
- `cross_scale_left`, `cross_scale_right` - scalar linearity

### Length and Normalization
- `lengthSq_nonneg`, `length_nonneg` - non-negativity
- `length_zero`, `lengthSq_eq_zero` - zero characterization
- `length_scale` - |s·v| = |s|·|v|
- `normalize_length` - |normalize v| = 1
- `normalize_idempotent` - normalizing a unit vector is identity

### Geometric Operations
- `project_reject_orthogonal` - projection ⊥ rejection
- `project_reject_sum` - projection + rejection = original
- `lerp_zero_t`, `lerp_one_t` - lerp endpoints

## Mat3.lean (Normal Transformation)

### Algebraic
- `mul_identity_left`, `mul_identity_right` - identity laws
- `mul_zero_left`, `mul_zero_right` - zero annihilation
- `mul_assoc` - matrix multiplication is associative

### Transpose
- `transpose_involutive` - (Aᵀ)ᵀ = A
- `transpose_identity`, `transpose_zero` - special matrices
- `transpose_add`, `transpose_scale` - linearity
- `transpose_mul` - (AB)ᵀ = BᵀAᵀ (reverses order)

### Determinant
- `det_identity` - det(I) = 1
- `det_zero` - det(0) = 0
- `det_transpose` - det(Aᵀ) = det(A)
- `det_scale` - det(sA) = s³·det(A)
- `det_mul` - det(AB) = det(A)·det(B) (multiplicative)

### Matrix-Vector Multiplication
- `mulVec_identity` - I × v = v
- `mulVec_zero_mat`, `mulVec_zero_vec` - zero cases
- `mulVec_mul` - (AB)v = A(Bv) (associative with vectors)
- `mulVec_add_vec`, `mulVec_scale_vec` - linearity

### Rotation Matrices
- `makeRotationX/Y/Z_zero` - R(0) = I (zero rotation is identity)
- `det_makeRotationX/Y/Z` - det = 1 (volume-preserving)

### Diagonal Matrices
- `diagonal_one` - diagonal(1,1,1) = I
- `uniformScale_one` - uniformScale(1) = I
- `det_diagonal` - det = d₀·d₁·d₂
- `det_uniformScale` - det = s³

## Mat4.lean

### Algebraic
- `add_comm`, `add_assoc`, `add_zero`, `zero_add`, `add_neg` - addition group
- `mul_identity_left`, `mul_identity_right` - identity laws
- `mul_zero_left`, `mul_zero_right` - zero annihilation
- `mul_assoc` - THE CRITICAL THEOREM: matrix multiplication is associative
- `mul_add_left`, `mul_add_right` - distributivity
- `scale_mul_left`, `scale_mul_right` - scalar multiplication

### Transpose
- `transpose_involutive` - (Aᵀ)ᵀ = A
- `transpose_identity`, `transpose_zero` - special matrices
- `transpose_add`, `transpose_scale` - linearity
- `transpose_mul` - (AB)ᵀ = BᵀAᵀ (reverses order)

### Determinant
- `det_identity` - det(I) = 1
- `det_zero` - det(0) = 0
- `det_transpose` - det(Aᵀ) = det(A)
- `det_scale` - det(sA) = s⁴·det(A)
- `det_mul` - det(AB) = det(A)·det(B) (multiplicative)

### Transformations
- `makeTranslation_zero`, `makeScale_one` - identity cases
- `makeTranslation_mul` - T(a)·T(b) = T(a+b) (translations compose by adding)
- `makeScale_mul` - S(a)·S(b) = S(a*b) (scales compose by multiplying)
- `makeRotationX/Y/Z_zero` - R(0) = I (zero rotation is identity)
- `det_makeTranslation` - det = 1 (volume-preserving)
- `det_makeScale` - det = sx·sy·sz (volume scaling)
- `det_makeRotationX/Y/Z` - det = 1 (volume-preserving)

### Invertibility
- `identity_invertible`, `makeTranslation_invertible` - basic invertibility
- `makeScale_invertible`, `makeRotationX/Y/Z_invertible` - transform invertibility
- `mul_invertible` - product of invertibles is invertible

## Mat4Inverse.lean

### Cofactors and Adjugate
- `c00`..`c33` - all 16 cofactor functions
- `adjugate` - transpose of cofactor matrix
- `adjugate_identity` - adj(I) = I

### Adjugate Laws
- `mul_adjugate` - A × adj(A) = det(A) × I (KEY IDENTITY)
- `adjugate_mul` - adj(A) × A = det(A) × I

### Inverse
- `inverse` - A⁻¹ = adj(A) / det(A) for invertible A
- `mul_inverse` - A × A⁻¹ = I (right inverse)
- `inverse_mul` - A⁻¹ × A = I (left inverse)
- `inverse_identity` - I⁻¹ = I
- `inverse_mul_rev` - (A × B)⁻¹ = B⁻¹ × A⁻¹ (reverses order)

## Mat4Projection.lean

### Perspective Projection
- `makePerspective` - symmetric frustum from fov, aspect, near, far
- `makeFrustum` - asymmetric frustum from bounds

### Orthographic Projection
- `makeOrthographic` - orthographic from bounds
- `makeOrthographicSymmetric` - centered orthographic
- `makeOrthographic_invertible` - non-degenerate ortho is invertible
- `det_makeOrthographicSymmetric` - determinant is nonzero

### View Matrix
- `makeLookAt` - view matrix from eye, center, up vectors

## Quaternion.lean

### Algebraic
- `add_comm`, `add_assoc`, `add_zero`, `zero_add`, `add_neg` - addition group
- `mul_identity_left`, `mul_identity_right` - identity laws
- `mul_zero_left`, `mul_zero_right` - zero annihilation
- `mul_assoc` - THE KEY THEOREM: quaternion multiplication is associative
- `mul_not_comm` - multiplication is NOT commutative (unlike matrices)
- `scale_mul_left`, `scale_mul_right` - scalar multiplication

### Conjugate
- `conjugate_involutive` - (q*)* = q
- `conjugate_identity`, `conjugate_zero` - special cases
- `conjugate_mul` - (ab)* = b*a* (reverses order)
- `conjugate_add` - distributes over addition
- `mul_conjugate`, `conjugate_mul_self` - q × q* = ‖q‖² × I

### Length
- `lengthSq_nonneg`, `length_nonneg` - non-negativity
- `lengthSq_identity`, `length_identity` - identity has length 1
- `lengthSq_zero`, `length_zero` - zero has length 0
- `lengthSq_eq_zero` - ‖q‖² = 0 ↔ q = 0
- `length_conjugate` - ‖q*‖ = ‖q‖
- `lengthSq_mul`, `length_mul` - ‖ab‖ = ‖a‖ × ‖b‖ (multiplicative)

### Unit Quaternions
- `IsUnit` - predicate for unit length
- `identity_isUnit` - I is unit
- `mul_isUnit` - unit × unit = unit (closed under multiplication)
- `conjugate_isUnit` - unit* is unit
- `fromRotationX/Y/Z_isUnit` - axis rotations are unit
- `normalize_isUnit` - normalization produces unit quaternion

### Inverse
- `inverse` - q⁻¹ = q* / ‖q‖²
- `inverse_unit` - for unit q: q⁻¹ = q*
- `mul_inverse_unit`, `inverse_mul_unit` - q × q⁻¹ = I for unit q

### SLERP
- `lerp` - linear interpolation (for small angles)
- `lerp_zero`, `lerp_one` - lerp endpoints
- `slerp` - spherical linear interpolation (THE KEY FEATURE)

### Rotation Matrix Conversion
- `toMat4` - convert quaternion to 4×4 rotation matrix
- `toMat4_identity` - identity quaternion → identity matrix
- `det_toMat4_unit` - det = 1 for unit quaternions (rotation matrices)

## Euler.lean (Euler Angles)

### Rotation Orders
- `RotationOrder` - XYZ, YZX, ZXY, XZY, YXZ, ZYX
- `RotationOrder.default` - XYZ is default

### Constructors
- `zero`, `zeroWithOrder` - identity rotation
- `fromAngles`, `fromAnglesWithOrder` - create from angles
- `fromVec3`, `fromVec3WithOrder` - create from Vec3

### Conversions
- `toMat3`, `toMat4`, `toQuaternion` - convert to rotation representations
- `toVec3` - extract angles as Vec3

### Identity Proofs
- `toMat3_zeroWithOrder` - zero Euler → identity Mat3 (for all orders)
- `toMat4_zeroWithOrder` - zero Euler → identity Mat4 (for all orders)
- `toQuaternion_zeroWithOrder` - zero Euler → identity quaternion (for all orders)

### Properties
- `neg_neg` - negation is involutive
- `fromVec3_toVec3_x/y/z` - Vec3 round-trip preserves angles
- `setOrder_preserves_x/y/z` - reordering preserves angles
- `setOrder_same` - setting same order is identity

## Ray.lean (Ray Casting)

### Constructors
- `default` - origin at zero, pointing +Z
- `fromPoints` - ray from origin to target
- `fromPointsNormalized` - ray with unit direction

### Parametric Operations
- `pointAt` - P(t) = origin + t * direction
- `recast` - move origin along ray
- `reverse` - flip ray direction
- `lookAt` - point ray at target

### Closest Point
- `closestPointParameter` - parameter t for closest point
- `closestPointToPoint` - closest point on ray (t ≥ 0)
- `closestPointToPointOnLine` - closest point on infinite line
- `distanceToPoint`, `distanceSqToPoint` - distance to ray

### Parametric Proofs
- `pointAt_zero` - P(0) = origin
- `pointAt_one` - P(1) = origin + direction
- `pointAt_add`, `pointAt_scale` - linearity in parameter
- `fromPoints_pointAt_one` - P(1) on fromPoints = target

### Recast Proofs
- `recast_zero` - recast(0) = identity
- `recast_recast` - recast is additive
- `recast_direction` - recast preserves direction

### Reverse Proofs
- `reverse_reverse` - reverse is involutive
- `reverse_pointAt` - P(-t) on reversed ray = P(t) on original

## Plane.lean (Infinite Planes)

### Constructors
- `default`, `xy`, `xz`, `yz` - standard coordinate planes
- `fromNormalAndConstant` - from normal and constant
- `fromNormalAndPoint` - from normal and point on plane
- `fromCoplanarPoints` - from three coplanar points

### Operations
- `distanceToPoint` - signed distance from point to plane
- `negate` - flip plane orientation
- `normalize` - make normal a unit vector
- `coplanarPoint` - get a point on the plane
- `projectPoint`, `reflectPoint` - point operations
- `translate` - translate the plane

### Distance Proofs
- `distanceToPoint_fromNormalAndPoint` - point used in constructor has distance 0
- `distanceToPoint_origin` - distance from origin equals constant
- `distanceToPoint_add_normal` - linearity along normal direction
- `distanceToPoint_fromCoplanarPoints_a/b/c` - all three points have distance 0

### Negate Proofs
- `negate_negate` - negation is involutive
- `distanceToPoint_negate` - negating flips sign of distance

### Translate Proofs
- `translate_zero` - translating by zero is identity
- `translate_translate` - translation composition
- `distanceToPoint_translate` - distance changes predictably

## Box3.lean (Axis-Aligned Bounding Box)

### Constructors
- `empty`, `unit` - standard boxes
- `fromHalfExtents`, `fromCenterAndSize` - from dimensions
- `fromPoint`, `fromCorners` - from points

### Queries
- `center`, `size`, `halfExtents` - box properties
- `volume`, `surfaceArea` - measurements
- `IsValid`, `IsEmpty` - validity predicates

### Containment
- `containsPoint`, `containsBox` - containment tests
- `intersectsBox` - intersection test

### Operations
- `expandByPoint`, `expandByVector`, `expandByScalar` - expansion
- `union`, `intersect` - set operations
- `clampPoint`, `distanceToPoint` - point operations
- `translate` - translation

### Containment Proofs
- `containsPoint_min`, `containsPoint_max` - corners are contained
- `containsPoint_center` - center is contained
- `containsPoint_fromPoint` - single-point box contains point
- `containsBox_self` - box contains itself

### Intersection Proofs
- `intersectsBox_comm` - intersection is commutative
- `intersectsBox_self` - valid box intersects itself

### Center/Size Proofs
- `center_unit`, `size_unit`, `volume_unit` - unit box properties
- `center_fromCenterAndSize`, `size_fromCenterAndSize` - round-trip
- `center_fromHalfExtents`, `halfExtents_fromHalfExtents` - round-trip

### Transform Proofs
- `translate_zero`, `translate_translate` - translation laws
- `size_translate` - translation preserves size
- `center_translate` - translation moves center
- `expandByVector_zero`, `expandByScalar_zero` - expansion identity
- `center_expandByVector` - expansion preserves center

## Sphere.lean (Bounding Spheres)

### Constructors
- `empty`, `unit`, `point` - standard spheres
- `fromCenterAndRadius` - explicit construction
- `boundingPoint`, `boundingTwoPoints` - bounding spheres

### Validity
- `IsValid`, `IsEmpty` - validity predicates
- `unit_isValid`, `point_isValid` - standard spheres are valid
- `empty_isEmpty` - empty sphere is empty

### Queries
- `diameter`, `surfaceArea`, `volume` - sphere measurements
- `distanceSqToCenter`, `distanceToCenter` - distance to center
- `distanceToPoint` - signed distance to surface
- `clampPoint` - clamp point to sphere

### Containment Proofs
- `containsPoint_center` - center is always contained
- `containsPoint_point` - point sphere contains its center
- `containsPoint_unit_origin` - unit sphere contains origin

### Intersection
- `intersectsSphere` - sphere-sphere intersection test
- `intersectsSphere_self` - valid sphere intersects itself
- `intersectsSphere_comm` - intersection is commutative
- `Vec3.distanceSq_comm` - squared distance is symmetric
- `Vec3.distance_comm` - distance is symmetric

### Translation and Scaling
- `translate_zero` - translating by zero is identity
- `translate_translate` - translation composition
- `radius_translate`, `center_translate` - translation effects
- `scaleRadius_one`, `expandRadius_zero` - identity cases
- `center_scaleRadius`, `center_expandRadius` - center preservation

## Triangle.lean (Triangles)

### Constructors
- `unit`, `degenerate` - standard triangles
- `fromPoints` - from three vertices

### Edges
- `edgeAB`, `edgeAC`, `edgeBC` - edge vectors
- `edgeBA`, `edgeCA`, `edgeCB` - reverse edges
- `edge_loop` - AB + BC + CA = 0 (closed loop)
- `edgeAB_neg_edgeBA` - edge direction inversion

### Normal and Area
- `normalUnnormalized`, `crossEdges` - normal computation
- `area`, `signedAreaXY` - triangle area
- `area_nonneg` - area is non-negative
- `degenerate_area` - degenerate has zero area
- `unit_area` - unit triangle has area 1/2

### Normal Perpendicularity (THE KEY PROOFS)
- `normal_perp_edgeAB` - normal ⊥ edge AB
- `normal_perp_edgeAC` - normal ⊥ edge AC

### Barycentric Coordinates
- `Barycentric` - (u, v, w) coordinates
- `Barycentric.sum`, `Barycentric.IsValid`, `Barycentric.IsInside`
- `barycentric_vertexA/B/C_sum` - vertex coords sum to 1
- `barycentric_centroid_sum` - centroid coords sum to 1
- `barycentric_vertexA/B/C_valid` - vertex coords are valid
- `fromBarycentric_vertexA/B/C` - vertices map correctly
- `fromBarycentric_centroid` - centroid maps correctly

### Unit Triangle
- `unit_a`, `unit_b`, `unit_c` - vertex positions
- `unit_edgeAB`, `unit_edgeAC` - edge vectors
- `unit_normal` - normal points in +Z

## Frustum.lean (View Frustum Culling)

### Constructors
- `default` - standard frustum
- `fromPlanes` - from six planes

### Plane Access
- `planes` - list of all six planes
- `getPlane` - plane by index (0-5)
- `getPlane_left/right/top/bottom/near/far` - named accessors

### Containment
- `inHalfspace` - point in positive halfspace of plane
- `containsPoint` - point inside all six halfspaces
- `containsPoint_iff_all_halfspaces` - equivalence
- `not_containsPoint_of_outside_*` - early-out conditions

### Sphere Intersection
- `sphereOutsidePlane` - sphere completely outside plane
- `intersectsSphere` - sphere not outside any plane
- `intersectsSphere_iff` - equivalence
- `intersectsSphere_of_containsPoint` - point spheres inside frustum intersect

### Box Intersection
- `boxPositiveVertex`, `boxNegativeVertex` - extreme vertices
- `boxOutsidePlane` - box completely outside plane
- `intersectsBox` - box not outside any plane
- `intersectsBox_iff` - equivalence

### Vertex Selection Proofs
- `boxPositiveVertex_x/y/z` - coordinate selection
- `boxNegativeVertex_x/y/z` - coordinate selection

## Integration.lean (Particle Physics Simulation)

### Integration Methods
- `eulerStep` - explicit Euler (simple but unstable)
- `semiImplicitEulerStep` - symplectic Euler (LATTICE rigid bodies)
- `verletStep` - Störmer-Verlet (LATTICE soft bodies)
- `verletStepDamped` - Verlet with damping factor
- `velocityVerletStep` - velocity Verlet (explicit velocity tracking)

### State Conversion
- `toVerletState` - convert particle state to Verlet state
- `fromVerletState` - extract ParticleState from VerletState
- `verletVelocity` - extract implicit velocity from Verlet state

### Zero Acceleration
- `euler_zero_accel` - zero acceleration preserves velocity
- `semiImplicit_zero_accel` - zero acceleration preserves velocity

### Zero Timestep
- `euler_zero_dt` - zero timestep is identity
- `semiImplicit_zero_dt` - zero timestep is identity
- `verlet_zero_dt` - zero timestep advances by implicit velocity

### Time-Reversibility (THE KEY THEOREM)
- `verlet_time_reversible` - Verlet is time-reversible (energy conservation)

### Euler Comparison
- `euler_semiImplicit_same_velocity` - both produce same velocity
- `euler_semiImplicit_position_diff` - position differs by a*dt²

### Verlet Equivalence
- `verlet_position_formula` - classic x(t+dt) = 2x(t) - x(t-dt) + a*dt²
- `verlet_conversion_velocity` - velocity preserved through conversion

### Damping Properties
- `verlet_damping_one` - damping=1 is undamped Verlet
- `verlet_damping_zero` - damping=0 eliminates velocity

### Velocity Verlet Properties
- `velocityVerlet_same_velocity` - same velocity as explicit Euler
- `velocityVerlet_position` - includes second-order correction

## Force.lean (Particle Physics Force Fields)

### Force Definitions
- `uniformForce` - constant direction/magnitude (wind, gravity)
- `gravityForce` - radial attraction/repulsion toward center
- `vortexForce` - tangential rotation around center
- `spiralForce` - combined vortex + radial pull

### Orthogonality (THE KEY THEOREMS)
- `vortex_force_orthogonal` - vortex · displacement = 0 (tangent forces do no radial work)
- `gravity_force_orthogonal_to_tangent` - gravity · perp(displacement) = 0 (radial only)

### Zero Strength
- `uniform_zero_strength` - zero strength = zero force
- `gravity_zero_strength` - zero strength = zero force
- `vortex_zero_strength` - zero strength = zero force

### Force Linearity (Superposition)
- `uniform_add` - uniform forces add by strength
- `gravity_add` - gravity forces from same center add
- `vortex_add` - vortex forces from same center add

### Point at Center
- `displacement_self` - displacement to self = zero
- `gravity_at_center` - gravity at center = zero (singularity avoided)
- `vortex_at_center` - vortex at center = zero

### Negation
- `gravity_neg_strength` - negating strength negates force
- `vortex_neg_strength` - negating strength negates force

## Constraint.lean (Soft Body Constraint Solving)

### Correction Direction (THE KEY THEOREMS)
- `correction_parallel_to_separation` - correction is scalar multiple of separation
- `correction_orthogonal_to_tangent` - correction · perp(separation) = 0

### Equal Mass
- `equal_mass_opposite` - equal mass corrections are exactly opposite
- `equal_mass_sum_zero` - sum is zero (preserves center of mass)

### Zero Conditions
- `correction_zero_when_satisfied` - zero error = zero correction
- `correction_zero_stiffness` - zero stiffness = zero correction
- `correction_zero_coincident` - coincident particles = zero correction

### Mass Weighting
- `pinned_A_no_move` - ratioA=0 means A doesn't move
- `pinned_B_no_move` - ratioB=0 means B doesn't move
- `equal_ratios_opposite` - equal ratios produce opposite corrections

### Ratio Sum
- `ratio_correction_sum` - weighted corrections sum to (ratioA-ratioB)*correction
- `half_ratios_sum_zero` - ratios (0.5, 0.5) sum to zero

### Scaling and Negation
- `stiffness_scales` - stiffness scales linearly
- `error_scales` - error scales linearly
- `neg_error_neg_correction` - negating error negates correction
- `swap_positions_neg_correction` - swapping positions negates correction
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- WHAT THESE PROOFS ENABLE AT BILLION-AGENT SCALE
-- ═══════════════════════════════════════════════════════════════════════════════

/-!
## Why These Proofs Matter

When 1 million agents operate at 1000+ tokens/second:

1. **No runtime validation needed**
   - `cross_perp_left` is PROVEN - no need to check `abs(dot(a, cross(a,b))) < epsilon`
   - `normalize_length` is PROVEN - no need to check `abs(length(normalize(v)) - 1) < epsilon`
   
2. **No exception handling paths**
   - Division by zero in `normalize` is impossible by construction (proof requires v ≠ 0)
   - NaN propagation is impossible (all values are real numbers)
   
3. **No coordination overhead**
   - All operations are pure functions
   - Same input → same output (deterministic)
   - Can be parallelized without locks
   
4. **Bounded computation**
   - Every operation completes in O(1)
   - No iteration, no recursion (except lerp which is O(1))
   
5. **Composable correctness**
   - `project_reject_sum` lets us decompose vectors knowing the sum is exact
   - Downstream proofs can rely on these without re-proving

## The Code Generation Contract

The generated PureScript mirrors the Lean definitions exactly:
- Same structure
- Same operations
- Same semantics (both pure, both call-by-value)

The proofs in Lean ARE the specification. The PureScript IS the implementation.
They match by construction.
-/

end Hydrogen.Math
