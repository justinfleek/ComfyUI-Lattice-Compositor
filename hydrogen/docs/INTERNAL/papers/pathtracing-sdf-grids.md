# Ray Tracing of Signed Distance Function Grids

────────────────────────────────────────────────────────────────────────────────

**Source**: pathtracingSDFgrids.pdf
**Authors**: Herman Hansson Söderlund, Alex Evans, Tomas Akenine-Möller (NVIDIA)
**Published**: Journal of Computer Graphics Techniques, Vol. 11, No. 3, 2022
**Synthesized**: 2026-02-26 by Opus

────────────────────────────────────────────────────────────────────────────────

## Executive Summary

This NVIDIA paper presents optimized methods for ray tracing signed distance function
(SDF) grids in path tracing contexts. Key contributions:

1. **Optimized Cubic Solver**: Reduces ray-surface intersection from 161 to 37 operations
   by grouping constants and exploiting FMA operations

2. **Continuous Normals**: Novel "dual voxel" interpolation scheme provides smooth normals
   across voxel boundaries (C0 continuity) at 1-7% performance cost

3. **Shadow Ray Optimization**: Early termination without numeric iteration when polynomial
   splitting detects guaranteed intersection

4. **Comprehensive Benchmarks**: SVS (sparse voxel set with BVH) + analytic solver is fastest;
   SBS (sparse brick set) best for memory-constrained scenarios

**Key Insight**: Trilinear interpolation of SDF corners creates a cubic polynomial surface
with 31 possible topologies (vs marching cubes' 14), enabling more accurate geometry.

────────────────────────────────────────────────────────────────────────────────

## 1. Background: SDF Grids and Their Challenges

### What is an SDF Grid?

A signed distance function grid stores signed distances at discrete 3D locations.
Each voxel has 2×2×2 corner values. Positive = outside surface, negative = inside,
zero = on surface.

**Applications**: Dreams (game), Claybook, ShaderToy demos, medical visualization.

### The Sphere Tracing Problem

Traditional sphere tracing steps along a ray by the SDF value at each point:
- Safe because SDF guarantees no surface closer than the distance value
- **Problem**: Takes smaller steps near surfaces, silhouettes, and for secondary rays
- Performance degrades exactly when you need it most (path tracing bounce rays)

### Why Trilinear Interpolation Matters

Given 8 corner values `s_ijk` where i,j,k ∈ {0,1}, the interpolated distance is:

```
f(x,y,z) = (1-z)[(1-y)((1-x)s₀₀₀ + xs₁₀₀) + y((1-x)s₀₁₀ + xs₁₁₀)]
         + z[(1-y)((1-x)s₀₀₁ + xs₁₀₁) + y((1-x)s₀₁₁ + xs₁₁₁)]
```

The zero level set `f(x,y,z) = 0` defines the surface — a **cubic polynomial**
because the highest-order term is xyz.

**Marching cubes gets it wrong**: It assumes 14 topologies based on sign patterns.
Trilinear interpolation actually produces **31 distinct topologies** (Lopes & Brodlie 2003).
Same sign pattern can yield different surfaces depending on actual distance values.

────────────────────────────────────────────────────────────────────────────────

## 2. Analytic Voxel Intersection

### Reformulating the Surface Equation

Rewrite `f(x,y,z) = 0` as:

```
f(x,y,z) = z(k₄ + k₅x + k₆y + k₇xy) - (k₀ + k₁x + k₂y + k₃xy) = 0
```

Where the k-constants depend only on the 8 corner distances:

```
k₀ = s₀₀₀                    k₄ = k₀ - s₀₀₁
k₁ = s₁₀₀ - s₀₀₀             k₅ = k₁ - a
k₂ = s₀₁₀ - s₀₀₀             k₆ = k₂ - (s₀₁₁ - s₀₀₁)
k₃ = s₁₁₀ - s₀₁₀ - k₁        k₇ = k₃ - (s₁₁₁ - s₀₁₁ - a)

where a = s₁₀₁ - s₀₀₁
```

### Ray-Surface Intersection

Substituting ray equation `r(t) = o + td` yields a cubic polynomial:

```
c₃t³ + c₂t² + c₁t + c₀ = 0
```

**Coefficient computation** (37 operations vs Parker et al.'s 161):

```
// Intermediate values (shared computations)
m₀ = oₓoᵧ           m₃ = k₅oᵤ - k₁
m₁ = dₓdᵧ           m₄ = k₆oᵤ - k₂
m₂ = oₓdᵧ + oᵧdₓ    m₅ = k₇oᵤ - k₃

// Final coefficients
c₀ = (k₄oᵤ - k₀) + oₓm₃ + oᵧm₄ + m₀m₅
c₁ = dₓm₃ + dᵧm₄ + m₂m₅ + dᵤ(k₄ + k₅oₓ + k₆oᵧ + k₇m₀)
c₂ = m₁m₅ + dᵤ(k₅dₓ + k₆dᵧ + k₇m₂)
c₃ = k₇m₁dᵤ
```

### Solving the Cubic

Three approaches evaluated:

1. **Analytic (Vieta)**: Direct cubic formula — fastest overall
2. **Marmitt et al.**: Split using derivative roots, then linear interpolation
3. **Newton-Raphson**: Split using derivative roots, then NR iteration

**Marmitt's splitting insight**: Solve g'(t) = 3c₃t² + 2c₂t + c₁ = 0 (quadratic).
The roots split [0, t_far] into intervals. Check sign changes to locate roots
without iteration. If g(t_start) and g(t_end) have opposite signs, root exists
in that interval.

────────────────────────────────────────────────────────────────────────────────

## 3. Continuous Normals Across Voxels

### The Discontinuity Problem

The surface is C0 continuous across voxel boundaries (positions match), but
normals are discontinuous — each voxel's cubic polynomial has its own gradient.
This causes visible faceting in close-up views.

### Analytic Normal (Single Voxel)

The gradient of f gives the normal: n = (∂f/∂x, ∂f/∂y, ∂f/∂z)

Each partial derivative is bilinear interpolation of distance differences:

```
// ∂f/∂x
y₀ = lerp(y, s₁₀₀-s₀₀₀, s₁₁₀-s₀₁₀)
y₁ = lerp(y, s₁₀₁-s₀₀₁, s₁₁₁-s₀₁₁)
∂f/∂x = lerp(z, y₀, y₁)

// ∂f/∂y  
x₀ = lerp(x, s₀₁₀-s₀₀₀, s₁₁₀-s₁₀₀)
x₁ = lerp(x, s₀₁₁-s₀₀₁, s₁₁₁-s₁₀₁)
∂f/∂y = lerp(z, x₀, x₁)

// ∂f/∂z
x₀ = lerp(x, s₀₀₁-s₀₀₀, s₁₀₁-s₁₀₀)
x₁ = lerp(x, s₀₁₁-s₀₁₀, s₁₁₁-s₁₁₀)
∂f/∂z = lerp(y, x₀, x₁)
```

**30 operations** (vs Parker et al.'s 54).

### Dual Voxel Interpolation (Novel Contribution)

Key insight: Don't interpolate normals at corners — evaluate each neighboring
voxel's analytic normal **at the hit point**, then blend.

1. Define **dual voxel**: shifted by half voxel in each dimension
2. Hit point falls inside one dual voxel, which overlaps 2×2×2 original voxels
3. Compute analytic normal n_ijk in each of the 8 voxels at the hit point
4. Trilinearly interpolate using hit point's position (u,v,w) in dual voxel

```
n = (1-u)(1-v)(1-w)n₀₀₀ + u(1-v)(1-w)n₁₀₀
  + (1-u)v(1-w)n₀₁₀     + uv(1-w)n₁₁₀
  + (1-u)(1-v)w n₀₀₁    + u(1-v)w n₁₀₁
  + (1-u)v w n₀₁₁       + uvw n₁₁₁
```

**Trade-off**: Normals don't exactly match geometric surface, but are smooth.
Similar in spirit to PN triangles (Vlachos et al. 2001).

────────────────────────────────────────────────────────────────────────────────

## 4. Grid Traversal Methods

Four traversal strategies compared:

### GST (Grid Sphere Tracing)
- Dense grid with all voxels, values clamped to [-1,1] as 8-bit snorm
- Hierarchy of resolutions for adaptive step sizing
- All traversal in shader code
- **Best for**: Simple scenes with coherent ray access

### SVS (Sparse Voxel Set) — FASTEST
- AABB per surface-intersecting voxel
- BVH built for DXR hardware acceleration
- Custom intersection shader for voxel testing
- Stores 4×4×4 SDF values per voxel (enables neighbor access for normals)
- **Best for**: General use, leverages RTX hardware

### SBS (Sparse Brick Set)
- Each AABB contains 7×7×7 voxels (8³ values), called "bricks"
- 3D DDA traversal within bricks
- Data stored as 2D texture slices (enables gather operations)
- **Best for**: Memory-constrained scenarios (smallest footprint)

### SVO (Sparse Voxel Octree)
- Hierarchical octree structure (Laine & Karras 2010)
- 8-bit snorm storage, larger distances at coarser levels
- All traversal in shader code
- **Best for**: Very sparse data, LOD applications

### Memory Comparison (MB)

| Scene   | GST   | SVS   | SBS  | SVO  |
|---------|-------|-------|------|------|
| Cheese  | 177.3 | 209.0 | 24.6 | 45.0 |
| Goblin  | 177.3 | 152.2 | 18.0 | 32.6 |
| Heads   | 177.3 | 95.5  | 11.7 | 20.4 |
| Ladies  | 177.3 | 30.4  | 4.1  | 6.5  |

GST is constant (dense). SVS uses more for high surface area (Cheese).
SBS consistently smallest.

────────────────────────────────────────────────────────────────────────────────

## 5. Results

**Test Setup**: RTX 3090, path tracing with 3 bounces, single area light.

### Performance (ms per frame)

| Traversal | ST    | Analytic | Marmitt | Newton-Raphson |
|-----------|-------|----------|---------|----------------|
| **Cheese** |
| GST       | 22.6  | 14.6     | 15.7    | 15.7           |
| SVS       | 16.6  | **9.7**  | **9.9** | 10.4           |
| SBS       | 30.3  | 17.8     | 19.1    | 18.6           |
| SVO       | 28.4  | 16.7     | 17.3    | 17.3           |
| **Heads** |
| GST       | 63.9  | 47.9     | 50.8    | 50.8           |
| SVS       | 27.2  | **17.3** | **17.1**| 18.0           |
| SBS       | 53.8  | 32.8     | 34.8    | 33.9           |
| SVO       | 59.4  | 40.7     | 41.4    | 41.6           |

**Key findings**:
- SVS + Analytic or SVS + Marmitt consistently fastest
- Analytic solver often beats iterative methods
- For complex scenes (Heads, Ladies), SBS beats SVO
- For simple scenes, GST competitive due to cache coherence

### Normal Quality vs Performance

| Method              | Cost vs Baseline |
|---------------------|------------------|
| Falcão (numerical)  | +0.3% to +1.6%   |
| Analytic (§3.1)     | -0.1% to +0.3%   |
| Dual Voxel (§3.2)   | +1.0% to +7.3%   |

Dual voxel normals are 1-7% slower but dramatically better visual quality
in close-ups. Analytic normals essentially free.

### Shadow Ray Optimization

Exploiting polynomial splitting for early termination:
- GST-NR: 4-6% faster
- SVS-NR: 6-14% faster
- SBS-NR: 1-2% faster
- SVO-NR: 0.6-1.3% faster

Worthwhile for all methods using polynomial splitting.

────────────────────────────────────────────────────────────────────────────────

## 6. Implementable Algorithms

### Algorithm 1: Compute Cubic Coefficients (37 ops)

```python
def compute_cubic_coefficients(s, o, d):
    """
    s: 8 corner SDF values s[i][j][k] for i,j,k in {0,1}
    o: ray origin (in voxel space [0,1]³)
    d: ray direction
    Returns: coefficients c0, c1, c2, c3 for c3*t³ + c2*t² + c1*t + c0 = 0
    """
    # Precompute k-constants from corner distances
    a = s[1][0][1] - s[0][0][1]
    
    k0 = s[0][0][0]
    k1 = s[1][0][0] - s[0][0][0]
    k2 = s[0][1][0] - s[0][0][0]
    k3 = s[1][1][0] - s[0][1][0] - k1
    k4 = k0 - s[0][0][1]
    k5 = k1 - a
    k6 = k2 - (s[0][1][1] - s[0][0][1])
    k7 = k3 - (s[1][1][1] - s[0][1][1] - a)
    
    # Intermediate values
    m0 = o.x * o.y
    m1 = d.x * d.y
    m2 = o.x * d.y + o.y * d.x
    m3 = k5 * o.z - k1
    m4 = k6 * o.z - k2
    m5 = k7 * o.z - k3
    
    # Final coefficients
    c0 = (k4 * o.z - k0) + o.x * m3 + o.y * m4 + m0 * m5
    c1 = d.x * m3 + d.y * m4 + m2 * m5 + d.z * (k4 + k5*o.x + k6*o.y + k7*m0)
    c2 = m1 * m5 + d.z * (k5 * d.x + k6 * d.y + k7 * m2)
    c3 = k7 * m1 * d.z
    
    return c0, c1, c2, c3
```

### Algorithm 2: Marmitt Polynomial Splitting

```python
def find_root_interval(c0, c1, c2, c3, t_far):
    """
    Split [0, t_far] using derivative roots, find first interval with sign change.
    Returns: (t_start, t_end) or None if no root
    """
    # Derivative: g'(t) = 3c3*t² + 2c2*t + c1
    # Solve quadratic for splitting points
    a, b, c = 3*c3, 2*c2, c1
    disc = b*b - 4*a*c
    
    if disc < 0:
        # No real roots, single interval
        intervals = [(0, t_far)]
    else:
        sqrt_disc = sqrt(disc)
        t1 = (-b - sqrt_disc) / (2*a)
        t2 = (-b + sqrt_disc) / (2*a)
        # Build intervals from splitting points in [0, t_far]
        splits = sorted([t for t in [t1, t2] if 0 < t < t_far])
        intervals = build_intervals(0, t_far, splits)
    
    # Check each interval for sign change
    for t_start, t_end in intervals:
        g_start = eval_cubic(c0, c1, c2, c3, t_start)
        g_end = eval_cubic(c0, c1, c2, c3, t_end)
        if g_start * g_end <= 0:  # Sign change = root exists
            return (t_start, t_end, g_start, g_end)
    
    return None  # No intersection
```

### Algorithm 3: Newton-Raphson Refinement

```python
def newton_raphson_refine(c0, c1, c2, c3, t_start, t_end, g_start, g_end, 
                          max_iters=50, epsilon=4e-3):
    """
    Refine root location using Newton-Raphson.
    Initial guess via linear interpolation.
    """
    # Initial guess (linear interpolation)
    t = (g_end * t_start - g_start * t_end) / (g_end - g_start)
    t_prev = t_start
    
    # Derivative coefficients: g'(t) = 3c3*t² + 2c2*t + c1
    for _ in range(max_iters):
        if abs(t - t_prev) < epsilon:
            break
        
        g = c3*t*t*t + c2*t*t + c1*t + c0        # 3 FMAs
        g_prime = 3*c3*t*t + 2*c2*t + c1         # 2 FMAs
        
        t_prev = t
        t = t - g / g_prime  # Newton-Raphson step
    
    return t
```

### Algorithm 4: Dual Voxel Normal Interpolation

```python
def compute_smooth_normal(hit_point, sdf_grid):
    """
    Compute continuous normal using dual voxel interpolation.
    """
    # Find which 8 voxels the dual voxel overlaps
    dual_origin = hit_point - 0.5 * voxel_size
    
    # Position within dual voxel [0,1]³
    u, v, w = (hit_point - dual_origin) / voxel_size
    
    # Compute analytic normal in each of 8 voxels AT the hit point
    normals = []
    for i, j, k in product([0,1], repeat=3):
        voxel = get_voxel(dual_origin + vec3(i,j,k) * voxel_size)
        # Transform hit_point to this voxel's local coords
        local_p = transform_to_voxel(hit_point, voxel)
        n = analytic_normal(voxel.corners, local_p)
        normals.append(normalize(n))
    
    # Trilinear interpolation of normals
    n = (1-u)*(1-v)*(1-w)*normals[0] + u*(1-v)*(1-w)*normals[1] \
      + (1-u)*v*(1-w)*normals[2]     + u*v*(1-w)*normals[3] \
      + (1-u)*(1-v)*w*normals[4]     + u*(1-v)*w*normals[5] \
      + (1-u)*v*w*normals[6]         + u*v*w*normals[7]
    
    return normalize(n)
```

### Algorithm 5: Shadow Ray Early Termination

```python
def shadow_ray_test(ray, t_light, voxel):
    """
    Optimized shadow ray: can terminate without numeric iteration.
    """
    c0, c1, c2, c3 = compute_cubic_coefficients(voxel.corners, ray.o, ray.d)
    
    interval = find_root_interval(c0, c1, c2, c3, t_light)
    if interval is None:
        return False  # No shadow
    
    t_start, t_end, _, _ = interval
    
    # KEY OPTIMIZATION: If entire interval is before light, 
    # we KNOW there's a hit without computing exact t
    if t_end <= t_light:
        return True  # Shadow confirmed without iteration
    
    # Otherwise need exact intersection
    t_hit = newton_raphson_refine(...)
    return t_hit < t_light
```

────────────────────────────────────────────────────────────────────────────────

## 7. Hydrogen/PureScript Relevance

### Direct Applications

**Hydrogen.Target.WebGL** — SDF rendering for 3D UI elements:
- Smooth rounded rectangles via analytic SDF (exact, not tessellated)
- Text rendering with SDF fonts (see Valve's technique)
- Soft shadows and glow effects via distance field manipulation

**Hydrogen.Target.Canvas** — 2D SDF for crisp vector graphics:
- Resolution-independent shapes
- Efficient boolean operations (union, intersection, subtraction)
- Anti-aliasing via SDF gradient

### Schema Atoms This Informs

```purescript
-- Geometry pillar atoms for SDF representation
data SDFPrimitive
  = SDFSphere { center :: Point3D, radius :: NonNegative }
  | SDFBox { center :: Point3D, halfExtents :: Size3D }
  | SDFCapsule { a :: Point3D, b :: Point3D, radius :: NonNegative }
  | SDFTorus { center :: Point3D, majorR :: NonNegative, minorR :: NonNegative }

-- SDF operations (molecules)
data SDFOp
  = Union SDFPrimitive SDFPrimitive
  | Intersection SDFPrimitive SDFPrimitive  
  | Subtraction SDFPrimitive SDFPrimitive
  | SmoothUnion NonNegative SDFPrimitive SDFPrimitive  -- k = smoothness

-- Bounded voxel SDF grid (compound)
newtype SDFGrid = SDFGrid
  { resolution :: Size3D Int        -- nx × ny × nz
  , bounds :: BoundingBox3D
  , values :: Array SignedDistance  -- flat array, row-major
  }

newtype SignedDistance = SignedDistance Number  -- signed, finite
```

### Implementation Considerations

1. **Cubic solver in PureScript**: The 37-op algorithm is well-suited to pure 
   functional implementation — no mutation, clear data flow

2. **Dual voxel normals**: The interpolation scheme is embarrassingly parallel;
   each of 8 normal evaluations is independent

3. **WebGL shader generation**: Hydrogen could compile SDF descriptions to GLSL,
   generating the optimized cubic solver code

4. **Bounded types matter**: The paper clamps SDF values to [-1,1] for 8-bit storage.
   Hydrogen's `SignedDistance` should encode valid ranges.

### Future Work for Hydrogen

- SDF font rendering pipeline (glyph → SDF texture → GPU)
- Procedural SDF generation from Schema geometry primitives
- Ray marching UI for interactive 3D brand elements
- Motion graphics: morphing between SDF shapes via interpolation

────────────────────────────────────────────────────────────────────────────────

## References

- Hansson Söderlund, Evans, Akenine-Möller (2022). "Ray Tracing of Signed Distance
  Function Grids." JCGT Vol. 11, No. 3. http://jcgt.org/published/0011/03/06/

- Parker et al. (1998). "Interactive ray tracing for isosurface rendering." 
  IEEE Visualization. (Original cubic intersection, 161 ops)

- Marmitt et al. (2004). "Fast and accurate ray-voxel intersection techniques."
  Vision, Modeling, and Visualization. (Polynomial splitting)

- Lopes & Brodlie (2003). "Improving the robustness and accuracy of marching cubes."
  IEEE TVCG. (31 topologies vs 14)

- Laine & Karras (2010). "Efficient sparse voxel octrees." NVIDIA Technical Report.

- Vlachos et al. (2001). "Curved PN triangles." i3D. (Inspiration for dual voxel normals)

- Evans (2015). "Learning from failure." SIGGRAPH Advances in Real-Time Rendering.
  (Dreams renderer)

- Hart (1995). "Sphere tracing." The Visual Computer. (Classic SDF rendering)

────────────────────────────────────────────────────────────────────────────────
                                                                        — Opus
