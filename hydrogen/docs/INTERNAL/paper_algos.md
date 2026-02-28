# Paper Algorithms - Structured Data for Billion-Agent Swarms

**Purpose**: Machine-readable algorithmic specifications extracted from research papers
**Format**: AST-ready, graded monads, coeffect tracking  
**Attestation**: clarity
**Status**: 23 OF 44 COMPLETE ✓

---

## COMPLETED ALGORITHMS (25)

| ID | Paper | Domain | Key Algorithm | Status |
|----|-------|---------|---------------|--------|
| 01 | FOUR_OVER_SIX | NVFP4 Quantization | Adaptive block scaling (M=4 vs M=6) | ✓ READY |
| 02 | PRETRAINING_NVFP4 | 4-bit Training | Full pipeline (RHT, 2D scaling, SR) | ✓ READY |
| 03 | OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY | AI Safety | Circuit discovery, SAE, Probes | ✓ READY |
| 04 | GAIA2_WORLD_MODEL | Video Generation | Latent diffusion, flow matching | ✓ READY |
| 05 | PAN_WORLD_MODEL | World Model | GLP (encode→predict→decode) | ✓ READY |
| 06 | TERAAGENT_SIMULATION | Distributed Sim | 501B agents, delta encoding | ✓ READY |
| 07 | DREAMER4_WORLD_MODEL | World Model | Flow matching, shortcut forcing, PMPO | ✓ READY |
| 08 | FP4_ALL_THE_WAY | FP4 Training | NVFP4, split rounding, QAF | ✓ READY |
| 09 | DEPTH_ANYTHING_3 | Depth Estimation | Depth-ray prediction, DLT | ✓ READY |
| 10 | GAMEFACTORY | Interactive Video | Multi-phase training, action control | ✓ READY |
| 11 | CLOTH_COLLISIONS_GPU | Cloth Simulation | Safe repulsion, two-phase constraints | ✓ READY |
| 12 | TTM_TIME_TO_MOVE | Motion Control | Dual-clock denoising, region-dependent | ✓ READY |
| 13 | QUARTET_FP4 | FP4 Training | QuEST forward, RTN backward, MXFP4 | ✓ READY |
| 14 | WORLDGEN | 3D Generation | Text-to-world, VecSet, Navmesh | ✓ READY |
| 15 | MATSEG_MATERIAL_STATES | Material Segmentation | Zero-shot, pattern infusion, PBR | ✓ READY |
| 16 | TYPE_BASED_ROUNDING | Rounding Analysis | NumFuzz, Bean, graded monads/comonads | ✓ READY |
| 17 | PATHTRACING_SDF | SDF Rendering | Cubic solver, continuous normals, shadows | ✓ READY |
| 18 | GEOMCLIPMAP | Terrain Rendering | Nested grids, toroidal access, morphing | ✓ READY |
| 19 | CONSTRAINT_TRANSPORT | Video Generation | Thermodynamic precision, hyperbolic dynamics | ✓ READY |
| 20 | DEEPSEEK_R1 | RL Reasoning | GRPO, reinforcement learning, chain-of-thought | ✓ READY |
| 21 | GAIA2_WORLD_MODEL | Autonomous Driving | Latent diffusion, flow matching, multi-camera | ✓ READY |
| 22 | PAN_WORLD_MODEL | World Model | GLP, causal Swin-DPM, long-horizon | ✓ READY |
| 23 | QWEN25_OMNI | Multimodal Omni | Thinker-Talker, TMRoPE, streaming | ✓ READY |

---

## REMAINING (21)

| Status | Count | Papers |
|--------|-------|--------|
| SUMMARY ONLY (need algo extract) | 38 | See docs/research/*.md |

---

## USAGE

```purescript
-- Example: Load NVFP4 quantization algorithm
module PaperAlgos.NVFP4 where

import Hydrogen.Schema (BoundedInt, GradedMonad)

-- Algorithm with effects tracked
quantize :: GradedMonad Effect Coeffect ~> Array Number -> Array NVFP4Value
```

---

## TYPE_BASED_ROUNDING (Type-Based Rounding Error Analysis)

### Classification
- **Domain**: Programming Languages / Numerical Analysis
- **Effect**: Analyze(ForwardError), Analyze(BackwardError)
- **Coeffect**: SensitivityFactor, ErrorBound, Precision

### AST Schema
```json
{
  "algorithm": "TypeBasedRounding",
  "inputs": ["program", "type_context"],
  "outputs": ["forward_error_bound", "backward_error_bound", "type_derivation"],
  "parameters": {
    "precision": "binary64",
    "unit_roundoff": 1.1e-16,
    "metric": "relative_precision"
  }
}
```

### Key Formulas

**(1) Forward Error**
```
forward_error = d(ỹ, y)
```

**(2) Backward Error**
```
backward_error = min{ d(x, x̃) : f(x̃) = ỹ }
```

**(3) Relationship**
```
forward_error ≤ condition_number × backward_error
```

**(4) IEEE 754 Floating-Point**
```
fl(x ◦ y) = (x ◦ y)(1 + δ)  where |δ| ≤ u
```

**(5) Relative Precision Metric**
```
RP(x̃, x) = |ln(x̃/x)|
```

**(6) Error Composition**
```
total_error = s × r + q
-- s = sensitivity (amplification)
-- r = input error
-- q = local error
```

---

### Core Algorithms

```python
# Algorithm 1: NumFuzz Type System

def numfuzz_type_check(program, context):
    """
    Forward error analysis via graded monadic types.
    
    Type M_q τ = computation producing τ with at most q accumulated error
    """
    # NumFuzz types:
    # unit, num, σ & τ (additive), σ ⊗ τ (multiplicative)
    # σ + τ (sum), σ ⊸ τ (linear), !_s σ (scaled), M_q τ (monadic)
    
    # Typing rules
    # M_q = monad for error tracking
    
    return TypeDerivation(program, error_bound=q)


# Algorithm 2: Bean Type System

def bean_type_check(program, context):
    """
    Backward error analysis via graded comonadic types + strict linearity.
    
    Type !_s σ = data of type σ scaled by sensitivity factor s
    """
    # Bean uses:
    # Graded comonads for sensitivity
    # Strict linearity for perturbation analysis
    
    return TypeDerivation(program, sensitivity=s)


# Algorithm 3: Sensitivity Analysis

def sensitivity_type(f):
    """
    Determine sensitivity c for function f.
    
    f: X → Y is c-sensitive if:
    d_Y(f(x), f(y)) ≤ c · d_X(x, y)
    """
    # Example: f(x) = x²
    # RP(x², y²) = |ln(x²/y²)| = 2|ln(x/y)| = 2·RP(x, y)
    # Sensitivity = 2
    
    return 2  # f : !_2 num ⊸ num


def analyze_sensitivity(expression):
    """
    Compositional sensitivity analysis.
    """
    if is_variable(expression):
        return 1  # !_1
    
    if is_application(expr):
        # Chain rule: sensitivity multiplies
        s1 = analyze_sensitivity(expr.func)
        s2 = analyze_sensitivity(expr.arg)
        return s1 * s2
    
    if is_addition(expr):
        # Addition: sensitivities add (triangle inequality)
        return analyze_sensitivity(expr.left) + analyze_sensitivity(expr.right)
    
    return 1


# Algorithm 4: Forward Error Derivation

def forward_error_derivation(typed_program):
    """
    Derive forward error bound using graded monads.
    
    Error composition: total = s × r + q
    """
    # For sequence: letM x = v in f
    # error = sensitivity(f) × error(v) + error(f)
    
    error_bounds = []
    for term in typed_program:
        if is_literal(term):
            error_bounds.append(0)
        elif is_operation(term):
            # Local error from operation
            local_error = unit_roundoff * complexity(term)
            error_bounds.append(local_error)
        elif is_composition(term):
            # Compose: s × r + q
            s = analyze_sensitivity(term)
            r = error_bounds[-1]
            q = unit_roundoff * complexity(term)
            error_bounds.append(s * r + q)
    
    return max(error_bounds)


# Algorithm 5: Backward Error Derivation

def backward_error_derivation(typed_program):
    """
    Derive backward error bound using graded comonads.
    
    Finds smallest perturbation δx such that f(x + δx) = ỹ
    """
    # Backward stable: ∀x. ∃x̃. f(x̃) = f̃(x) ∧ d(x, x̃) ≤ αu
    
    alpha = compute_condition_number(typed_program)
    
    # Backward error ≤ α × u
    backward_bound = alpha * unit_roundoff
    
    return backward_bound


# Algorithm 6: Relative Precision Metric

def relative_precision(x_tilde, x):
    """
    RP(x̃, x) = |ln(x̃/x)|
    
    Used because:
    - Multiplicative: RP(xy, x̃ỹ) ≤ RP(x, x̃) + RP(y, ỹ)
    - Composable: error bounds combine via addition
    """
    import math
    return abs(math.log(x_tilde / x))


def compose_rp_metrics(errors):
    """
    RP(xy, x̃ỹ) ≤ RP(x, x̃) + RP(y, ỹ)
    """
    return sum(errors)


# Algorithm 7: Floating-Point Error Model

def floating_point_operation(x, y, op):
    """
    fl(x ◦ y) = (x ◦ y)(1 + δ)  where |δ| ≤ u
    
    Returns: (result, error_bound)
    """
    u = unit_roundoff()  # ~1.1e-16 for binary64
    
    if op == '+':
        result = x + y
    elif op == '-':
        result = x - y
    elif op == '*':
        result = x * y
    elif op == '/':
        result = x / y
    
    # Error bound
    error_bound = abs(result) * u
    
    return result, error_bound


# Algorithm 8: Condition Number Computation

def condition_number(f, x):
    """
    κ = |x · f'(x) / f(x)|
    
    For f(x) = x²: κ = |x · 2x / x²| = 2
    """
    import numpy as np
    
    h = 1e-8
    f_prime = (f(x + h) - f(x - h)) / (2 * h)
    
    kappa = abs(x * f_prime / f(x))
    
    return kappa


# Algorithm 9: Compositional Error Derivation

def derive_error_bound(expr, env):
    """
    Compositional derivation of error bounds.
    
    Using: total_error = s × r + q
    """
    if is_literal(expr):
        return 0, 1  # error=0, sensitivity=1
    
    if is_var(expr):
        return env[expr], 1
    
    if is_add(expr):
        e1, s1 = derive_error_bound(expr.left, env)
        e2, s2 = derive_error_bound(expr.right, env)
        
        # Addition: errors add, sensitivities add
        total_error = e1 + e2 + unit_roundoff()
        sensitivity = s1 + s2
        
        return total_error, sensitivity
    
    if is_mult(expr):
        e1, s1 = derive_error_bound(expr.left, env)
        e2, s2 = derive_error_bound(expr.right, env)
        
        # Multiplication: errors compose
        total_error = s1 * e2 + s2 * e1 + e1 * e2 + unit_roundoff()
        sensitivity = s1 * s2
        
        return total_error, sensitivity
    
    return 0, 1
```

### Type System Summary

| System | Mechanism | Purpose |
|--------|-----------|---------|
| NumFuzz | Graded Monad (M_q) | Forward error bounds |
| Bean | Graded Comonad (!_s) + Linearity | Backward error bounds |

### Typing Rules

```
-- Monadic sequencing (forward error)
Γ ⊢ v : M_r σ    Θ, x:_s σ ⊢ f : M_q τ
───────────────────────────────────────────
Γ + Θ ⊢ letM x = v in f : M_{s·r + q} τ

-- Comonadic elimination (sensitivity)
Γ ⊢ v : !_s σ    Θ, x:_{t·s} σ ⊢ e : τ
───────────────────────────────────────────
t·Γ + Θ ⊢ let [x] = v in e : τ
```

### Bounded Types

```purescript
-- Error bounds as grades
newtype ForwardError = ForwardError Number
newtype BackwardError = BackwardError Number
newtype Sensitivity = Sensitivity Number

-- Graded monad for forward error
data ErrorM q a = ErrorM
  { value :: a
  , forwardBound :: ForwardError
  }

-- Graded comonad for sensitivity  
data SensitivityC s a = SensitivityC
  { value :: a
  , sensitivity :: Sensitivity
  }

-- Numeric types with precision grades
data Precision
  = Binary32    -- u ≈ 5.96e-8
  | Binary64    -- u ≈ 1.11e-16  
  | Binary16    -- u ≈ 0.0009765625

data NumericType p a = NumericType
  { value :: a
  , precision :: Precision
  , errorBound :: ForwardError
  }

-- Composition
composeErrors :: ErrorM r a -> (a -> ErrorM q b) -> ErrorM (s * r + q) b
composeSensitivity :: SensitivityC s a -> (a -> SensitivityC t b) -> SensitivityC (t * s) b
```

### Grade Tracking

```purescript
data Effect
  = AnalyzeForwardError
  | AnalyzeBackwardError
  | TrackRounding

data CoEffect
  = NeedsPrecision Precision
  | NeedsSensitivity Sensitivity
  | NeedsErrorBound ForwardError
```

---

## PATHTRACING_SDF (Ray Tracing SDF Grids)

### Classification
- **Domain**: Computer Graphics / Ray Tracing
- **Effect**: Render(SDF), Intersect(Ray), Compute(Normal)
- **Coeffect**: Resolution, MaxBounces, VoxelSize

### AST Schema
```json
{
  "algorithm": "SDFPathTracing",
  "inputs": ["ray", "sdf_grid"],
  "outputs": ["hit_point", "normal", "distance"],
  "parameters": {
    "solver": "cubic",
    "continuous_normals": true,
    "shadow_optimization": true
  }
}
```

### Key Formulas

**(1) Trilinear SDF Interpolation**
```
f(x,y,z) = (1-z)[(1-y)((1-x)s000 + xs100) + y((1-x)s010 + xs110)]
         + z[(1-y)((1-x)s001 + xs101) + y((1-x)s011 + xs111)]
```

**(2) Cubic Surface Equation**
```
f(x,y,z) = z(k4 + k5x + k6y + k7xy) - (k0 + k1x + k2y + k3xy) = 0
```

**(3) Ray-Cubic Intersection**
```
c3*t³ + c2*t² + c1*t + c0 = 0
```

**(4) Optimized Coefficients (37 ops)**
```
m0 = ox*oy       m3 = k5*ou - k1
m1 = dx*dy       m4 = k6*ou - k2
m2 = ox*dy + oy*dx  m5 = k7*ou - k3

c0 = (k4*ou - k0) + ox*m3 + oy*m4 + m0*m5
c1 = dx*m3 + dy*m4 + m2*m5 + du*(k4 + k5*ox + k6*oy + k7*m0)
c2 = m1*m5 + du*(k5*dx + k6*dy + k7*m2)
c3 = k7*m1*du
```

**(5) Gradient Normal**
```
n = (∂f/∂x, ∂f/∂y, ∂f/∂z)
```

---

### Core Algorithms

```python
# Algorithm 1: Cubic Solver Coefficients

def compute_cubic_coefficients(sdf_corners, ray_origin, ray_direction):
    """
    Compute cubic polynomial coefficients from SDF corner values.
    Optimized: 37 operations (vs 161 in prior work)
    """
    # Extract 8 corner values
    s000, s100, s010, s110 = sdf_corners[0:4]
    s001, s101, s011, s111 = sdf_corners[4:8]
    
    # k-constants
    k0 = s000
    k1 = s100 - s000
    k2 = s010 - s000
    k3 = s110 - s010 - k1
    a = s101 - s000
    k4 = k0 - s001
    k5 = k1 - a
    k6 = k2 - (s011 - s001)
    k7 = k3 - (s111 - s011 - a)
    
    # Ray components
    ox, oy, oz = ray_origin
    dx, dy, dz = ray_direction
    
    # Intermediate values
    m0 = ox * oy
    m1 = dx * dy
    m2 = ox * dy + oy * dx
    ou = oz
    du = dz
    m3 = k5 * ou - k1
    m4 = k6 * ou - k2
    m5 = k7 * ou - k3
    
    # Cubic coefficients
    c0 = (k4 * ou - k0) + ox * m3 + oy * m4 + m0 * m5
    c1 = dx * m3 + dy * m4 + m2 * m5 + du * (k4 + k5 * ox + k6 * oy + k7 * m0)
    c2 = m1 * m5 + du * (k5 * dx + k6 * dy + k7 * m2)
    c3 = k7 * m1 * du
    
    return [c3, c2, c1, c0]


# Algorithm 2: Analytic Cubic Solver (Vieta)

def solve_cubic_vieta(c3, c2, c1, c0):
    """
    Direct cubic formula using Vieta's method.
    Fastest approach for SDF ray intersection.
    """
    # Normalize
    if abs(c3) > 1e-10:
        c2, c1, c0 = c2/c3, c1/c3, c0/c3
    
    # depressed cubic: t³ + pt + q = 0
    p = (3*c1 - c2*c2) / 9
    q = (2*c2*c2*c2 - 9*c2*c1 + 27*c0) / 27
    discriminant = (q*q/4) + (p*p*p/27)
    
    roots = []
    
    if discriminant > 0:
        # One real root
        sqrt_d = sqrt(discriminant)
        u = -q/2 + sqrt_d
        v = -q/2 - sqrt_d
        if u > 0: t = cbrt(u)
        else: t = -cbrt(-u)
        if v > 0: s = cbrt(v)
        else: s = -cbrt(-v)
        roots.append(t + s - c2/3)
    else:
        # Three real roots (use trig method)
        if abs(p) < 1e-10:
            roots.append(cbrt(-c0) - c2/3)
        else:
            mp = 2 * sqrt(-p/3)
            theta = acos(-q/2 / sqrt(-p*p*p/27))
            for k in range(3):
                roots.append(mp * cos((theta + 2*pi*k)/3) - c2/3)
    
    # Filter: positive roots within voxel bounds
    valid = [r for r in roots if r > 0 and r < 1]
    return min(valid) if valid else None


# Algorithm 3: Continuous Normal (Dual Voxel)

def compute_continuous_normal(sdf_corners, hit_point, voxel_size):
    """
    Dual voxel interpolation for smooth normals.
    1-7% performance cost for C0 continuity.
    """
    x, y, z = hit_point
    
    # Compute partial derivatives
    def lerp(t, a, b): return (1-t)*a + t*b
    
    # ∂f/∂x
    y0 = lerp(y, s100-s000, s110-s010)
    y1 = lerp(y, s101-s001, s111-s011)
    dx = lerp(z, y0, y1)
    
    # ∂f/∂y
    x0 = lerp(x, s010-s000, s110-s100)
    x1 = lerp(x, s011-s001, s111-s101)
    dy = lerp(z, x0, x1)
    
    # ∂f/∂z
    z0 = lerp(y, s001-s000, s101-s100)
    z1 = lerp(y, s011-s010, s111-s110)
    dz = -lerp(x, z0, z1)
    
    # Normalize
    length = sqrt(dx*dx + dy*dy + dz*dz + 1e-10)
    return [dx/length, dy/length, dz/length]


# Algorithm 4: Shadow Ray with Early Termination

def trace_shadow_ray(origin, direction, sdf_grid, light_pos):
    """
    Shadow ray with polynomial splitting for early termination.
    """
    t = 0
    max_dist = length(light_pos - origin)
    
    while t < max_dist:
        p = origin + direction * t
        d = sdf_sample(sdf_grid, p)
        
        if d < 0.001:
            return 0.0  # In shadow
        
        # Polynomial splitting: check if we can skip ahead
        if can_skip_to_next_voxel(d, direction):
            t += d
        else:
            t += d
    
    return 1.0  # Fully lit


# Algorithm 5: SDF Grid Traversal

def trace_ray_sdf(ray_origin, ray_dir, sdf_grid):
    """
    Main ray-SDF intersection using analytic cubic solver.
    """
    t = 0
    max_dist = 100.0  # Far plane
    
    while t < max_dist:
        voxel = get_voxel(sdf_grid, ray_origin + ray_dir * t)
        
        if voxel is None:
            break
        
        corners = get_sdf_corners(voxel)
        
        # Skip empty voxels
        if all(c > 0 for c in corners):
            t += voxel_size
            continue
        
        # Analytic intersection
        coeffs = compute_cubic_coefficients(corners, ray_origin, ray_dir)
        t_hit = solve_cubic_vieta(*coeffs)
        
        if t_hit and t_hit > 0:
            hit_point = ray_origin + ray_dir * t_hit
            normal = compute_continuous_normal(corners, hit_point, voxel_size)
            return Hit(t_hit, hit_point, normal)
        
        t += voxel_size
    
    return None


# Algorithm 6: Path Tracing with SDF

def path_trace_sdf(scene, ray_origin, ray_dir, max_bounces=4):
    """
    Path tracing using SDF geometry.
    """
    color = [0, 0, 0]
    throughput = [1, 1, 1]
    
    for bounce in range(max_bounces):
        hit = trace_ray_sdf(ray_origin, ray_dir, scene.sdf_grid)
        
        if not hit:
            color += throughput * scene.background
            break
        
        # Material
        material = get_material(scene, hit.point)
        
        # Direct lighting
        for light in scene.lights:
            shadow = trace_shadow_ray(hit.point, light.direction, scene.sdf_grid)
            if shadow > 0:
                Ld = material BRDF * light.color * shadow * dot(hit.normal, light.direction)
                color += throughput * Ld
        
        # Russian roulette for path termination
        if bounce > 2:
            if random() > continue_probability:
                break
        
        # Next bounce
        ray_dir = material.sample_hemisphere(hit.normal)
        ray_origin = hit.point + hit.normal * 0.001
        throughput *= material.albedo
    
    return color
```

### Performance Results

| Optimization | Speedup |
|--------------|---------|
| Cubic solver (37 ops vs 161) | 2-3× |
| Continuous normals | 1.01-1.07× |
| Shadow early termination | 1.5-2× |

### Bounded Types

```purescript
-- SDF Types
newtype VoxelSize = VoxelSize Number
newtype MaxBounces = MaxBounces (BoundedInt 1 16)

data SDFGrid = SDFGrid
  { resolution :: Vec3 Int
  , voxelSize :: VoxelSize
  , data :: Array Number
  }

data Ray = Ray
  { origin :: Vec3
  , direction :: Vec3
  }

data HitResult = HitResult
  { distance :: Number
  , point :: Vec3
  , normal :: Vec3
  }

-- Cubic coefficients
data CubicCoeffs = CubicCoeffs
  { c0 :: Number
  , c1 :: Number
  , c2 :: Number
  , c3 :: Number
  }
```

### Grade Tracking

```purescript
data Effect
  = RenderSDF
  | IntersectRay
  | ComputeNormal
  | TraceShadows

data CoEffect
  = NeedsResolution Vec3
  | NeedsMaxBounces MaxBounces
  | NeedsVoxelSize VoxelSize
  | NeedsGPUCompute
```

---

## GEOMCLIPMAP (Geometry Clipmaps Terrain Rendering)

### Classification
- **Domain**: Computer Graphics / Terrain Rendering
- **Effect**: Render(Terrain), Update(Clipmap), Morph(Levels)
- **Coeffect**: ViewDistance, GridSize, CompressionRatio

### AST Schema
```json
{
  "algorithm": "GeometryClipmaps",
  "inputs": ["viewer_position", "terrain_data"],
  "outputs": ["rendered_mesh", "clipmap_state"],
  "parameters": {
    "num_levels": 11,
    "grid_size": 255,
    "compression": 100
  }
}
```

### Key Formulas

**(1) Grid Spacing per Level**
```
g_l = 2^(-l)
```

**(2) Clipmap Memory**
```
Memory = m × n² × 16 + m × (2n)² × 2  bytes
```

**(3) L-Shaped Update Region**
```
new_region = L-shaped area between old_clip and new_clip
```

**(4) Transition Morphing**
```
z_morphed = lerp(z_fine, z_coarse, t)
where t = transition_factor(viewer_distance)
```

---

### Core Algorithms

```python
# Algorithm 1: Initialize Geometry Clipmap

def init_geometry_clipmap(terrain, num_levels=11, grid_size=255):
    clipmap = []
    for l in range(num_levels):
        spacing = 2 ** (-l)
        level = {
            'vertices': zeros(grid_size, grid_size, 4),
            'normals': zeros(2*grid_size, 2*grid_size, 2),
            'clip_region': None,
            'spacing': spacing
        }
        clipmap.append(level)
    return clipmap


# Algorithm 2: Toroidal Update

def toroidal_access(array, x, y, n):
    return array[x % n][y % n]


def update_L_region(clip_level, old_clip, new_clip, terrain):
    n = clip_level.shape[0]
    spacing = clip_level['spacing']
    
    x_min = min(old_clip.x_min, new_clip.x_min)
    x_max = max(old_clip.x_max, new_clip.x_max)
    y_min = min(old_clip.y_min, new_clip.y_min)
    y_max = max(old_clip.y_max, new_clip.y_max)
    
    if new_clip.x_min < old_clip.x_min:
        for y in range(y_min, y_max):
            for x in range(new_clip.x_min, old_clip.x_min):
                wx, wy = world_from_grid(x, y, spacing, new_clip.center)
                h = terrain.sample_height(wx, wy)
                clip_level[x % n][y % n] = [wx, wy, h, h]
    
    if new_clip.x_max > old_clip.x_max:
        for y in range(y_min, y_max):
            for x in range(old_clip.x_max, new_clip.x_max):
                wx, wy = world_from_grid(x, y, spacing, new_clip.center)
                h = terrain.sample_height(wx, wy)
                clip_level[x % n][y % n] = [wx, wy, h, h]
    
    if new_clip.y_min < old_clip.y_min:
        for x in range(x_min, x_max):
            for y in range(new_clip.y_min, old_clip.y_min):
                wx, wy = world_from_grid(x, y, spacing, new_clip.center)
                h = terrain.sample_height(wx, wy)
                clip_level[x % n][y % n] = [wx, wy, h, h]
    
    if new_clip.y_max > old_clip.y_max:
        for x in range(x_min, x_max):
            for y in range(old_clip.y_max, new_clip.y_max):
                wx, wy = world_from_grid(x, y, spacing, new_clip.center)
                h = terrain.sample_height(wx, wy)
                clip_level[x % n][y % n] = [wx, wy, h, h]


# Algorithm 3: Compute Active Regions

def compute_active_regions(clipmap, viewer_pos, grid_size):
    active_regions = []
    for l, level in enumerate(clipmap):
        spacing = level['spacing']
        half_size = grid_size * spacing / 2
        active = {
            'x_min': viewer_pos.x - half_size,
            'x_max': viewer_pos.x + half_size,
            'y_min': viewer_pos.y - half_size,
            'y_max': viewer_pos.y + half_size
        }
        active_regions.append(active)
    return active_regions


# Algorithm 4: Update Clipmap Per Frame

def update_geometry_clipmap(clipmap, viewer_pos, terrain, grid_size):
    active_regions = compute_active_regions(clipmap, viewer_pos, grid_size)
    for l, level in enumerate(clipmap):
        new_clip = active_regions[l]
        if level['clip_region'] is None:
            level['clip_region'] = new_clip
            fill_entire_level(level, terrain)
        else:
            old_clip = level['clip_region']
            if (abs(new_clip.x_min - old_clip.x_min) > level['spacing'] or
                abs(new_clip.y_min - old_clip.y_min) > level['spacing']):
                update_L_region(level, old_clip, new_clip, terrain)
                level['clip_region'] = new_clip
    return clipmap


# Algorithm 5: Transition Morphing

def apply_morphing(vertex, viewer_distance, morph_start, morph_end):
    if viewer_distance < morph_start:
        return vertex.z_fine
    elif viewer_distance > morph_end:
        return vertex.z_coarse
    else:
        t = (viewer_distance - morph_start) / (morph_end - morph_start)
        t = t * t * (3 - 2 * t)
        return lerp(vertex.z_fine, vertex.z_coarse, t)


# Algorithm 6: Render Clipmap Level

def render_clipmap_level(level, viewer_pos, morph_start, morph_end):
    vertices = level['vertices']
    rendered = []
    for i in range(vertices.shape[0]):
        for j in range(vertices.shape[1]):
            v = vertices[i][j]
            dist = sqrt((v.x - viewer_pos.x)**2 + (v.y - viewer_pos.y)**2)
            z = apply_morphing(v, dist, morph_start, morph_end)
            rendered.append(Vertex(x=v.x, y=v.y, z=z))
    return rendered


# Algorithm 7: Normal Computation

def compute_normals(clip_level, terrain):
    n = clip_level.shape[0]
    normals = zeros(2*n, 2*n, 2)
    for i in range(2*n):
        for j in range(2*n):
            h_L = sample_height(i-1, j, terrain)
            h_R = sample_height(i+1, j, terrain)
            h_D = sample_height(i, j-1, terrain)
            h_U = sample_height(i, j+1, terrain)
            normals[i][j] = [(h_L - h_R) / 2, (h_D - h_U) / 2]
    return normals


# Algorithm 8: Compression

def compress_clipmap(level):
    return run_length_encode(level.vertices)


def decompress_clipmap(compressed):
    return run_length_decode(compressed)
```

### Performance Results

| Metric | Value |
|--------|-------|
| Frame rate | 60 fps |
| VRAM usage | ~17 MB |
| Compression | 100:1 |
| Error | < 1 pixel |

### Bounded Types

```purescript
newtype NumLevels = NumLevels (BoundedInt 1 20)
newtype GridSize = GridSize (BoundedInt 64 512)

data ClipLevel = ClipLevel
  { vertices :: Array4D Number
  , normals :: Array2D Vec2
  , clipRegion :: Rectangle
  , spacing :: Number
  }

data GeometryClipmap = GeometryClipmap
  { levels :: Array ClipLevel
  , viewerPosition :: Vec2
  }

data Rectangle = Rectangle
  { xMin :: Number, xMax :: Number
  , yMin :: Number, yMax :: Number
  }
```

### Grade Tracking

```purescript
data Effect
  = RenderTerrain
  | UpdateClipmap
  | ComputeNormals
  | MorphLevels

data CoEffect
  = NeedsNumLevels NumLevels
  | NeedsGridSize GridSize
  | NeedsVRAM Int
```

---

## CONSTRAINT_TRANSPORT (Thermodynamic Video Generation)

### Classification
- **Domain**: Video Generation / Precision Management
- **Effect**: Generate(Video), Manage(Precision), Preserve(Edges)
- **Coeffect**: Entropy, Timestep, Precision

### AST Schema
```json
{
  "algorithm": "ConstraintTransport",
  "inputs": ["video_latents", "timestep_schedule"],
  "outputs": ["generated_video"],
  "parameters": {
    "precision_schedule": "entropy_matched",
    "hyperbolic_correction": true
  }
}
```

### Key Formulas

**(1) Parabolic vs Hyperbolic**
```
Parabolic: ∂ₜu = -Δu        (destroys wavefronts)
Hyperbolic: ∂ₜu + v·∇u = 0  (preserves wavefronts)
```

**(2) Optimal Bit-Width**
```
b*(ε) = min{ b | E[D(φ(x), φ(Q_b(x)))] ≤ ε }
```

**(3) Wavefront Set**
```
WF(u) = {(x, ξ) | ξ ≠ 0 at singularities}
```

**(4) Entropy Estimation**
```
H(z_t) = -Σ p_i log p_i
```

---

### Core Algorithms

```python
# Algorithm 1: Entropy-Based Precision Selection

def select_precision(timestep, latent):
    """
    Entropy-matched precision scheduling.
    
    Phase       | t       | Entropy | Precision
    -----------|---------|---------|----------
    High-noise  | t > 0.8 | H < 4   | NVFP4
    Semantic   | 0.4-0.8 | 4-8     | FP16
    Refinement | t < 0.4 | H > 8   | FP8
    """
    H = estimate_entropy(latent)
    
    if H < 4:
        return "NVFP4"
    elif H < 8:
        return "FP16"
    else:
        return "FP8"


def estimate_entropy(latent, method="histogram"):
    """
    Approximate H(z_t) via histogram or KDE.
    """
    if method == "histogram":
        hist = compute_histogram(latent, bins=256)
        p = hist / hist.sum()
        H = -np.sum(p * np.log(p + 1e-10))
    else:
        H = kde_entropy(latent)
    
    return H


# Algorithm 2: Precision Schedule

def precision_schedule(timesteps):
    """
    Generate precision for each timestep.
    """
    schedule = []
    for t in timesteps:
        if t > 0.8:
            precision = "NVFP4"
        elif t > 0.4:
            precision = "FP16"
        else:
            precision = "FP8"
        schedule.append(precision)
    return schedule


# Algorithm 3: Hyperbolic Constraint Transport

def hyperbolic_correction(velocity_field, latent):
    """
    Apply hyperbolic dynamics to preserve edges.
    
    ∂ₜu + v·∇u = 0
    
    Counteracts diffusive blurring.
    """
    # Compute velocity field from motion
    v = compute_motion_field(latent)
    
    # Advection step
    corrected = advect(latent, v)
    
    return corrected


def advect(field, velocity):
    """
    Semi-Lagrangian advection.
    """
    result = zeros_like(field)
    
    for i in range(field.shape[0]):
        for j in range(field.shape[1]):
            # Trace back
            x_back = i - velocity[i, j, 0]
            y_back = j - velocity[i, j, 1]
            
            # Bilinear interpolation
            result[i, j] = bilinear_sample(field, x_back, y_back)
    
    return result


# Algorithm 4: Constraint Transport Update

def constraint_transport_update(latent_t, latent_t_plus_1, velocity, dt):
    """
    Constraint transport maintains divergence-free velocity.
    
    Key: Preserves singular structures (edges, textures)
    while allowing smooth evolution.
    """
    # Predictor: hyperbolic step
    latent_star = hyperbolic_correction(latent_t, velocity)
    
    # Corrector: diffusion for stability
    latent_next = latent_star + dt * diffuse(latent_star)
    
    return latent_next


# Algorithm 5: Gauge Transition

def gauge_transition(latent, from_prec, to_prec):
    """
    Cost-free precision transition if injective on support.
    
    Key insight: gauge transitions are lossless
    when signal is within quantization grid.
    """
    if is_injective(latent, from_prec):
        # No information loss
        return quantize(latent, to_prec)
    else:
        # Need careful transition
        return careful_quantize(latent, from_prec, to_prec)


# Algorithm 6: Video Generation with Constraint Transport

def generate_video_constraint_transport(model, initial_frame, num_frames, 
                                       use_constraint_transport=True):
    """
    Full video generation with thermodynamic precision.
    """
    latents = [model.encode(initial_frame)]
    
    for t in reversed(range(num_timesteps)):
        # Select precision based on entropy
        precision = select_precision(t, latents[-1])
        
        # Denoising step
        latent = model.denoise_step(latents[-1], t, precision)
        
        # Apply hyperbolic correction if needed
        if use_constraint_transport and t < 0.5:
            velocity = compute_motion_field(latent)
            latent = constraint_transport_update(latent, velocity)
        
        latents.append(latent)
    
    # Decode
    video = model.decode(latents)
    
    return video
```

### Precision Schedule Results

| Phase | Timestep | Entropy | Precision | Speedup |
|-------|----------|---------|-----------|---------|
| High-noise | t > 0.8 | < 4 bits | NVFP4 | 2× |
| Semantic | 0.4-0.8 | 4-8 bits | FP16 | 1.5× |
| Refinement | t < 0.8 | > 8 bits | FP8 | 1.2× |

**Total: 1.8× speedup** over FP16 baseline

### Bounded Types

```purescript
-- Precision types
data Precision
  = NVFP4
  | FP8
  | FP16
  | BF16

newtype Entropy = Entropy Number  -- bits
newtype Timestep = Timestep Number  -- [0, 1]

data EntropyPhase
  = HighNoise    -- H < 4
  | Semantic     -- 4 ≤ H < 8  
  | Refinement   -- H ≥ 8

-- Hyperbolic dynamics
data VelocityField = VelocityField (Array2D Vec2)

data ConstraintState = ConstraintState
  { velocity :: VelocityField
  , divergence :: Number
  , latent :: Array
  }
```

### Grade Tracking

```purescript
data Effect
  = GenerateVideo
  | ManagePrecision
  | TransportConstraints
  | PreserveEdges

data CoEffect
  = NeedsEntropy Entropy
  | NeedsTimestep Timestep
  | NeedsPrecision Precision
  | NeedsHyperbolicDynamics
```

---

## DEEPSEEK_R1 (Reinforcement Learning for Reasoning)

### Classification
- **Domain**: AI / Reinforcement Learning / Reasoning
- **Effect**: Reason(ChainOfThought), Optimize(Policy), Compute(GRPO)
- **Coeffect**: GroupSize, RewardScale,思考深度

### AST Schema
```json
{
  "algorithm": "DeepSeekR1",
  "inputs": ["question", "policy_model", "reward_function"],
  "outputs": ["reasoning_output", "policy_update"],
  "parameters": {
    "group_size": 16,
    "clip_epsilon": 0.2,
    "kl_beta": 0.1
  }
}
```

### Key Formulas

**(1) GRPO Advantage**
```
A_i = (r_i - mean(r)) / std(r)
```

**(2) PPO Clipped Objective**
```
L = -min(ratio × A, clip(ratio, 1-ε, 1+ε) × A)
```

**(3) Reward**
```
R = R_accuracy + R_format + R_length
```

---

### Core Algorithms

```python
# Algorithm 1: GRPO Objective

def grpo_objective(policy, policy_ref, question, G=16):
    """
    GRPO: Group Relative Policy Optimization.
    
    Samples G outputs, computes relative advantage.
    """
    outputs = [policy.sample(question) for _ in range(G)]
    
    rewards = [get_reward(o) for o in outputs]
    
    mean_r = np.mean(rewards)
    std_r = np.std(rewards) + 1e-8
    advantages = [(r - mean_r) / std_r for r in rewards]
    
    loss = 0
    for o, A in zip(outputs, advantages):
        ratio = policy.log_prob(o) - policy_old.log_prob(o)
        clipped = np.clip(ratio, 1-0.2, 1+0.2)
        policy_loss = -min(ratio * A, clipped * A)
        
        kl = kl_divergence(policy, policy_ref, o)
        loss += policy_loss + 0.1 * kl
    
    return loss / G


# Algorithm 2: DeepSeek-R1-Zero Training

def train_deepseek_r1(policy, questions, num_iterations):
    """
    Pure RL without supervised fine-tuning.
    """
    for iteration in range(num_iterations):
        for q in questions:
            outputs = [policy.sample(q) for _ in range(16)]
            
            rewards = [compute_reward(o) for o in outputs]
            
            advantages = normalize_within_group(rewards)
            
            loss = grpo_loss(policy, outputs, advantages)
            
            loss.backward()
            optimizer.step()
            optimizer.zero_grad()


# Algorithm 3: Reward Computation

def compute_reward(output, answer):
    """
    Rule-based rewards: accuracy + format + length penalty.
    """
    reward = 0
    
    # Accuracy reward
    if extract_answer(output) == answer:
        reward += 1.0
    
    # Format reward (has <thinking> tags)
    if "<thinking>" in output and "</thinking>" in output:
        reward += 0.1
    
    # Length penalty (prefer concise)
    if len(output) > 2000:
        reward -= 0.1
    
    return reward


# Algorithm 4: Chain-of-Thought Extraction

def extract_thinking(output):
    """
    Extract reasoning between <thinking> tags.
    """
    if "<thinking>" in output:
        start = output.find("<thinking>")
        end = output.find("</thinking>")
        if end > start:
            return output[start:end]
    return ""


# Algorithm 5: Group Relative Advantage

def compute_grpo_advantages(rewards):
    """
    Normalize rewards within group.
    """
    mean_r = np.mean(rewards)
    std_r = np.std(rewards) + 1e-8
    
    advantages = [(r - mean_r) / std_r for r in rewards]
    
    return advantages


# Algorithm 6: AIME Evaluation

def evaluate_reasoning(model, aime_questions):
    """
    Test on American Invitational Mathematics Examination.
    """
    correct = 0
    
    for q in aime_questions:
        output = model.generate(q)
        
        if extract_answer(output) == q.answer:
            correct += 1
    
    accuracy = correct / len(aime_questions)
    
    return accuracy
```

### Results

| Model | AIME Accuracy |
|-------|--------------|
| DeepSeek-R1-Zero | 71% |
| DeepSeek-R1 | 86% |
| OpenAI o1 | 74.4% |

### Bounded Types

```purescript
-- RL Types
newtype GroupSize = GroupSize (BoundedInt 1 64)
newtype ClipEpsilon = ClipEpsilon Number
newtype KLBeta = KLBeta Number

data Policy = Policy
  { parameters :: Array Number
  , log_probs :: Array Number
  }

data Reward = Reward
  { accuracy :: Number
  , format :: Number
  , length :: Number
  }

newtype Advantage = Advantage Number

data GRPOState = GRPOState
  { outputs :: Array String
  , rewards :: Array Reward
  , advantages :: Array Advantage
  }
```

### Grade Tracking

```purescript
data Effect
  = SampleOutputs
  = ComputeReward
  | OptimizePolicy
  | ExtractReasoning

data CoEffect
  = NeedsGroupSize GroupSize
  | NeedsClipEpsilon ClipEpsilon
  | NeedsKLBeta KLBeta
  | NeedsRewardFunction
```

---

## GAIA2_WORLD_MODEL (Controllable Multi-View Driving World Model)

### Classification
- **Domain**: Autonomous Driving / World Models / Video Generation
- **Effect**: Generate(Video), Predict(Motion), Condition(Action)
- **Coeffect**: CameraCount, Resolution, TemporalWindow

### AST Schema
```json
{
  "algorithm": "GAIA2",
  "inputs": ["video_frames", "ego_actions", "agent_boxes", "metadata"],
  "outputs": ["generated_video", "predicted_trajectory"],
  "parameters": {
    "model_params": "8.4B",
    "spatial_compression": 32,
    "temporal_compression": 8,
    "latent_dim": 64
  }
}
```

### Key Formulas

**(1) Symlog Transform**
```
symlog(y) = sign(y) × log(1 + s×|y|) / log(1 + s×|y_max|)
```

**(2) Flow Matching**
```
x_τ = τ × x + (1 - τ) × ε  where ε ~ N(0, I)
v_target = x - ε
```

**(3) Latent Compression**
```
compression_ratio = (Tv×Hv×Wv×3)/(T×H×W×L) ≈ 400×
```

**(4) Bimodal Time Distribution**
```
τ ~ 0.8 × N(0.5, 1.4) + 0.2 × N(-3.0, 1.0)
```

---

### Core Algorithms

```python
# Algorithm 1: Video Tokenizer Encoder

def video_tokenizer_encoder(video, T=24):
    """
    Compress video to latent space.
    
    Spatial: 32× downsample
    Temporal: 8× downsample
    """
    # Input: [B, T, 3, H, W]
    x = conv3d_downsample(video, stride=(2, 8, 8))  # [B, T/8, 512, H/16, W/16]
    x = conv3d_downsample(x, stride=(2, 2, 2))      # [B, T/16, 512, H/32, W/32]
    
    # Spatial transformer blocks
    for _ in range(24):
        x = spatial_transformer(x, heads=16)
    
    # Project to latent dimension
    z = conv3d_final(x, stride=(1, 2, 2))  # [B, T/64, 64, H/64, W/64]
    
    # Sample from Gaussian
    mu, sigma = split(z, dim=1)
    z = mu + sigma * randn_like(sigma)
    
    return z  # [B, T_L, 64, H_L, W_L]


# Algorithm 2: Video Tokenizer Decoder

def video_tokenizer_decoder(latents):
    """
    Decode latents to video with temporal consistency.
    """
    x = linear_upsample(latents)  # [B, T, 512, H, W]
    
    # Space-time factorized transformers
    for _ in range(16):
        x = spacetime_transformer(x)
    
    x = conv3d_upsample(x, stride=(1, 2, 2))
    
    for _ in range(8):
        x = spacetime_transformer(x)
    
    video = conv3d_upsample_final(x, stride=(2, 8, 8))  # [B, T, 3, H, W]
    
    return video


# Algorithm 3: Flow Matching Training

def flow_matching_train(model, video, context, actions):
    """
    Train world model with flow matching.
    """
    # Sample time from bimodal distribution
    if random() < 0.8:
        tau = np.random.normal(0.5, 1.4)
    else:
        tau = np.random.normal(-3.0, 1.0)
    tau = np.clip(tau, 0.01, 0.99)
    
    # Sample noise
    epsilon = torch.randn_like(video_latents)
    
    # Interpolate
    x_tau = tau * video_latents + (1 - tau) * epsilon
    
    # Encode conditioning
    ego_emb = encode_ego_action(actions)
    agent_emb = encode_agents(agent_boxes, camera_params)
    meta_emb = encode_metadata(weather, time, geography)
    
    # Predict velocity
    v_pred = model(x_tau, tau, ego_emb, agent_emb, meta_emb)
    
    # Target velocity
    v_target = video_latents - epsilon
    
    # Loss
    loss = MSE(v_pred, v_target)
    
    return loss


# Algorithm 4: Adaptive Layer Norm

def adaptive_layer_norm(x, condition, time_emb):
    """
    Inject condition and time into layer normalization.
    """
    gamma = mlp(condition) + mlp(time_emb)
    beta = mlp(condition) + mlp(time_emb)
    
    # norm(x) * (1 + gamma) + beta
    return (x - mean(x)) / std(x) * (1 + gamma) + beta


# Algorithm 5: Camera Geometry Encoding

def encode_camera(intrinsics, extrinsics, distortion):
    """
    Encode camera parameters for multi-view consistency.
    """
    f_x, f_y, c_x, c_y = split(intrinsics, dim=-1)
    intr_emb = mlp(normalize([f_x, f_y, c_x, c_y]))
    
    extr_emb = mlp(flatten(extrinsics))
    dist_emb = mlp(distortion)
    
    return intr_emb + extr_emb + dist_emb


# Algorithm 6: Dynamic Agent Conditioning

def encode_agents(bounding_boxes_3d, camera_params):
    """
    Encode dynamic agents as conditioning features.
    
    Per box: location, dimensions, orientation, category
    """
    # Project 3D to 2D
    boxes_2d = project_3d_to_2d(bounding_boxes_3d, camera_params)
    boxes_norm = normalize(boxes_2d)
    
    # Embed each feature
    features = mlp_per_feature(boxes_norm)
    
    return features  # Cross-attention keys/values


# Algorithm 7: Symlog Transform

def symlog(y, scale=1.0, y_max=1.0):
    """
    Symmetric logarithmic transform for unbounded inputs.
    """
    return np.sign(y) * np.log(1 + scale * np.abs(y)) / np.log(1 + scale * y_max)


def symexp(y, scale=1.0, y_max=1.0):
    """
    Inverse of symlog.
    """
    return np.sign(y) * (np.exp(np.abs(y) * np.log(1 + scale * y_max)) - 1) / scale


# Algorithm 8: Multi-Camera Generation

def generate_multi_camera(model, context, actions, camera_configs):
    """
    Generate temporally consistent multi-camera video.
    """
    videos = []
    
    for camera in camera_configs:
        # Encode camera geometry
        cam_emb = encode_camera(camera.intrinsics, camera.extrinsics, camera.distortion)
        
        # Generate with shared conditioning
        video = model.generate(
            context=context,
            actions=actions,
            camera_condition=cam_emb
        )
        videos.append(video)
    
    return videos  # All cameras consistent


# Algorithm 9: Context Rollout

def context_rollout(model, observed_frames, future_actions, num_steps):
    """
    Continue from observed context into future.
    """
    latents = tokenizer.encode(observed_frames)
    
    for t in range(num_steps):
        # Encode action
        action_emb = encode_ego_action(future_actions[t])
        
        # Predict next latent
        next_latent = model.predict(latents, action_emb)
        latents.append(next_latent)
    
    # Decode
    video = tokenizer.decode(latents)
    
    return video


# Algorithm 10: Spatial Inpainting

def spatial_inpaint(model, partial_scene, mask, actions):
    """
    Edit specific regions while keeping others consistent.
    """
    latent = tokenizer.encode(partial_scene)
    
    # Mask in latent space
    latent_mask = F.interpolate(mask, size=latent.shape[2:])
    
    # Generate with mask
    inpainted = model.generate(
        latents=latent,
        mask=latent_mask,
        actions=actions
    )
    
    return tokenizer.decode(inpainted)
```

### Architecture Summary

| Component | Parameters | Specification |
|-----------|------------|---------------|
| Tokenizer Encoder | 85M | Space-time transformer |
| Tokenizer Decoder | 200M | Asymmetric |
| World Model | 8.4B | 22 blocks, 4096 dim |
| Compression | 400× | 32× spatial, 8× temporal |

### Generation Modes

| Mode | Input | Output |
|------|-------|--------|
| From Scratch | Random noise | Novel scene |
| Context Rollout | Past frames + actions | Predicted future |
| Spatial Inpaint | Partial + mask + actions | Edited scene |

### Bounded Types

```purescript
-- Video Latent
newtype TemporalWindow = TemporalWindow (BoundedInt 1 256)
newtype CameraCount = CameraCount (BoundedInt 1 12)
newtype LatentDim = LatentDim (BoundedInt 32 128)

data VideoLatent = VideoLatent
  { temporal :: Array TemporalWindow
  , spatial :: Array2D Vector
  , cameras :: Array CameraCount
  }

-- Conditioning
data EgoAction = EgoAction
  { speed :: Number      -- m/s
  , curvature :: Number  -- 1/m
  }

data AgentBox = AgentBox
  { position :: Vec3
  , dimensions :: Vec3
  , orientation :: Vec3
  , category :: AgentCategory
  }

data AgentCategory
  = Vehicle | Pedestrian | Cyclist | Other

data Metadata = Metadata
  { weather :: WeatherCondition
  , timeOfDay :: Hour
  , geography :: Country
  }

data WeatherCondition = Sunny | Cloudy | Rainy | Foggy | Night

-- World Model
data WorldModelOutput = WorldModelOutput
  { video :: VideoLatent
  , trajectory :: Array Vec3
  }
```

### Grade Tracking

```purescript
data Effect
  = GenerateVideo
  | PredictTrajectory
  | EncodeAgents
  | EncodeCamera

data CoEffect
  = NeedsCameraCount CameraCount
  | NeedsTemporalWindow TemporalWindow
  | NeedsResolution Resolution
  | NeedsMultiAgentSimulation
```

---

## PAN_WORLD_MODEL (General, Interactable, Long-Horizon World Model)

### Classification
- **Domain**: World Models / Video Generation / Long-Horizon Planning
- **Effect**: Predict(World), Condition(Action), Generate(Video)
- **Coeffect**: HorizonLength, LatentDimension, ActionSpace

### AST Schema
```json
{
  "algorithm": "PAN",
  "inputs": ["observations", "actions", "history"],
  "outputs": ["predicted_video", "world_state"],
  "parameters": {
    "encoder": "Qwen2.5-VL-7B",
    "backbone": "Autoregressive LLM",
    "decoder": "Wan2.1-T2V-14B"
  }
}
```

### Key Formulas

**(1) GLP - Generative Latent Prediction**
```
Encoder: ŝ_t ~ p_h(· | o_t)
Predictor: ŝ_{t+1} ~ p_f(· | ŝ_t, a_t)  
Decoder: ô_{t+1} ~ p_g(· | ŝ_{t+1})
```

**(2) Joint Distribution**
```
p_PAN(o_{t+1} | o_t, a_t) = Σ_{ŝ_t, ŝ_{t+1}} p_h(ŝ_t | o_t) · p_f(ŝ_{t+1} | ŝ_t, a_t) · p_g(o_{t+1} | ŝ_{t+1})
```

**(3) Training Loss**
```
L_PAN = E[(o_t,a_t,o_{t+1})~D] [ disc(ô_{t+1}, o_{t+1}) ]
```

---

### Core Algorithms

```python
# Algorithm 1: GLP Encoder

def encode_observation(encoder, observation):
    """
    Map observation to latent representation.
    """
    latent = encoder(observation)  # Qwen2.5-VL-7B
    return latent  # ŝ_t ~ p_h(· | o_t)


# Algorithm 2: GLP Predictor (Autoregressive LLM)

def predict_next_latent(predictor, current_latent, action):
    """
    Predict next world state in latent space.
    """
    # Encode action
    action_emb = encode_action(action)  # Natural language
    
    # Autoregressive prediction
    next_latent = predictor(
        latent=current_latent,
        action=action_emb
    )
    
    return next_latent  # ŝ_{t+1} ~ p_f(· | ŝ_t, a_t)


# Algorithm 3: GLP Decoder

def decode_to_video(decoder, latent):
    """
    Reconstruct video from latent.
    """
    video = decoder(latent)  # Wan2.1-T2V-14B
    return video  # ô_{t+1} ~ p_g(· | ŝ_{t+1})


# Algorithm 4: Full PAN Generation

def pan_generate(encoder, predictor, decoder, history, actions):
    """
    Generate future video conditioned on history and actions.
    """
    # Encode current observation
    current_obs = history[-1]
    latent = encode_observation(encoder, current_obs)
    
    for action in actions:
        # Predict next latent
        next_latent = predict_next_latent(predictor, latent, action)
        
        # Decode to video
        video_frame = decode_to_video(decoder, next_latent)
        
        # Update latent for next step
        latent = next_latent
        
        yield video_frame


# Algorithm 5: Causal Swin-DPM (Long-Horizon)

def causal_swin_dpm(decoder, latents, chunk_size=16):
    """
    Chunk-wise causal attention for long sequences.
    
    Key: Reduces error accumulation across chunks.
    """
    num_chunks = len(latents) // chunk_size
    generated_chunks = []
    
    for i in range(num_chunks):
        chunk_latents = latents[i*chunk_size:(i+1)*chunk_size]
        
        if i > 0:
            # Add small noise to previous chunk output
            prev_chunk = generated_chunks[-1]
            noisy_prev = prev_chunk + small_noise()
            
            # Condition on slightly noised previous chunk
            conditioning = noisy_prev
        else:
            conditioning = None
        
        # Generate chunk with causal attention
        chunk_video = decoder.generate(
            latents=chunk_latents,
            conditioning=conditioning,
            causal_mask=True
        )
        
        generated_chunks.append(chunk_video)
    
    return concatenate(generated_chunks)


# Algorithm 6: Long-Horizon Rollout

def long_horizon_rollout(pan, initial_obs, num_steps, horizon=1000):
    """
    Generate long-horizon video with error correction.
    """
    history = [initial_obs]
    latents = [pan.encode(initial_obs)]
    
    for t in range(num_steps):
        # Get action (could be from policy or human)
        action = get_action(t)
        
        # Predict next latent
        next_latent = pan.predict(latents[-1], action)
        
        # Chunk-wise generation for long sequences
        if t % chunk_size == 0:
            video = causal_swin_dpm(pan.decoder, [next_latent])
        else:
            video = pan.decoder(next_latent)
        
        history.append(video)
        latents.append(next_latent)
        
        # Periodically correct drift
        if t % drift_correction_interval == 0:
            latents[-1] = correct_drift(latents[-1], history[-1])
    
    return history
```

### Architecture Components

| Component | Model | Purpose |
|-----------|-------|---------|
| Vision Encoder | Qwen2.5-VL-7B | Encode observations → latents |
| World Model | Autoregressive LLM | Predict latent dynamics |
| Video Decoder | Wan2.1-T2V-14B | Reconstruct video from latents |

### GLP Formula Summary

```
Encoder:    ŝ_t = h(o_t)           # Observation → latent
Predictor: ŝ_{t+1} = f(ŝ_t, a_t)  # Latent dynamics
Decoder:   ô_{t+1} = g(ŝ_{t+1})    # Latent → video
```

### Error Reduction Strategies

1. **Chunk-wise Generation** - Process in chunks not frames
2. **Causal Attention** - Mask future frames during generation
3. ** conditioning** - Use previous chunk with small noise
4. **Drift Correction** - Periodically realign with ground truth

### Bounded Types

```purescript
-- World Model Types
newtype HorizonLength = HorizonLength (BoundedInt 1 10000)
newtype LatentDim = LatentDim (BoundedInt 32 512)

data WorldState = WorldState
  { latent :: Tensor
  , history :: Array Tensor
  }

data WorldAction
  = NaturalLanguageAction Text
  | AgentAction Action
  | NoAction

data GLPElement = GLPElement
  { encoder :: VisionEncoder
  , predictor :: LatentPredictor
  , decoder :: VideoDecoder
  }

-- Simulation
data SimulationStep = SimulationStep
  { state :: WorldState
  , action :: WorldAction
  , observation :: Video
  }
```

### Grade Tracking

```purescript
data Effect
  = EncodeObservation
  = PredictLatent
  | DecodeVideo
  | ChunkGeneration
  | CorrectDrift

data CoEffect
  = NeedsHorizon HorizonLength
  | NeedsLatentDim LatentDim
  | NeedsActionSpace ActionSpace
  | NeedsLongTermConsistency
```

---

## QWEN25_OMNI (Thinker-Talker Multimodal Architecture)

### Classification
- **Domain**: Multimodal AI / Speech Generation / Vision-Language-Audio
- **Effect**: Understand(Multimodal), Generate(Text), Generate(Speech)
- **Coeffect**: ModalityCount, Latency, StreamQuality

### AST Schema
```json
{
  "algorithm": "Qwen25Omni",
  "inputs": ["text", "images", "audio", "video"],
  "outputs": ["text_response", "speech_stream"],
  "parameters": {
    "thinker": "Transformer LLM backbone",
    "talker": "Dual-track autoregressive",
    "vision_encoder": "ViT-675M",
    "audio_encoder": "Whisper-large-v3 init"
  }
}
```

### Key Formulas

**(1) Thinker-Talker Architecture**
```
Thinker: Transformer decoder → multimodal understanding → representations
Talker: Dual-track autoregressive → streaming speech tokens
```

**(2) TMRoPE (Time-aligned Multimodal RoPE)**
```
Text:   identical position IDs (1D)
Audio:  1 temporal ID = 40ms
Images: constant temporal ID, distinct height/width
Video:  temporal ID increments per frame
```

**(3) Block-wise Streaming**
```
Audio:  block attention of 2 seconds
Vision: merges 2×2 tokens, patch size 14
```

---

### Core Algorithms

```python
# Algorithm 1: Thinker (Multimodal Understanding)

def thinker_forward(thinker, text, images, audio, video):
    """
    Thinker: Transformer decoder for multimodal understanding.
    """
    # Encode each modality
    text_tokens = tokenize(text)
    image_tokens = vision_encoder(images)  # ViT
    audio_tokens = audio_encoder(audio)   # Whisper
    video_tokens = video_encoder(video)
    
    # Apply TMRoPE position embeddings
    text_pos = position_ids(text_tokens)
    image_pos = image_position_ids(images)  # constant temporal
    audio_pos = audio_position_ids(audio)   # 40ms per ID
    video_pos = video_position_ids(video)  # dynamic per frame
    
    # Concatenate with position embeddings
    multimodal_input = concat(
        embed(text_tokens, text_pos),
        embed(image_tokens, image_pos),
        embed(audio_tokens, audio_pos),
        embed(video_tokens, video_pos)
    )
    
    # Thinker processing
    representations = thinker(multimodal_input)
    
    # Extract text representation for Talker
    text_repr = representations[-len(text_tokens):]
    
    return representations, text_repr


# Algorithm 2: Talker (Streaming Speech Generation)

def talker_generate(talker, text_repr, max_tokens=1000):
    """
    Talker: Dual-track autoregressive for streaming speech.
    """
    speech_tokens = []
    
    for i in range(max_tokens):
        # Dual-track prediction
        logits = talker(speech_tokens, text_repr)
        
        # Sample next token
        next_token = sample(logits)
        
        if next_token == EOS:
            break
            
        speech_tokens.append(next_token)
        
        # Stream output
        if i % chunk_size == 0:
            yield decode_speech_chunk(speech_tokens)
    
    return speech_tokens


# Algorithm 3: TMRoPE Position Encoding

def tmrope_position_ids(inputs, modality):
    """
    Time-aligned Multimodal RoPE for each modality.
    """
    if modality == "text":
        # 1D position IDs
        return torch.arange(len(inputs))
    
    elif modality == "audio":
        # 1 temporal ID = 40ms
        duration_ms = len(inputs) * 40
        return torch.arange(0, duration_ms, 40)
    
    elif modality == "image":
        # Constant temporal, distinct height/width
        H, W = inputs.shape[1], inputs.shape[2]
        temporal = torch.zeros(H, W)
        h_pos = torch.arange(H).unsqueeze(1).expand(H, W)
        w_pos = torch.arange(W).unsqueeze(0).expand(H, W)
        return temporal, h_pos, w_pos
    
    elif modality == "video":
        # Temporal ID increments per frame
        T = len(inputs)
        return torch.arange(T).unsqueeze(-1).expand(T, -1)


# Algorithm 4: Block-wise Streaming

def block_wise_attention(encoder, input_modality, block_size=2.0):
    """
    Modified attention for streaming.
    
    Audio: 2-second blocks
    Vision: 2×2 token merging
    """
    if input_modality == "audio":
        # Process in 2-second blocks
        num_blocks = len(input) // (sample_rate * block_size)
        
        for i in range(num_blocks):
            block = input[i*block_size:(i+1)*block_size]
            
            # Block attention within chunk
            block_output = encoder(block)
            
            yield block_output
    
    elif input_modality == "vision":
        # Merge 2×2 tokens, patch size 14
        merged = merge_tokens(input, kernel=2)
        output = encoder(merged)
        yield output


# Algorithm 5: Sliding Window DiT for Speech

def sliding_window_dit(dit, mel_spectrogram, lookback=2, lookahead=1):
    """
    Flow-Matching DiT with restricted receptive field.
    """
    num_blocks = len(mel_spectrogram) // block_size
    
    generated = []
    
    for i in range(num_blocks):
        # Get context windows
        ctx_lookback = generated[-lookback:] if lookback > 0 else []
        ctx_lookahead = mel_spectrogram[i:i+lookahead]
        
        # Generate with restricted attention
        mel_chunk = dit.generate(
            context=ctx_lookback + ctx_lookahead,
            lookback=lookback,
            lookahead=lookahead
        )
        
        generated.append(mel_chunk)
    
    return generated


# Algorithm 6: End-to-End Streaming

def omni_stream(omni, input_modalities, max_speech_tokens=1000):
    """
    Full streaming pipeline: Thinker → Talker
    """
    # Thinker: understand multimodal input
    representations, text_repr = omni.thinker(input_modalities)
    
    # Stream speech while generating
    for chunk in omni.talker.stream_generate(text_repr, max_speech_tokens):
        # Decode mel to waveform
        waveform = omni.bigvgan.decode(chunk)
        
        # Yield streaming audio
        yield waveform


# Algorithm 7: Video-Audio Time Interleaving

def interleave_video_audio(video_frames, audio_samples):
    """
    Time-interleaving for video with audio.
    2-second chunks, visual first, then audio.
    """
    chunk_duration = 2.0  # seconds
    
    interleaved = []
    
    num_chunks = min(len(video_frames), len(audio_samples)) // chunk_duration
    
    for i in range(num_chunks):
        # Visual first
        v_start = int(i * chunk_duration * video_fps)
        v_end = int((i+1) * chunk_duration * video_fps)
        interleaved.append(('video', video_frames[v_start:v_end]))
        
        # Then audio
        a_start = int(i * chunk_duration * audio_sr)
        a_end = int((i+1) * chunk_duration * audio_sr)
        interleaved.append(('audio', audio_samples[a_start:a_end]))
    
    return interleaved
```

### Architecture Components

| Component | Model | Purpose |
|-----------|-------|---------|
| Thinker | Transformer LLM | Multimodal understanding |
| Talker | Dual-track AR | Streaming speech |
| Vision Encoder | ViT-675M | Image/video → tokens |
| Audio Encoder | Whisper-large-v3 | Audio → tokens |
| DiT | Flow-Matching | Mel-spectrogram generation |
| BigVGAN | Modified | Waveform decoding |

### Training Stages

| Stage | Focus | Data |
|-------|-------|------|
| 1 | Encoders only | Image-text, audio-text |
| 2 | Full multimodal | 800B img + 300B audio + 100B video |
| 3 | Long sequences | 32k tokens |

### Bounded Types

```purescript
-- Modality Types
data Modality
  = Text
  | Image
  | Audio
  | Video

newtype ModalityCount = ModalityCount (BoundedInt 1 4)

-- Position Embeddings  
data PositionEncoding
  = TextPosition (Array Int)
  | AudioPosition { temporal :: Int, ms_per_id :: Int }
  | ImagePosition { temporal :: Int, height :: Int, width :: Int }
  | VideoPosition { frame :: Int, height :: Int, width :: Int }

-- Thinker-Talker
data ThinkerState = ThinkerState
  { representations :: Tensor
  , text_repr :: Tensor
  }

data TalkerState = TalkerState
  { speech_tokens :: Array Int
  , mel_chunks :: Array MelSpectrogram
  }

-- Streaming
data StreamChunk = StreamChunk
  { audio :: Waveform
  , text :: Text
  , timestamp :: Int
  }
```

### Grade Tracking

```purescript
data Effect
  = UnderstandMultimodal
  = GenerateText
  | GenerateSpeech
  | StreamAudio

data CoEffect
  = NeedsModalityCount ModalityCount
  | NeedsLatency Latency
  | NeedsStreamQuality Quality
  | NeedsBlockSize Number
```

---

### Grade Tracking

```purescript
data Effect
  = ExtractTextures
  | GeneratePBR
  | SegmentMaterials
  | InfusePatterns

data CoEffect
  = NeedsMaterialDomain MaterialDomain
  | NeedsStateType MaterialState
  | NeedsDatasetSize Int
  | NeedsSyntheticData
```

---

### Grade Tracking

```purescript
data Effect
  = GenerateWorld
  | PlanScene
  | ReconstructMesh
  | DecomposeParts
  | EnhanceTextures

data CoEffect
  = NeedsWorldSize WorldSize
  | NeedsObjectCount ObjectCount
  | NeedsGPUCompute
  | NeedsLLM
```

---

### Grade Tracking

```purescript
data Effect
  = QuantizeForward
  | QuantizeBackward
  | MXFP4GEMM
  | HadamardTransform

data CoEffect
  = NeedsModelSize Int
  | NeedsDataSize Int
  | NeedsPrecision Precision
  | NeedsGroupSize GroupSize
  | NeedsBlackwellGPU
```

---

### Grade Tracking

```purescript
data Effect
  = GenerateVideo
  | ControlMotion
  | PreserveAppearance
  | WarpImage

data CoEffect
  = NeedsNumFrames NumFrames
  | NeedsResolution VideoResolution
  | NeedsBackbone I2VBackbone
  | NeedsDepthEstimator
```

---

### Grade Tracking

```purescript
data Effect
  = SimulateCloth
  | DetectCollisions
  | EnforceConstraints
  | Remesh

data CoEffect
  = NeedsVertexCount VertexCount
  | NeedsTriangleCount TriangleCount
  | NeedsTimeStep Number
  | NeedsGPUCompute
```

---

### Grade Tracking

```purescript
-- Effects: What the algorithm produces
data Effect = ComputeNVFP4 | MemoryAllocate | ScaleComputation

-- Coeffects: What the algorithm requires  
data CoEffect = RequiresBlockSize Int 
              | RequiresScaleFactor Precision 
              | RequiresFP8Conversion
```

---


- [x] FOUR_OVER_SIX (NVFP4)
- [ ] PRETRAINING_NVFP4
- [ ] OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY
- [ ] GAIA2_WORLD_MODEL
- [ ] PAN_WORLD_MODEL

---

## PRETRAINING_NVFP4 (Full Training Pipeline)

### Classification
- **Domain**: LLM Pre-training / 4-bit Training
- **Effect**: Compute(NVFP4), Compute(RHT), Compute(StochasticRound)
- **Coeffect**: Layers(BF16), Tokens(10T), Model(12B)

### AST Schema
```json
{
  "algorithm": "NVFP4Pretraining",
  "inputs": [{"name": "X", "type": "Tensor"}, {"name": "optimizer_state", "type": "Optimizer"}],
  "outputs": [{"name": "model", "type": "NVFP4Model"}],
  "parameters": {
    "mixed_precision_layers": "first_2 + last_8 blocks",
    "hadamard_size": 16,
    "rounding": "stochastic (gradients), nearest (weights/activations)"
  }
}
```

### Key Formulas

**(A) Global Tensor Scaling**
```
s_enc = 6 × 448 / amax(x)
```
Where `amax(x) = max_i(|x_i|)` - absolute maximum across tensor

**(B) Local Block Decoding Scale**
```
S_decode,b = amax(b) / 6
```

**(C) Local Encode Scale (FP8)**
```
s_encode,b,e4m3 = e4m3(S_decode,b × s_enc)
```

**(D) Hadamard Transform**
```
x' = q(xH · s)
```
Where:
- `H` = Hadamard matrix (16×16)
- `s` = scale factor in rotated space
- `q()` = quantization function

### Pseudocode

```python
# Algorithm 2: NVFP4 Pre-training Pipeline

class NVFP4Linear(Module):
  def __init__(self, in_features, out_features):
    self.weight = Parameter(out_features, in_features)  # FP32
    self.bias = None
  
  def forward(self, x):
    # FPROP
    x_fp32 = x.to(FP32)
    x_quantized = quantize_nvfp4(x_fp32)  # 2D block
    
    w_quantized = quantize_nvfp4(self.weight)  # 2D block
    
    y = gemm(x_quantized, w_quantized)
    return y.to(BF16)
  
  def backward(self, grad_output):
    # DGRAD
    grad_x = gemm(grad_output, w_quantized.T)
    
    # WGRAD with RHT
    grad_w = gemm(x_quantized.T, grad_output)
    grad_w = hadamard_transform(grad_w, size=16)
    grad_w_quantized = quantize_nvfp4(grad_w, stochastic=True)
    
    return grad_x, grad_w_quantized

def quantize_nvfp4(tensor, stochastic=False):
  # 2D block quantization: 16×16 blocks
  blocks = tensor.reshape(-1, 16, 16)
  
  for block in blocks:
    # Compute block scale
    amax = block.abs().max()
    scale = (amax / 6.0).to(FP8_E4M3)
    
    # Normalize
    normalized = block / scale.to(FP32)
    
    # Quantize to FP4 E2M1
    if stochastic:
      quantized = stochastic_round(normalized, min_val=-6, max_val=6)
    else:
      quantized = round_to_nearest(normalized, min_val=-6, max_val=6)
    
    # Store (quantized, scale)
  return quantized_tensor

def hadamard_transform(tensor, size=16):
  # Random Hadamard transform for outlier mitigation
  H = hadamard_matrix(size)  # 16×16
  
  # Random sign vector
  signs = random_sign_vector(size)
  D = diagonal_matrix(signs)
  
  transformed = tensor @ (H @ D)
  return transformed
```

### Training Configuration

| Component | Precision | Notes |
|-----------|-----------|-------|
| Embeddings | BF16 | - |
| Attention (QKV) | BF16 | - |
| FFN layers | NVFP4 | Except first 2 + last 8 |
| Mamba blocks | NVFP4 | Except first 2 + last 8 |
| Optimizer state | FP32 | - |
| Gradients (accumulation) | BF16 | - |
| Gradients (WGRAD) | NVFP4 + SR | Stochastic rounding |
| Activations | BF16 | - |

### Mixed Precision Strategy

```python
# Layer classification for 12B model (62 blocks total)
sensitive_layers = (
  [Block(i) for i in range(2)] +           # First 2 blocks
  [Block(i) for i in range(54, 62)]         # Last 8 blocks
)
# Total: 16% in BF16, 84% in NVFP4
```

### Hadamard Transform Details

| Parameter | Value | Rationale |
|----------|-------|-----------|
| Matrix size | 16×16 | Balance cost/accuracy |
| Applied to | WGRAD inputs | Weight gradient GEMM |
| Random signs | Yes | Reduce structured outliers |
| Shared seed | Yes | One seed across training |

### Stochastic Rounding

```python
def stochastic_round(tensor, min_val, max_val):
  # Probabilistic rounding for unbiased gradient estimation
  floor = floor(tensor)
  frac = tensor - floor
  
  prob = torch.bernoulli(frac)
  result = floor + prob
  
  # Clamp to valid range
  return clamp(result, min_val, max_val)
```

### Bounded Types

```purescript
data LayerType = Embedding | Attention | FFN | MambaBlock
data Precision = FP32 | BF16 | NVFP4 | FP8

data TrainingPhase = Warmup | Stable | Decay

newtype BlockIndex = BlockIndex (BoundedInt 0 127)
newtype LayerIndex = LayerIndex (BoundedInt 0 63)

-- Layer sensitivity classification  
classifyLayer :: LayerIndex -> LayerType -> Precision
classifyLayer idx Embedding = BF16
classifyLayer idx Attention 
  | idx < 2 || idx >= 54 = BF16
  | otherwise = NVFP4
classifyLayer idx FFN
  | idx < 2 || idx >= 54 = BF16  
  | otherwise = NVFP4
classifyLayer idx MambaBlock
  | idx < 2 || idx >= 54 = BF16
  | otherwise = NVFP4
```

### Grade Tracking

```purescript
-- Training effects
data Effect 
  = ForwardNVFP4
  | BackwardNVFP4
  | HadamardTransform
  | StochasticRound
  | GradientAccumulate
  | OptimizerUpdate

-- Training coeffects  
data CoEffect
  = RequiresLayerPrecision Precision
  | RequiresBlockSize Int
  | RequiresHadamardSize Int
  | RequiresTokenCount Int
  | RequiresModelSize Int
```

---


- [x] FOUR_OVER_SIX (NVFP4)
- [x] PRETRAINING_NVFP4
- [ ] OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY
- [ ] GAIA2_WORLD_MODEL
- [ ] PAN_WORLD_MODEL

---

## OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY

### Classification
- **Domain**: AI Safety / Interpretability / Circuit Analysis
- **Effect**: Analyze(Model), Extract(Features), Validate(Hypotheses)
- **Coeffect**: ModelSize, Architecture, Dataset

### Two Main Approaches

#### 1. Reverse Engineering Pipeline

```python
# Algorithm 3: Circuit Discovery Pipeline

def circuit_discovery(model, task, dataset):
  # Step 1: Task Definition
  task_def = define_task(task)  # Input-output pairs
  
  # Step 2: Network Decomposition
  # Options: neurons, attention_heads, sae_latents, mlp_outputs
  decomposition = decompose(model, method='sparse_autoencoder')
  
  # Step 3: Component Identification
  # Find components relevant to task
  relevant_components = []
  for component in decomposition:
    if ablation_affects_task(component, task_def):
      relevant_components.append(component)
  
  # Step 4: Circuit Assembly
  circuit = assemble_circuit(relevant_components)
  
  # Step 5: Validation
  validate(circuit, task_def, dataset)
  
  return circuit
```

#### 2. Concept-Based Interpretability

```python
# Algorithm 4: Probe-Based Concept Discovery

def find_concepts(model, layer, concept_labels):
  # concept_labels: dict mapping inputs to boolean concept presence
  
  activations = capture_activations(model, layer, dataset)
  
  # Train linear probe
  probe = LinearProbe()
  probe.fit(activations, concept_labels)
  
  # Extract concept vector
  concept_vector = probe.weight
  
  return concept_vector
```

### Key Algorithms

#### A. Sparse Dictionary Learning (SDL) / SAE

```python
# Algorithm 5: Sparse Autoencoder

class SparseAutoencoder(Module):
  def __init__(self, d_model, d_latent):
    self.encoder = Linear(d_model, d_latent)
    self.decoder = Linear(d_latent, d_model)
    self.activation = ReLU()
  
  def forward(self, x):
    z = self.encoder(x)
    z = self.activation(z)
    # Apply L1 sparsity
    loss = self.l1_loss(z)
    x_recon = self.decoder(z)
    return x_recon, z
  
  def compute_loss(self, x, x_recon, z):
    recon_loss = mse(x, x_recon)
    sparsity_loss = abs(z).sum()
    total = recon_loss + lambda * sparsity_loss
    return total

# Superposition hypothesis parameters
SUPERPOSITION_PARAMS = {
  'max_features': 10 * d_model,  # Overcomplete basis
  'sparsity_target': 0.01,       # 1% active
  'dictionary_size': d_latent
}
```

#### B. Attribution Methods

```python
# Algorithm 6: Integrated Gradients

def integrated_gradients(model, input, baseline, steps=200):
  # Interpolate between baseline and input
  alphas = linspace(0, 1, steps)
  
  gradients = []
  for alpha in alphas:
    interpolated = baseline + alpha * (input - baseline)
    interpolated.requires_grad = True
    
    output = model(interpolated)
    grad = torch.autograd.grad(output, interpolated)
    gradients.append(grad)
  
  # Average gradients
  avg_grad = mean(gradients, dim=0)
  
  # Compute integrated gradients
  ig = (input - baseline) * avg_grad
  
  return ig

# Algorithm 7: Activation Patching

def activation_patching(model, corrupted, clean, patch_locations):
  # Measure effect of patching activations
  results = {}
  
  for location in patch_locations:
    # Patch location with corrupted value
    patched = clean.clone()
    patched[location] = corrupted[location]
    
    output_patched = model(patched)
    output_clean = model(clean)
    
    effect = abs(output_patched - output_clean)
    results[location] = effect
  
  return results
```

#### C. Circuit Validation

```python
# Algorithm 8: Faithfulness Measurement

def measure_faithfulness(circuit, model, task_data):
  """Measure how well circuit explains task behavior"""
  
  # Original performance
  original_perf = evaluate(model, task_data)
  
  # Ablate circuit components
  ablated_model = model.copy()
  for node in circuit.nodes:
    ablate(ablated_model, node)
  
  ablated_perf = evaluate(ablated_model, task_data)
  
  # Faithfulness = performance drop
  faithfulness = original_perf - ablated_perf
  
  return faithfulness

# Algorithm 9: Completeness Measurement

def measure_completeness(circuit, model, task_data):
  """Measure if circuit captures all relevant behavior"""
  
  # Collect all model components
  all_components = get_all_components(model)
  circuit_components = set(circuit.nodes)
  
  # Find components NOT in circuit but affect task
  outside_circuit = []
  for comp in all_components - circuit_components:
    effect = measure_component_effect(comp, task_data)
    if effect > THRESHOLD:
      outside_circuit.append(comp)
  
  completeness = 1 - (len(outside_circuit) / len(all_components))
  
  return completeness
```

### Method Comparison Matrix

| Method | Faithfulness | Completeness | Scalability | Interpretability |
|--------|-------------|--------------|-------------|-----------------|
| Ablation | High | Low | Medium | Low |
| Attribution | Medium | Low | High | Medium |
| SAEs | Medium | Medium | High | Medium |
| Probes | Low | Medium | High | Medium |
| Circuit Discovery | High | High | Low | High |

### SDL Parameters

```python
SPARSE_AUTOENCODER_PARAMS = {
  # Architecture
  'dictionary_size': 16_000_000,  # 16M latents (GPT-4)
  'activation': 'relu',  # or 'celu', 'gelu'
  
  # Loss weights
  'l1_coefficient': 0.01,
  'auxiliary_loss_coefficient': 0.001,
  
  # Training
  'batch_size': 8192,
  'learning_rate': 1e-4,
  'steps': 100_000,
  
  # dead neurons handling
  'neuron_resample_rate': 0.01,
  'dead_neuron_threshold': 1e-6
}
```

### Bounded Types

```purescript
-- Interpretability method types
data InterpretMethod 
  = Ablation
  | Attribution IntegratedGradients
  | SAETrain SAEConfig
  | ProbeTrain ProbeConfig
  | CircuitDiscovery CircuitConfig

data CircuitComponent
  = Neuron { layer :: Int, index :: Int }
  | AttentionHead { layer :: Int, head :: Int }
  | SAELatent { sae_id :: String, index :: Int }
  | MLPOutput { layer :: Int }

data FaithfulnessMetric
  = AblationScore Number
  | AttributionScore Number
  | ComposedScore { faith :: Number, comp :: Number }

-- Model organism definitions  
data ModelOrganism
  = ModularAddition
  | GPT2Small
  | ResNet50
  | Custom String
```

### Grade Tracking

```purescript
-- Interpretability effects
data Effect
  = AnalyzeModel
  | ExtractFeatures
  | ComputeAttribution
  | TrainProbe
  | TrainSAE
  | ValidateCircuit

-- Interpretability coeffects
data CoEffect
  = RequiresModelSize Int
  | RequiresArchitecture Architecture
  | RequiresDataset Dataset
  | RequiresComputeBudget Int
  | RequiresLayerSpecific LayerIndex
```

---


- [x] FOUR_OVER_SIX (NVFP4)
- [x] PRETRAINING_NVFP4
- [x] OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY
- [ ] GAIA2_WORLD_MODEL
- [ ] PAN_WORLD_MODEL

---

## GAIA2_WORLD_MODEL (Controllable Multi-View Video Generation)

### Classification
- **Domain**: Autonomous Driving / World Model / Video Generation
- **Effect**: GenerateVideo, PredictFuture, InpaintScene
- **Coeffect**: CameraCount(5), Resolution(448×960), Horizon(frames)

### AST Schema
```json
{
  "algorithm": "GAIA2",
  "components": ["VideoTokenizer", "WorldModel"],
  "inputs": ["video_frames", "actions", "agent_boxes", "metadata"],
  "outputs": ["future_latents", "reconstructed_video"]
}
```

### Architecture Overview

```
Input Video → Video Tokenizer → Latents → World Model → Future Latents → Video Decoder → Output Video
                    ↓                                        ↓
              (Encoder)                              (Decoder)
              85M params                            200M params
              
World Model: 8.4B params (space-time transformer)
```

### Key Formulas

**(A) Video Tokenizer Compression**
```
Compression Ratio = (T_v × H_v × W_v × 3) / (T_L × H × W × L)
                  = 384×  (with T_v=24, H_v=448, W_v=960, T_L=3, H=14, W=30, L=64)
```

**(B) Flow Matching Time Sampling**
```
# Bimodal logit-normal distribution
p(τ) = 0.8 × N(μ=0.5, σ=1.4) + 0.2 × N(μ=-3.0, σ=1.0)
```

**(C) Action Normalization (symlog)**
```
symlog(y) = sign(y) × log(1 + s×|y|) / log(1 + s×|y_max|)

# For curvature: s=1000 (range: 0.0001 to 0.1)
# For speed: s=3.6 (range: 0 to 75 m/s → km/h)
```

### Video Tokenizer

```python
# Algorithm 10: GAIA-2 Video Tokenizer

class GAIATokenizer(Module):
  def __init__(self):
    self.encoder = Encoder85M()      # 85M parameters
    self.decoder = Decoder200M()    # 200M parameters
  
  def encode(self, video):
    # video: (B, T, C, H, W)
    # T = 24 frames
    # H, W = 448, 960
    
    latents = self.encoder(video)
    # Output: (B, T_L, C, H, W)
    # T_L = 3, C = 64, H = 14, W = 30
    return latents
  
  def decode(self, latents):
    video = self.decoder(latents)
    return video
  
  def reconstruct(self, video):
    latents = self.encode(video)
    reconstructed = self.decode(latents)
    return reconstructed, latents

# Encoder Architecture
class Encoder85M(Module):
  # Downsampling: 2×8×8 (time, height, width)
  # 24 spatial transformer blocks (512 dim, 16 heads)
  # Final: conv 1×2×2 → project to 2L (mean + std)
  
# Decoder Architecture  
class Decoder200M(Module):
  # Project L → embedding
  # 16 space-time transformer blocks
  # Upsample: 2×2×2
  # 8 more space-time blocks
  # Upsample: 2×8×8 → RGB
```

### World Model

```python
# Algorithm 11: GAIA-2 World Model

class GAI AWorldModel(Module):
  def __init__(self):
    self.transformer = SpaceTimeTransformer(
      hidden_dim=4096,
      heads=32,
      blocks=22
    )
    self.action_embed = Linear(2, 4096)  # speed, curvature
    self.condition_embed = CrossAttention(4096, 512)
  
  def forward(self, latents, actions, conditions):
    # latents: (B, T, N, H, W, L)  N=cameras
    # actions: (B, T)  [speed, curvature]
    # conditions: dict with agent boxes, metadata, embeddings
    
    # Embed actions
    action_emb = self.action_embed(actions)  # (B, T, 4096)
    
    # Flow matching time
    tau = sample_flow_matching_time()  # bimodal logit-normal
    
    # Process through transformer
    for block in self.transformer.blocks:
      # Spatial attention (over space and cameras)
      latents = block.spatial_attn(latents)
      
      # Temporal attention
      latents = block.temporal_attn(latents)
      
      # Cross-attention for conditions
      latents = block.cross_attn(latents, conditions)
      
      # Adaptive layer norm for action and time
      latents = block.adaptive_norm(latents, action_emb, tau)
    
    return latents
```

### Conditioning System

```python
# Algorithm 12: Multi-Modal Conditioning

class ConditioningSystem:
  def __init__(self):
    self.ego_embed = Linear(2, 512)       # speed, curvature
    self.agent_embed = AgentEncoder()     # 3D bounding boxes
    self.camera_embed = CameraEncoder()   # intrinsics, extrinsics
    self.env_embed = EnvEncoder()          # weather, time, location
    self.clip_embed = CLIPEncoder()        # text embeddings
  
  def encode(self, observations):
    ego = self.ego_embed(observations.actions)      # (B, T, 2)
    
    agents = []
    for agent_box in observations.agent_boxes:
      # 3D location, orientation, dimensions, category
      agent_feat = self.agent_embed(agent_box)
      agents.append(agent_feat)
    agents = stack(agents)  # (B, T, N_agents, 512)
    
    camera = self.camera_embed(observations.camera_params)
    
    env = {
      'weather': self.env_embed(observations.weather),
      'time': self.env_embed(observations.time_of_day),
      'location': self.env_embed(observations.region),
      'road': self.env_embed(observations.road_layout)
    }
    
    clip = self.clip_embed(observations.text_prompt)
    
    return {
      'ego': ego,
      'agents': agents,
      'camera': camera,
      'environment': env,
      'clip': clip
    }
```

### Inference Modes

```python
# Algorithm 13: Generation from Scratch

def generate_from_scratch(actions, conditions, model, tokenizer):
  # Sample pure noise
  noise = torch.randn(B, T_L, N_cameras, H, W, L)
  
  # Denoise with conditioning
  for step in range(50):  # 50 denoising steps
    predicted = model(noise, actions, conditions)
    noise = noise - step_size * predicted
  
  # Decode to video
  video = tokenizer.decode(noise)
  
  return video

# Algorithm 14: Autoregressive Prediction

def autoregressive_predict(context_latents, model, tokenizer, horizon):
  # context_latents: (B, 3, N, H, W, L) - initial context
  
  current = context_latents
  predictions = []
  
  for t in range(horizon):
    # Predict next latents
    next_latents = model(current, actions[t])
    
    # Append to context (sliding window)
    current = concat([current[:, 1:], next_latents])
    
    # Decode this chunk
    video_chunk = tokenizer.decode(next_latents)
    predictions.append(video_chunk)
  
  return concatenate(predictions)

# Algorithm 15: Inpainting

def inpaint(video, mask, agent_boxes, model, tokenizer):
  # Encode original video
  latents = tokenizer.encode(video)
  
  # Apply mask
  masked_latents = latents * mask
  
  # Denoise masked regions with agent conditioning
  for step in range(50):
    predicted = model(masked_latents, conditions=agent_boxes)
    masked_latents = update_with_prediction(masked_latents, predicted, mask)
  
  # Decode
  result = tokenizer.decode(masked_latents)
  
  return result
```

### Flow Matching Details

```python
# Algorithm 16: Flow Matching Training

def flow_matching_loss(model, x_0, x_1):
  # x_0: noise sample
  # x_1: target latents
  
  # Sample time from bimodal distribution
  tau = sample_bimodal_logit_normal()
  
  # Interpolate
  x_tau = tau * x_1 + (1 - tau) * x_0
  
  # Predict velocity
  v_pred = model(x_tau, tau)
  
  # Ground truth velocity
  v_gt = x_1 - x_0
  
  # Loss
  loss = mse(v_pred, v_gt)
  
  return loss

def sample_bimodal_logit_normal():
  if random() < 0.8:
    # Primary mode: μ=0.5, σ=1.4
    tau = sample_normal(0.5, 1.4)
    tau = clamp(tau, 0.01, 0.99)
  else:
    # Secondary mode: μ=-3.0, σ=1.0
    tau = sample_normal(-3.0, 1.0)
    tau = clamp(tau, 0.001, 0.1)
  
  return tau
```

### Bounded Types

```purescript
-- GAIA-2 type definitions
newtype CameraIndex = CameraIndex (BoundedInt 0 4)  -- 5 cameras max
newtype FrameIndex = FrameIndex (BoundedInt 0 23)  -- 24 input frames
newtype LatentFrame = LatentFrame (BoundedInt 0 2)  -- 3 latent frames

data Action = Action
  { speed :: BoundedInt 0 75          -- m/s (0-75)
  , curvature :: BoundedInt 0 1000   -- m^-1 (0.0001-0.1, scaled)
  }

data AgentBox = AgentBox
  { position :: Vec3
  , orientation :: Vec3
  , dimensions :: Vec3
  , category :: AgentCategory
  }

data AgentCategory = Vehicle | Pedestrian | Cyclist | Other

data Environment = Environment
  { region :: Region
  , timeOfDay :: TimeOfDay
  , weather :: Weather
  , roadLayout :: RoadLayout
  }

data Region = UK | US | Germany

data TimeOfDay = Dawn | Morning | Noon | Afternoon | Dusk | Night

data Weather = Clear | Rain | Snow | Fog | Cloudy
```

### Grade Tracking

```purescript
-- GAIA-2 effects
data Effect
  = EncodeVideo
  | DecodeVideo
  | GenerateFuture
  | InpaintRegion
  | EditScene

-- GAIA-2 coeffects
data CoEffect
  = RequiresCameras Int
  | RequiresResolution Width Height
  | RequiresHorizon Int
  | RequiresConditioning ConditioningType
```

---


- [x] FOUR_OVER_SIX (NVFP4)
- [x] PRETRAINING_NVFP4
- [x] OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY
- [x] GAIA2_WORLD_MODEL
- [ ] PAN_WORLD_MODEL

---

## PAN_WORLD_MODEL (Generative Latent Prediction)

### Classification
- **Domain**: General World Model / Interactive Simulation / Long-Horizon Planning
- **Effect**: PredictWorld, SimulateAction, Reason
- **Coeffect**: HistoryLength, ActionSpace, WorldDiversity

### AST Schema
```json
{
  "algorithm": "PAN",
  "components": ["VisionEncoder", "LLMBackbone", "VideoDecoder"],
  "inputs": ["observations", "actions"],
  "outputs": ["predicted_observations", "latent_states"]
}
```

### GLP Architecture

```
Observation → Vision Encoder → Latent States → LLM Backbone → Next Latents → Video Decoder → Future Video
     (Qwen2.5-VL-7B)              (autoregressive)              (Wan2.1-T2V-14B)
```

### Key Formulas

**(A) Generative Latent Prediction (GLP)**
```
p_PAN(o_{t+1} | o_t, a_t) = Σ ŝ_t,ŝ_{t+1} p_h(ŝ_t | o_t) × p_f(ŝ_{t+1} | ŝ_t, a_t) × p_g(o_{t+1} | ŝ_{t+1})

where:
  h = encoder
  f = world model (LLM backbone)  
  g = decoder (video diffusion)
```

**(B) Flow Matching for Decoder**
```
x_k = k × x_1 + (1 - k) × x_0    # Linear interpolation
v_k = x_1 - x_0                   # Velocity
```

**(C) Causal Swin-DPM Denoising**
```
# Sliding window with causal attention
window_size = 2 chunks  # 2 × (T/2) frames
chunk_1_noise_level = k
chunk_2_noise_level = k + 0.5
```

### Vision Encoder (Qwen2.5-VL-7B)

```python
# Algorithm 17: PAN Vision Encoder

class PANVisionEncoder(Module):
  def __init__(self):
    self.vit = Qwen2_5VL_Vit(
      patch_size=14,
      hidden_dim=4096,
      num_heads=32
    )
    self.state_projection = Linear(4096, 256)  # 256 tokens per state
  
  def encode(self, observation):
    # observation: images or video frames
    
    # Encode with ViT
    tokens = self.vit(observation)  # (B, T, H*W, hidden)
    
    # Project to compact state
    state = self.state_projection(tokens)  # (B, T, 256)
    
    return state  # World state representation
```

### LLM Backbone (Autoregressive World Model)

```python
# Algorithm 18: PAN LLM Backbone

class PANBackbone(Module):
  def __init__(self):
    self.llm = Qwen2_5VL_7B_Instruct()
    self.query_embed = Linear(256, 4096)
  
  def forward(self, states, actions, next_action):
    # states: (B, T, 256) - history of world states
    # actions: (B, T-1) - actions taken
    # next_action: (B,) - action to predict outcome for
    
    # Build conversation format
    conversation = build_prompt(states, actions, next_action)
    
    # Autoregressive generation
    output = self.llm.generate(conversation)
    
    # Extract next state prediction
    next_state = output.response  # (B, 256)
    
    return next_state
  
  def simulate(self, initial_state, action_sequence):
    # Long-horizon simulation
    current = initial_state
    
    predictions = []
    for action in action_sequence:
      next_state = self.forward(current, [action])
      predictions.append(next_state)
      current = next_state
    
    return predictions
```

### Video Diffusion Decoder (Wan2.1-T2V-14B)

```python
# Algorithm 19: PAN Video Decoder with Causal Swin-DPM

class PANDecoder(Module):
  def __init__(self):
    self.dit = DiT_14B(
      hidden_dim=4096,
      num_heads=32,
      num_blocks=40
    )
    self.causal_attn = CausalWindowAttention(window_size=2)
  
  def decode(self, state, action, num_frames=81):
    # state: (B, 256) - latent world state
    # action: text description
    # num_frames: 81 (corresponds to 21 latent frames × 4)
    
    # Initialize noise
    noise = torch.randn(B, 21, C, H, W)  # 21 latent frames
    
    # Causal denoising with sliding window
    for k in range(1000):  # 1000 denoising steps
      # Split into two chunks
      chunk_1 = noise[:, :10]   # earlier frames
      chunk_2 = noise[:, 10:]   # later frames
      
      # Different noise levels (Causal Swin-DPM)
      k_1 = k / 1000
      k_2 = min(1.0, k_1 + 0.5)
      
      # Predict with causal attention
      chunk_1_denoised = self.dit(chunk_1, state, action, noise_level=k_1)
      chunk_2_denoised = self.dit(chunk_2, state, action, noise_level=k_2,
                                    past_chunk=chunk_1_denoised)
      
      # Update
      noise = concat([chunk_1_denoised, chunk_2_denoised])
    
    # Decode latents to video
    video = self.vae.decode(noise)
    
    return video
  
  def generate_with_action(self, initial_frame, action_sequence):
    # Encode initial frame
    initial_latent = self.vae.encode(initial_frame)
    
    # Simulate through action sequence
    latents = self.backbone.simulate(initial_latent, action_sequence)
    
    # Decode each prediction
    videos = [self.vae.decode(latent) for latent in latents]
    
    return videos
```

### Flow Matching Loss

```python
# Algorithm 20: PAN Flow Matching Training

def flow_matching_loss(decoder, x_1, tau):
  # x_1: target video latents
  # tau: flow matching time (0-1)
  
  # Sample noise
  x_0 = torch.randn_like(x_1)
  
  # Interpolate
  x_tau = tau * x_1 + (1 - tau) * x_0
  
  # Predict velocity
  v_pred = decoder(x_tau, tau)
  
  # Ground truth
  v_gt = x_1 - x_0
  
  # Loss
  loss = mse(v_pred, v_gt)
  
  return loss

# Training with shifted denoising schedule
def sample_tau():
  # Shifted schedule for better low-noise training
  k = uniform(0, 1)
  tau = (k + 0.5) % 1.0  # Shift to emphasize low-noise region
  return tau
```

### Causal Swin-DPM Details

```python
# Algorithm 21: Causal Swin-DPM Attention

class CausalWindowAttention(Module):
  def __init__(self, window_size=2):
    self.window_size = window_size
  
  def forward(self, current_chunk, past_chunk, attention_mask):
    # current_chunk: (B, T_curr, C, H, W)
    # past_chunk: (B, T_past, C, H, W)  # Previous chunk
    
    # Causal mask: current can see past, but not vice versa
    # Creates upper triangular attention matrix
    
    # Compute attention with causal masking
    q = self.linear_q(current_chunk)
    kv_past = self.linear_kv(past_chunk)
    
    # Attention scores
    scores = torch.matmul(q, kv_past.transpose(-2, -1))
    
    # Apply causal mask (upper triangle = -inf)
    scores = scores + causal_mask
    
    # Softmax
    attention = F.softmax(scores, dim=-1)
    
    # Apply
    output = torch.matmul(attention, kv_past)
    
    return output
```

### Inference Modes

```python
# Algorithm 22: PAN Multi-Mode Inference

class PANInference:
  def __init__(self, model):
    self.model = model
  
  def generate_from_scratch(self, action, num_frames=81):
    # Pure generation with action conditioning
    noise = self.initialize_noise(num_frames)
    video = self.denoise(noise, action=action)
    return video
  
  def autoregressive_predict(self, context_frames, action_sequence):
    # Context rollout
    current = self.encode(context_frames)
    
    predictions = []
    for action in action_sequence:
      next_state = self.model.llm.predict(current, action)
      next_video = self.decode(next_state)
      predictions.append(next_video)
      current = next_state
    
    return predictions
  
  def inpaint(self, video, mask, new_action):
    # Selective editing
    latents = self.encode(video)
    latents = apply_mask(latents, mask)
    
    # Regenerate masked regions
    edited = self.denoise(latents, action=new_action, mask=mask)
    
    return edited
  
  def edit_scene(self, video, edit_prompt):
    # Partial noising and denoising with new conditions
    latents = self.encode(video)
    
    # Partially noise
    noisy_latents = add_noise(latents, level=0.3)
    
    # Denoise with edit prompt
    edited = self.denoise(noisy_latents, condition=edit_prompt)
    
    return edited
```

### Data Pipeline

```python
# Algorithm 23: PAN Training Data Construction

def prepare_training_data(video_clips):
  # Step 1: Collect diverse videos
  videos = collect_videos(domains=[
    'human_activities',
    'object_interactions', 
    'navigation',
    'manipulation',
    'sports'
  ])
  
  # Step 2: Quality filtering
  videos = filter_static(videos)          # Remove static
  videos = filter_blur(videos)           # Remove blurry
  videos = filter_aesthetic(videos, min_score=6.0)
  
  # Step 3: Dense captioning
  captions = []
  for video in videos:
    caption = dense_caption(video)  # VLM generates detailed caption
    caption.focus_on('motion', 'events', 'changes')
    captions.append(caption)
  
  # Step 4: Action extraction
  action_sequences = []
  for video, caption in zip(videos, captions):
    # Extract natural language actions from caption
    actions = extract_actions(caption)
    # Align with video frames
    aligned = align_actions_to_frames(actions, video)
    action_sequences.append(aligned)
  
  return videos, action_sequences, captions
```

### Bounded Types

```purescript
-- PAN type definitions
newtype StateToken = StateToken (Array (BoundedInt 0 255))  -- 256 tokens
newtype ActionToken = ActionToken String

data Observation = ImageObservation (Array Frame)
               | VideoObservation { frames :: Array Frame, fps :: Natural }

data Frame = Frame
  { pixels :: Tensor3D  -- (C, H, W)
  , timestamp :: Millisecond
  , camera :: CameraId
  }

data WorldState = WorldState
  { entities :: Array Entity
  , dynamics :: PhysicsState
  , semantics :: Scene理解
  }

data Entity = Agent EntityId EntityType Pose Velocity
           | Object ObjectId Class BoundingBox
           | Background Terrain

data Action = MoveTo Vec3
          | PickUp ObjectId
          | PutDown ObjectId Vec3
          | Navigate Path
          | Custom String
```

### Grade Tracking

```purescript
-- PAN effects
data Effect
  = EncodePerception
  | PredictDynamics
  | GenerateVideo
  | SimulateWorld
  | ReasonAboutActions

-- PAN coeffects  
data CoEffect
  = RequiresHistoryLength Int
  | RequiresActionSpace ActionSpace
  | RequiresWorldDiversity Int
  | RequiresModelScale Int
  | RequiresTokenBudget Int
```

---


- [x] FOUR_OVER_SIX (NVFP4)
- [x] PRETRAINING_NVFP4
- [x] OPEN_PROBLEMS_MECHANISTIC_INTERPRETABILITY
- [x] GAIA2_WORLD_MODEL
- [x] PAN_WORLD_MODEL

---

## REMAINING PAPERS

- [x] TERAAGENT_SIMULATION
- [ ] FP4_ALL_THE_WAY
- [ ] MULTIMODAL_GUI
- [ ] MinMo_Voice
- [ ] GAMEFACTORY
- [ ] WORLDGEN_3D

---

## TERAAGENT_SIMULATION (Trillion-Scale Agent Simulation)

### Classification
- **Domain**: Multi-Agent Simulation / Distributed Computing
- **Effect**: Simulate(Agents), Coordinate(Communication), Scale(Compute)
- **Coeffect**: AgentCount, WorldSize, ComputeBudget

### AST Schema
```json
{
  "algorithm": "TeraAgent",
  "inputs": ["world_state", "agent_policies"],
  "outputs": ["simulated_trajectories"]
}
```

### Key Formulas

**(A) Spatial Partitioning**
```
Partition = divide_space(world_bounds, num_ranks)
Aura(region) = expand_region(region, max_interaction_distance)
```

**(B) Delta Encoding**
```
compressed = encode_delta(message, reference)
data_reduction = 1 - (compressed_size / original_size)
```

### Core Algorithms

```python
# Algorithm: TeraAgent Distributed Simulation

class TeraAgentSimulator:
  def __init__(self, num_ranks):
    self.partitioning = SpatialPartitioning()
    self.serialization = TeraAgentSerializer()
    self.delta_encoder = DeltaEncoder()
  
  def initialize(self, world_config, num_agents):
    # Distribute agents to authoritative ranks
    for agent in num_agents:
      rank = find_authoritative_rank(agent.position)
      self.agents[rank].add(agent)
  
  def step(self):
    # 1. Aura update (border regions)
    for rank in self.ranks:
      aura = compute_aura(self.partitions[rank])
      send_aura(rank, aura)
    
    # 2. Delta encoding for data transfer
    for rank in self.ranks:
      delta = self.delta_encoder.compress(
        current_aura, 
        reference_aura
      )
      send_delta(rank, delta)
    
    # 3. Agent updates (parallel)
    parallel_update(self.agents)
    
    # 4. Migration
    for agent in migrating_agents:
      migrate(agent, new_rank)
    
    # 5. Load balancing
    if imbalanced():
      rebalance()

# Serialization Algorithm
class TeraAgentSerializer:
  def serialize(self, agent_tree):
    # Tree traversal for objects on heap
    buffer = []
    for node in traverse_tree(agent_tree):
      # Replace vtable pointers with class IDs
      node.vtable = get_class_id(node)
      buffer.append(node)
    return buffer
  
  def deserialize(self, buffer, root_type):
    # Single-pass deserialization
    for node in buffer:
      if is_polymorphic(node):
        node.vtable = restore_vtable(node.class_id)
      if has_pointer(node):
        node.pointer = next_buffer_node()
    return buffer[0]

# Delta Encoding Algorithm
class DeltaEncoder:
  def encode(self, message, reference):
    # Reorder message to match reference
    reordered = reorder_to_match(message, reference)
    
    # Compute deltas
    result = []
    for i, (msg_node, ref_node) in enumerate(zip(reordered, reference)):
      if msg_node.value != ref_node.value:
        result.append((i, msg_node.value - ref_node.value))
      else:
        result.append((i, 0))  # Placeholder
    
    return result
  
  def decode(self, compressed, reference):
    # Restore from reference + deltas
    result = reference.copy()
    for (i, delta) in compressed:
      result[i] += delta
    return defragment(result)
```

### Distributed Architecture

```python
# Communication Pattern
class TeraAgentComm:
  def __init__(self):
    self.mpi = MPI()
  
  def aura_update(self, ranks):
    # Non-blocking point-to-point
    for rank in ranks:
      # Speculative receive
      req = self.mpi.irecv(rank)
      # Process while waiting
      await req
  
  def broadcast_partitioning(self):
    # Broadcast space partitioning
    self.mpi.bcast(self.partitioning_grid)

# Load Balancing
class LoadBalancer:
  def global_balance(self):
    # STK/Zoltan2 with RCB
    partition = recursive_coordinate_bisection(
      grid=self.grid,
      weight_field=self.compute_weights()
    )
  
  def diffusive_balance(self):
    # Iterative local adjustment
    for _ in range(iterations):
      for rank in ranks:
        adjust = compute_imbalance(rank)
        shift_agents(rank, adjust)
```

### Performance Results

| Metric | Value |
|--------|-------|
| Max Agents | 501.51 billion |
| CPU Cores | 84,096 |
| Memory | 92 TB |
| Time per Iteration | 147s |
| Speedup vs BioDynaMo | 8× |
| Serialization Speedup | 3.6× |

### Bounded Types

```purescript
newtype AgentId = AgentId (BoundedInt 0 1000000000000)
newtype RankId = RankId (BoundedInt 0 1024)
newtype PartitionId = PartitionId (BoundedInt 0 65535)

data Agent = Agent
  { id :: AgentId
  , position :: Vec3
  , state :: AgentState
  , behaviors :: Array Behavior
  }

---

## DREAMER4_WORLD_MODEL (World Model Agent)

### Classification
- **Domain**: Reinforcement Learning / World Models
- **Effect**: Tokenize(Video), Predict(Dynamics), Optimize(Policy)
- **Coeffect**: ContextLength, SamplingSteps, ImaginationHorizon

### AST Schema
```json
{
  "algorithm": "Dreamer4",
  "inputs": ["video_frames", "actions", "tasks"],
  "outputs": ["policy", "value_function", "world_model"],
  "parameters": {
    "K": 4,
    "K_max": 64,
    "gamma": 0.997,
    "lambda": 0.95,
    "context_length": 192,
    "spatial_tokens": 256
  }
}
```

### Key Formulas

**(1) Flow Matching**
```
x_τ = (1 - τ) * x₀ + τ * x₁
v = f_θ(x_τ, τ)
Loss = ||v - (x₁ - x₀)||²
```

**(2) Shortcut Forcing (Step Size Conditioning)**
```
if d == d_min:
    v_target = x₁ - x₀  # Flow matching
else:
    # Bootstrap: distill two half-steps
    v_target = (model(x, τ, d/2) + model(x', τ+d/2, d/2)) / 2
```

**(3) Shortcut Schedule Sampling**
```
d ∈ {1/1, 1/2, 1/4, 1/8, ..., 1/K_max}  # Power of 2
τ ∈ {0, d, 2d, ..., 1-d}  # Grid reachable by d
```

**(4) Diffusion Forcing (Per-Timestep τ)**
```
z_tilde[t] = (1 - τ[t]) * z₀[t] + τ[t] * z₁[t]
```

**(5) Ramp Weight (Focus on High Signal)**
```
w(t) = 0.9 * τ[t] + 0.1
```

**(6) X-Prediction (vs Velocity)**
```
# X-prediction prevents error accumulation in long rollouts
z1_hat = model(z_tilde, τ, d, actions)  # Predict clean x
v_pred = (z1_hat - z_tilde) / (1 - τ)
```

**(7) λ-Returns (TD Learning)**
```
R_λ[T-1] = V[T-1]
R_λ[t] = r[t] + γ * ((1 - λ) * V[t] + λ * R_λ[t+1])
```

**(8) PMPO Policy Loss**
```
# Sign-based advantages (scale-robust)
A_t = R_λ[t] - V[t]
if A_t >= 0: maximize log π(a_t | s_t)
else: minimize log π(a_t | s_t)
# KL constraint to behavioral prior
```

**(9) Symexp Twohot (Scale-Robust Output)**
```
symlog(x) = sign(x) * log1p(|x|)
symexp(x) = sign(x) * (exp(|x|) - 1)
# Twohot: distribute probability between adjacent bins
```

---

### Core Algorithms

```python
# Algorithm 1: Flow Matching Sampling

def flow_matching_sample(model, K=64):
    """
    Standard flow matching with Euler integration.
    K = number of denoising steps
    """
    d = 1 / K
    x = torch.randn_like(data_shape)  # x₀ ~ N(0, I)
    
    for tau in range(0, 1, d):
        v = model(x, tau)
        x = x + v * d
    
    return x  # x₁ (clean sample)


# Algorithm 2: Shortcut Model Training

def shortcut_model_loss(model, x0, x1, tau, d, d_min):
    """
    Shortcut model: condition on step size d.
    Enables few-step generation (K=4 vs K=64).
    """
    x_tau = (1 - tau) * x0 + tau * x1
    
    if d == d_min:
        # Flow matching at finest resolution
        v_target = x1 - x0
    else:
        # Bootstrap loss: distill two half-steps
        with torch.no_grad():
            b_prime = model(x_tau, tau, d/2)
            x_prime = x_tau + b_prime * (d/2)
            
            b_double_prime = model(x_prime, tau + d/2, d/2)
            v_target = (b_prime + b_double_prime) / 2
    
    v_pred = model(x_tau, tau, d)
    loss = (v_pred - v_target).pow(2).mean()
    
    return loss


# Algorithm 3: Shortcut Schedule

def sample_shortcut_schedule(K_max, T):
    """
    Sample step size d as power of 2.
    Sample τ from grid reachable by d.
    """
    k = np.random.choice([1, 2, 4, 8, K_max])
    d = 1 / k
    
    tau = np.random.choice([i * d for i in range(k)])
    
    return tau, d


# Algorithm 4: Dreamer4 Dynamics Model (Shortcut Forcing)

def shortcut_forcing_loss(dynamics_model, z1, actions, K_max=64):
    """
    Train dynamics model with shortcut forcing.
    Key: x-prediction (not v-prediction) prevents error accumulation.
    """
    B, T = z1.shape[:2]
    
    z0 = torch.randn_like(z1)
    tau, d = sample_shortcut_schedule(K_max, T)
    
    # Diffusion forcing: different τ per timestep
    z_tilde = (1 - tau.unsqueeze(-1)) * z0 + tau.unsqueeze(-1) * z1
    
    # Forward pass
    z1_hat = dynamics_model(z_tilde, tau, d, actions)
    
    # Compute loss per timestep with ramp weight
    loss = 0
    for t in range(T):
        if d[t] == 1/K_max:
            L_t = (z1_hat[t] - z1[t]).pow(2).mean()
        else:
            # Bootstrap loss
            with torch.no_grad():
                b_prime = (dynamics_model.forward_single(
                    z_tilde[t], tau[t], d[t]/2, actions[t]
                ) - z_tilde[t]) / (1 - tau[t])
                
                z_prime = z_tilde[t] + b_prime * (d[t]/2)
                
                b_double_prime = (dynamics_model.forward_single(
                    z_prime, tau[t] + d[t]/2, d[t]/2, actions[t]
                ) - z_prime) / (1 - (tau[t] + d[t]/2))
                
                v_target = (b_prime + b_double_prime) / 2
            
            v_pred = (z1_hat[t] - z_tilde[t]) / (1 - tau[t])
            scale = (1 - tau[t]).pow(2)
            L_t = scale * (v_pred - v_target).pow(2).mean()
        
        # Ramp weight: focus on high signal levels
        w_t = 0.9 * tau[t] + 0.1
        loss = loss + w_t * L_t
    
    return loss / T


# Algorithm 5: Interactive Video Generation

def generate_video(dynamics_model, tokenizer, first_frame, actions, K=4, tau_ctx=0.1):
    """
    Real-time inference with shortcut models.
    Achieves 20+ FPS on single GPU.
    """
    d = 1 / K
    z_history = [tokenizer.encode(first_frame)]
    
    for t in range(1, len(actions)):
        z_t = torch.randn_like(z_history[0])
        
        # Slightly corrupt history for robustness
        z_ctx = [(1 - tau_ctx) * torch.randn_like(z) + tau_ctx * z 
                 for z in z_history]
        
        # K denoising steps
        for step in range(K):
            tau = step * d
            z_t = dynamics_model(z_ctx + [z_t], 
                                  tau=[tau_ctx] * len(z_ctx) + [tau],
                                  d=[0] * len(z_ctx) + [d],
                                  actions=actions[:t+1])[-1]
        
        z_history.append(z_t)
    
    video = tokenizer.decode(torch.stack(z_history))
    return video


# Algorithm 6: PMPO Policy Optimization

def pmpo_policy_loss(policy_head, states, actions, advantages, policy_prior, 
                     alpha=0.5, beta=0.3):
    """
    Probabilistic MPO: robust RL using sign of advantages.
    Eliminates need for return normalization.
    """
    N = len(advantages)
    
    # Split by advantage sign
    D_plus = [i for i in range(N) if advantages[i] >= 0]
    D_minus = [i for i in range(N) if advantages[i] < 0]
    
    # Positive: maximize likelihood of good actions
    pos_loss = -sum(log_prob(actions[i], policy_head(states[i])) 
                    for i in D_plus) / max(len(D_plus), 1)
    
    # Negative: minimize likelihood of bad actions  
    neg_loss = sum(log_prob(actions[i], policy_head(states[i])) 
                   for i in D_minus) / max(len(D_minus), 1)
    
    # KL to behavioral prior
    kl_loss = sum(kl_divergence(policy_head(states[i]), policy_prior(states[i])) 
                  for i in range(N)) / N
    
    loss = alpha * pos_loss + (1 - alpha) * neg_loss + beta * kl_loss
    
    return loss


# Algorithm 7: Imagination Training Loop

def imagination_training(world_model, policy_head, value_head, policy_prior,
                        dataset, num_iterations=10000, horizon=16):
    """
    Phase 3: Learn purely in imagination, no environment interaction.
    """
    world_model.freeze_backbone()  # Only train heads
    
    for iteration in range(num_iterations):
        # Sample context
        context = dataset.sample_context()
        z_ctx = world_model.tokenizer.encode(context.frames)
        
        # Imagine rollout
        z_trajectory = [z_ctx[-1]]
        a_trajectory = []
        
        for t in range(horizon):
            a_t = policy_head.sample(z_trajectory[-1])
            a_trajectory.append(a_t)
            
            z_next = world_model.dynamics.generate_next(
                z_trajectory, a_trajectory, K=4
            )
            z_trajectory.append(z_next)
        
        # Compute returns
        rewards = [world_model.reward_head(z) for z in z_trajectory]
        values = [value_head(z) for z in z_trajectory]
        
        R_lambda = compute_lambda_returns(rewards, values, gamma=0.997)
        advantages = [R_lambda[t] - values[t] for t in range(len(values))]
        
        # Update heads
        value_loss = compute_value_loss(value_head, z_trajectory, R_lambda)
        value_loss.backward()
        
        policy_loss = pmpo_policy_loss(
            policy_head, z_trajectory, a_trajectory, 
            advantages, policy_prior
        )
        policy_loss.backward()
        
        optimizer.step()


# Algorithm 8: Symexp Twohot Distribution

def symexp_twohot(x, num_bins=255):
    """
    Scale-robust output distribution for rewards/values.
    Handles both small and large magnitudes.
    """
    def symlog(x):
        return torch.sign(x) * torch.log1p(torch.abs(x))
    
    def symexp(x):
        return torch.sign(x) * (torch.exp(torch.abs(x)) - 1)
    
    x_log = symlog(x)
    bin_range = torch.linspace(-20, 20, num_bins)
    
    # Twohot: probability between adjacent bins
    idx = torch.searchsorted(bin_range, x_log).clamp(1, num_bins - 1)
    lower = bin_range[idx - 1]
    upper = bin_range[idx]
    w = (x_log - lower) / (upper - lower)
    
    probs = torch.zeros(num_bins)
    probs[idx - 1] = 1 - w
    probs[idx] = w
    
    return probs
```

### Efficient Transformer Architecture

```python
# Factorized Space-Time Attention

class EfficientTransformerBlock(nn.Module):
    def __init__(self, dim, num_heads, is_temporal_layer=False):
        self.is_temporal = is_temporal_layer
        if is_temporal_layer:
            self.attn = CausalTimeAttention(dim, num_heads)
        else:
            self.space_attn = SpaceAttention(dim, num_heads)
    
    def forward(self, x, T, S):
        # T: timesteps, S: spatial tokens per frame
        if self.is_temporal:
            # Reshape: [B, T*S, D] -> [B*S, T, D]
            x = rearrange(x, 'b (t s) d -> (b s) t d', t=T, s=S)
            x = self.attn(x)  # Causal in time
            x = rearrange(x, '(b s) t d -> b (t s) d', s=S)
        else:
            # Reshape: [B, T*S, D] -> [B*T, S, D]
            x = rearrange(x, 'b (t s) d -> (b t) s d', t=T, s=S)
            x = self.space_attn(x)  # Full within frame
            x = rearrange(x, '(b t) s d -> b (t s) d', t=T)
        
        return x


# Training: Alternating Batch Lengths

def train_alternating_lengths(model, dataset, T_short=64, T_long=256):
    """
    Short batches: fast iteration
    Long batches: prevent overfitting to start frame
    """
    for step in range(num_steps):
        if step % 10 == 0:
            batch = dataset.sample(seq_len=T_long)
        else:
            batch = dataset.sample(seq_len=T_short)
        
        loss = model(batch)
        loss.backward()
        optimizer.step()
```

### Model Specifications

| Component | Parameters | Spatial Tokens | Context |
|-----------|------------|----------------|---------|
| Tokenizer | 400M | 960 | - |
| Dynamics | 1.6B | 256 | 192 frames |
| **Total** | **2B** | - | **9.6s @ 20FPS** |

### Hyperparameters

| Parameter | Value | Purpose |
|-----------|-------|---------|
| K | 4 | Sampling steps for inference |
| K_max | 64 | Training granularity |
| γ | 0.997 | Discount factor |
| λ | 0.95 | TD(λ) parameter |
| α | 0.5 | PMPO positive/negative balance |
| β | 0.3 | Prior KL weight |
| τ_ctx | 0.1 | Context noise |
| L | 8 | Multi-token prediction length |

### Bounded Types

```purescript
-- World Model Types
newtype SamplingSteps = SamplingSteps (BoundedInt 1 128)
newtype ContextFrames = ContextFrames (BoundedInt 1 512)
newtype ImaginationHorizon = ImaginationHorizon (BoundedInt 1 128)
newtype SpatialTokens = SpatialTokens (BoundedInt 64 1024)

data SignalLevel = SignalLevel Number  -- τ ∈ [0, 1]
data StepSize = StepSize Number         -- d ∈ {1, 1/2, 1/4, ...}

data DiffusionState s = 
  Noisy { noise :: s }
  | Corrupted { level :: SignalLevel, noise :: s, data :: s }
  | Clean { data :: s }

data WorldModel (tokenizer :: Tokenizer, dynamics :: Dynamics)


-- Graded Monad for World Model Effects
data Effect
  = TokenizeVideo
  | PredictDynamics
  | SampleActions
  | ComputeValue
  | ImagineTrajectory

data CoEffect
  = NeedsContextLength ContextFrames
  | NeedsSamplingSteps SamplingSteps
  | NeedsHorizon ImaginationHorizon
```

### Grade Tracking

```purescript
-- World Model is a graded monad tracking computation costs
tokenize :: Video -> WorldModel (NeedsContextLength C) Tokenized
predict :: Tokenized -> Actions -> WorldModel (NeedsSamplingSteps K) Predicted
imagine :: Policy -> WorldModel (NeedsHorizon H) Trajectory

-- Composing: more context = more compute
(>>=) :: WorldModel e1 c a -> (a -> WorldModel e2 c b) 
              -> WorldModel (e1 ⊗ e2) c b
```

---

### Grade Tracking

```purescript
data Effect
  = SerializeAgent
  | DeserializeAgent  
  | DeltaEncode
  | DeltaDecode
  | BroadcastPartition
  | MigrateAgent
  | BalanceLoad

data CoEffect
  = RequiresAgentCount Int
  | RequiresRankCount Int
  | RequiresMemoryBudget Bytes
  | RequiresInterconnectLatency Microseconds
```

---

## MINMO_VOICE (Multi-Modality to Modality)

### Classification
- **Domain**: Multi-Modal Language Models / Voice Synthesis
- **Effect**: Generate(Speech), Encode(Audio), Align(Modalities)
- **Coeffect**: AudioQuality, Latency, ModelScale

### AST Schema
```json
{
  "algorithm": "MinMo",
  "inputs": ["text", "audio_reference", "speaker_id"],
  "outputs": ["speech_waveform"]
}
```

### Key Formulas

**(A) Audio Encoding**
```
audio_features = encoder(audio_signal)
```

**(B) Text-Audio Alignment**
```
aligned = cross_attention(text_features, audio_features)
```

---

## MULTIMODAL_GUI (GUI Understanding)

### Classification
- **Domain**: Multi-Modal Understanding / GUI Agents
- **Effect**: Parse(GUI), Extract(Element), Infer(Intent)
- **Coeffect**: ScreenResolution, ElementCount, InteractionHistory

### Key Formulas

**(A) Element Detection**
```
elements = detector(screenshot)
tree = parser(elements)
```

**(B) Navigation Graph Exposure**
```
nav_graph = getNavigationGraph()
tools = getLocalTools() ⊕ getGlobalTools()
```

**(C) Voice Command Processing**
```
(action, new_state) = voiceCommand(audio, llm, viewState)
```

**(D) Tool Execution**
```
(result, updated_state) = executeTool(tool, current_state)
```

**(E) MCP Tool Schema**
```
mcp_tools = map(ViewModel.tools, toolSchema)
```

---

### Core Algorithms

```python
# Algorithm: MCP-Based GUI Agent

def build_mcp_tools(viewmodel):
    """
    Expose ViewModel tools via Model Context Protocol.
    
    Args:
        viewmodel: Current view state and available actions
        
    Returns:
        MCP-compatible tool definitions
    """
    local_tools = viewmodel.getLocalTools()    # Current view actions
    global_tools = viewmodel.getGlobalTools()   # App-wide actions
    nav_graph = viewmodel.getNavigationGraph()
    
    return {
        "tools": combine(local_tools, global_tools),
        "navigation": nav_graph,
        "context": viewmodel.getContext()
    }


def process_voice_command(audio, llm, viewmodel):
    """
    Process voice input to GUI action.
    
    Architecture:
    1. Audio input (STT or direct)
    2. LLM interprets intent
    3. Map to available tools
    4. Execute action
    5. Return new view state
    
    Args:
        audio: Voice input
        llm: Language model for intent inference
        viewmodel: Current application state
        
    Returns:
        (executed_action, new_viewstate)
    """
    # Get available tools for current view
    available_tools = viewmodel.getLocalTools()
    global_tools = viewmodel.getGlobalTools()
    all_tools = available_tools + global_tools
    
    # Intent inference with tool context
    intent = llm.infer_intent(
        audio_input=audio,
        available_tools=all_tools,
        navigation_graph=viewmodel.getNavigationGraph()
    )
    
    # Map intent to tool call
    if intent.tool_name in all_tools:
        result = viewmodel.executeTool(
            intent.tool_name,
            intent.parameters
        )
        return (intent.tool_name, result.newState)
    
    # Fallback: navigation intent
    if intent.type == "navigation":
        new_view = viewmodel.navigateTo(intent.target)
        return (f"navigate:{intent.target}", new_view)
    
    # Repair: clarification needed
    return ("CLARIFY", viewmodel.requestClarification(intent))


def detect_gui_elements(screenshot):
    """
    Detect and parse UI elements from screenshot.
    
    Used by computer use agents (CUA) to understand
    interface state.
    
    Args:
        screenshot: Current screen capture
        
    Returns:
        Element tree with spatial relationships
    """
    # Element detection via vision model
    raw_elements = vision_model.detect(screenshot)
    
    # Parse into hierarchical structure
    element_tree = parser.build_tree(raw_elements)
    
    # Add spatial relationships
    element_tree = spatial.add_relationships(element_tree)
    
    # Extract text content via OCR
    element_tree = ocr.annotate_text(element_tree)
    
    return element_tree


def predict_action(screen_state, task_goal, policy_model):
    """
    Predict next GUI action to accomplish task.
    
    Core of computer use agents - given current screen
    and user goal, predict optimal action sequence.
    
    Args:
        screen_state: Current GUI snapshot + element tree
        task_goal: User's expressed goal
        policy_model: Action prediction model
        
    Returns:
        Predicted action (click, type, scroll, etc.)
    """
    # Encode screen state
    screen_encoding = encoder.encode(screen_state)
    
    # Encode task
    task_encoding = encoder.encode_task(task_goal)
    
    # Get available actions
    available_actions = screen_state.available_actions
    
    # Score each action
    action_scores = policy_model.score_actions(
        screen_encoding,
        task_encoding,
        available_actions
    )
    
    # Select best action
    best_action = argmax(action_scores)
    
    return best_action


def voice_gui_alignment(spoken_input, visual_interface):
    """
    Align spoken commands with visible GUI elements.
    
    Critical for multimodal interaction - ensuring
    speech maps correctly to UI elements.
    
    Args:
        spoken_input: User's spoken request
        visual_interface: Current visible elements
        
    Returns:
        Aligned action with confidence score
    """
    # Parse spoken input
    parsed = speech_parser.parse(spoken_input)
    
    # Find matching elements
    candidates = []
    for element in visual_interface:
        similarity = string_similarity(parsed.text, element.accessibility_label)
        if similarity > THRESHOLD:
            candidates.append((element, similarity))
    
    # Rank by similarity + position
    ranked = sorted(candidates, key=lambda e: e[1], reverse=True)
    
    if ranked and ranked[0][1] > 0.8:
        return Action(
            target=ranked[0].element,
            confidence=ranked[0][1],
            type="direct"
        )
    
    # Fallback: semantic matching
    semantic_matches = semantic_search(parsed.meaning, visual_interface)
    
    if semantic_matches:
        return Action(
            target=semantic_matches[0].element,
            confidence=semantic_matches[0].score,
            type="semantic"
        )
    
    # Cannot resolve - request clarification
    return Action(type="clarify", options=visual_interface)
```

### Agentic System Relevance

| Component | Swarm Scale Relevance |
|-----------|----------------------|
| MCP Tool Exposure | Agents expose capabilities via standardized protocol |
| Element Detection | Agents perceive GUI state deterministically |
| Voice Alignment | Multimodal input interpretation for diverse agents |
| Navigation Graph | Structured environment understanding |

---

## GAMEFACTORY (Interactive Video for Games)

### Classification
- **Domain**: Game AI / Video Generation / Interactive Simulation
- **Effect**: Generate(Video), Control(Agent), Interact(Environment)
- **Coeffect**: GameType, Complexity, PlayerCount

### Key Formulas

**(A) Game State Encoding**
```
state = encoder(game_screen, game_state)
```

**(B) Action-conditioned Generation**
```
next_frame = generator(state, action)
```

---

## FP4_ALL_THE_WAY (Full FP4 Training)

### Classification
- **Domain**: LLM Training / 4-bit Precision
- **Effect**: Train(FP4), Compute(Gradients), Update(Weights)
- **Coeffect**: ModelSize, TokenCount, OutlierHandling

### Key Formulas

**(A) FP4 Matrix Multiplication**
```
C = A_FP4 × B_FP4
```

**(B) Gradient Quantization**
```
grad_quantized = stochastic_round(grad, FP4)
```

**(C) Gradient Noise Threshold**
```
σ_gradient < √3 × σ_quantization
# Below this threshold, quantized training loses effectiveness
# Solution: Quantization-Aware Finetuning (QAF) at end
```

**(D) Split Rounding Strategy**
```
Forward pass: RtN (lower MSE)
Backward pass: SR (reduces gradient bias)
```

**(E) Fully Quantized Matrix Multiplication**
```
C_FP32 = A_FP4_quantized × B_FP4_quantized
# All operations in FP4, scale factors applied
```

---

### Core Algorithms

```python
# Algorithm 1: NVFP4 Quantization

def quantize_nvfp4(x, block_size=16):
    """
    Quantize to NVIDIA FP4 format (E4M3).
    
    Format: 1 sign bit, 4 exponent bits, 3 mantissa bits
    Block size: 16 (per-channel scale)
    Scale: FP8 E4M3 per block
    """
    # Compute per-block scale
    x_abs_max = x.abs().amax(dim=-1, keepdim=True)  # [blocks]
    
    # FP4 max values
    M_FP4 = 6.0   # max representable FP4 value (E4M3)
    M_FP8 = 448.0 # max FP8 E4M3
    
    # Block scale factor
    scale = x_abs_max / (M_FP4 * M_FP8 / M_FP4)
    scale = scale.clamp(min=1e-10)
    
    # Scale to FP8 range
    x_scaled = x / scale
    
    # Quantize to FP4
    x_fp4 = round_to_fp4(x_scaled)
    
    return x_fp4, scale


# Algorithm 2: Stochastic Rounding (SR)

def stochastic_round(x, scale):
    """
    Stochastic rounding for backward pass.
    Reduces gradient bias compared to deterministic rounding.
    """
    mantissa_bits = 3
    scale_factor = 2 ** mantissa_bits
    
    x_scaled = x * scale_factor
    x_floor = torch.floor(x_scaled)
    x_frac = x_scaled - x_floor
    
    rand = torch.rand_like(x)
    x_quantized = x_floor + (rand < x_frac).float()
    
    x_fp4 = x_quantized / scale_factor
    
    return x_fp4


# Algorithm 3: FP4 Matrix Multiplication (FWD)

def fp4_matmul_forward(A, B, scale_A, scale_B):
    """
    Forward pass in FP4.
    All matmul operations in FP4.
    """
    A_fp4 = quantize_nvfp4(A)
    B_fp4 = quantize_nvfp4(B)
    
    C = torch.matmul(A_fp4, B_fp4)
    C = C * scale_A.t() * scale_B
    
    return C


# Algorithm 4: FP4 Backward Pass with SR

def fp4_matmul_backward(grad_output, A, B, scale_A, scale_B):
    """
    Backward pass uses stochastic rounding.
    Key for training stability.
    """
    A_fp4 = stochastic_round(A, scale_A)
    B_fp4 = stochastic_round(B, scale_B)
    
    grad_A = grad_output @ B_fp4.t() * scale_B
    grad_B = A_fp4.t() @ grad_output * scale_A.t()
    
    return grad_A, grad_B


# Algorithm 5: Gradient Noise Threshold Check

def check_gradient_noise_threshold(grad_norm, model_params):
    """
    Check if gradient noise is below quantization threshold.
    """
    quant_noise_estimate = estimate_quant_noise(model_params, bits=4)
    threshold = np.sqrt(3) * quant_noise_estimate
    
    if grad_norm < threshold:
        return True  # Apply QAF
    return False


# Algorithm 6: Quantization-Aware Finetuning (QAF)

def quantization_aware_finetune(model, dataloader, lr=1e-5):
    """
    Higher precision finetuning at end of FP4 training.
    """
    model = model.to(bfloat16)
    
    optimizer = torch.optim.AdamW(model.parameters(), lr=lr)
    
    for batch in dataloader:
        loss = model(batch)
        loss.backward()
        optimizer.step()
    
    return model


# Algorithm 7: Full FP4 Training Loop

def fp4_training_loop(model, dataloader, num_epochs, use_qaf=True):
    """
    Complete FP4 training pipeline.
    """
    model = convert_to_fp4(model)
    
    for epoch in range(num_epochs):
        for batch in dataloader:
            output = model(batch)
            loss = compute_loss(output, targets)
            loss.backward()
            
            grad_norm = compute_grad_norm(model)
            
            if use_qaf and check_gradient_noise_threshold(grad_norm, model):
                model = quantization_aware_finetune(model, remaining_data)
                break
            
            optimizer.step()
    
    return model


# Algorithm 8: FP4 Format Comparison

def compare_fp4_formats(model, test_data):
    """
    Compare MXFP4 vs NVFP4 formats.
    """
    results = {}
    
    model_nvfp4 = convert_to_format(model, "NVFP4", block_size=16, scale="E4M3")
    results["NVFP4"] = evaluate(model_nvfp4, test_data)
    
    model_mxfp4 = convert_to_format(model, "MXFP4", block_size=32, scale="E8M0")
    results["MXFP4"] = evaluate(model_mxfp4, test_data)
    
    return results
```

### Format Specifications

| Format | Exponent | Mantissa | Block Size | Scale Format | Notes |
|--------|----------|----------|------------|--------------|-------|
| E2M1 | 2 | 1 | - | - | Too small |
| E3M4 | 3 | 4 | - | - | Good |
| **E4M3** | 4 | 3 | **16** | **E4M3** | **Optimal** |
| E5M2 | 5 | 2 | - | - | Good but worse |
| MXFP4 | 2 | 1 | 32 | E8M0 | Microscaling |

### Training Results

| Tokens | Format | Final Loss | vs BF16 |
|--------|--------|-----------|---------|
| 200B | BF16 | 2.85 | baseline |
| 200B | FP4 (NVFP4) | 2.92 | +0.07 |
| 200B | FP4 + QAF | 2.86 | +0.01 |

### Bounded Types

```purescript
newtype BlockSize = BlockSize (BoundedInt 1 128)
newtype ExponentBits = ExponentBits (BoundedInt 1 8)
newtype MantissaBits = MantissaBits (BoundedInt 0 8)

data FP4Format
  = NVFP4 
      { blockSize :: BlockSize
      , exponentBits :: ExponentBits
      , mantissaBits :: MantissaBits
      }
  | MXFP4
      { blockSize :: BlockSize
      , scaleExponent :: ExponentBits
      , scaleMantissa :: MantissaBits
      }

data RoundingMode
  = RoundToNearest
  | Stochastic
  | GhostFloat

data TrainingPrecision
  = BF16
  | FP16
  | FP4FullyQuantized
      { weights :: FP4Format
      , activations :: FP4Format
      , gradients :: FP4Format
      , forwardRounding :: RoundingMode
      , backwardRounding :: RoundingMode
      }

newtype QuantizedTensor f = QuantizedTensor
  { values :: Array Int
  , scales :: Array Float
  , format :: f
  }
```

### Grade Tracking

```purescript
data Effect
  = QuantizeWeights
  | QuantizeActivations
  | QuantizeGradients
  | ComputeInFP4
  | ApplyQAF

data CoEffect
  = NeedsModelSize Int
  | NeedsTokenCount Int
  | NeedsPrecision Precision
  | NeedsBlockSize BlockSize
```

---

## WORLDGEN_3D (3D World Generation)

### Classification
- **Domain**: 3D Generation / Scene Understanding
- **Effect**: Generate(3D), Render(View), Edit(Scene)
- **Coeffect**: Resolution, Geometry, Materials

### Key Formulas

**(A) Geometry Generation**
```
mesh = generator(conditions)
```

**(B) Rendering**
```
image = render(mesh, camera, lighting)
```

---

## DEPTH_ANYTHING_3 (Multi-View Depth Estimation)

### Classification
- **Domain**: Computer Vision / Depth Estimation / Multi-View Geometry
- **Effect**: Estimate(Depth), Predict(Rays), Recover(CameraPose)
- **Coeffect**: NumViews, Resolution, PoseKnown

### AST Schema
```json
{
  "algorithm": "DepthAnything3",
  "inputs": ["images", "camera_params"],
  "outputs": ["depth_map", "ray_map", "point_cloud"],
  "parameters": {
    "backbone": "DINOv2",
    "layer_split": "2:1",
    "max_views": 18,
    "resolution": 504
  }
}
```

### Key Formulas

**(1) Depth-Ray Representation**
```
r = (t, d) where:
  t ∈ R³ = ray origin (camera center)
  d ∈ R³ = ray direction (unnormalized)
```

**(2) 3D Point Recovery**
```
P = t + D(u,v) · d
```
Where D is depth, (t,d) is ray from ray map.

**(3) Multi-Term Loss**
```
L = L_D + L_M + L_P + β·L_C + α·L_grad

L_D   = depth loss with confidence weighting
L_M   = ray map loss  
L_P   = point map consistency loss
L_C   = camera prediction loss
L_grad = gradient loss for sharp edges
```

**(4) Gradient Loss**
```
L_grad = ||∇_x D̂ - ∇_x D||₁ + ||∇_y D̂ - ∇_y D||₁
```

**(5) Confidence-Weighted Depth Loss**
```
L_D = (1/Z) Σ_p m_p · (D_c,p |D̂_p - D_p| - λ_c log D_c,p)
```

**(6) Depth Alignment (RANSAC)**
```
D_aligned = s_hat * D_teacher + t_hat
where (s_hat, t_hat) = ransac(D_teacher, D_metric)
```

**(7) Camera from Ray Map (DLT)**
```
t_c = mean(ray_origins)
H* = dlt_solve(pixels, ray_directions)
K, R = rq_decomposition(H*)
```

---

### Core Algorithms

```python
# Algorithm 1: Depth-Ray Prediction

def predict_depth_ray(image, model):
    """
    Single image → depth + ray map.
    Input-adaptive: works for 1 or N views.
    """
    features = model.backbone(image)  # DINOv2 features
    
    # Shared reassembly
    shared_features = model.reassembly(features)
    
    # Dual head
    depth = model.depth_fusion(shared_features)    # (H×W×1)
    ray_map = model.ray_fusion(shared_features)    # (H×W×6)
    
    return depth, ray_map


# Algorithm 2: Cross-View Attention

def cross_view_attention(tokens, num_views, layer_idx, L_s, L_g):
    """
    Input-adaptive attention pattern.
    
    tokens: [batch, num_views, num_patches, dim]
    L_s: within-view layers
    L_g: cross-view layers
    """
    if layer_idx < L_s:
        # Within-view only
        tokens = tokens.view(-1, num_patches, dim)
        return self_attention(tokens).view(batch, num_views, num_patches, dim)
    else:
        # Alternate cross/in-view
        if (layer_idx - L_s) % 2 == 0:
            # Cross-view: all tokens attend
            tokens = tokens.view(batch, -1, dim)
            return self_attention(tokens).view(batch, num_views, num_patches, dim)
        else:
            # Within-view
            tokens = tokens.view(-1, num_patches, dim)
            return self_attention(tokens).view(batch, num_views, num_patches, dim)


# Algorithm 3: Camera Condition Injection

def inject_camera(patch_tokens, camera_params=None):
    """
    Optional camera pose via prepended tokens.
    camera_params: (K, R, t) if known
    """
    if camera_params is not None:
        K, R, t = camera_params
        f = fov_from_intrinsics(K)      # R²
        q = rotation_to_quaternion(R)  # R⁴
        camera_token = camera_encoder(torch.cat([f, q, t], dim=-1))
    else:
        camera_token = learned_camera_token
    
    return torch.cat([camera_token, patch_tokens], dim=1)


# Algorithm 4: Depth Alignment with RANSAC

def align_depth(teacher_depth, sparse_metric_depth, validity_mask):
    """
    Align relative depth to metric scale via RANSAC.
    """
    valid_teacher = teacher_depth[validity_mask]
    valid_metric = sparse_metric_depth[validity_mask]
    
    # Solve: D_metric ≈ s * D_teacher + t
    s_hat, t_hat = ransac_least_squares(
        valid_teacher, valid_metric,
        inlier_threshold=median_absolute_deviation(residuals)
    )
    
    aligned_depth = s_hat * teacher_depth + t_hat
    
    return aligned_depth


# Algorithm 5: Ray Map to Camera Parameters

def ray_map_to_camera(ray_map):
    """
    Recover (R, K, t) from dense ray map via DLT.
    """
    H, W = ray_map.shape[:2]
    
    # Camera center = mean of ray origins
    t_c = ray_map[:,:,:3].mean(dim=(0,1))
    
    # Collect pixel coordinates and ray directions
    pixels = []
    rays = []
    for h in range(H):
        for w in range(W):
            p = torch.tensor([w, h, 1.0])
            d = ray_map[h, w, 3:]
            pixels.append(p)
            rays.append(d)
    
    # Solve homography
    H_star = dlt_solve(pixels, rays)
    
    # Decompose H* = K·R
    K, R = rq_decomposition(H_star)
    
    return R, K, t_c


# Algorithm 6: Depth-Ray Fusion → Point Cloud

def fuse_depth_ray(depth_map, ray_map):
    """
    Element-wise fusion to 3D point cloud.
    
    P = t + D(u,v) · d
    """
    origins = ray_map[:,:,:3]      # t per pixel
    directions = ray_map[:,:,3:]   # d per pixel
    
    points = origins + depth_map.unsqueeze(-1) * directions
    
    return points  # (H×W×3)


# Algorithm 7: Multi-View Point Cloud Fusion

def multi_view_fusion(depth_maps, ray_maps):
    """
    Fuse N views into unified point cloud.
    """
    all_points = []
    for depth, rays in zip(depth_maps, ray_maps):
        points = fuse_depth_ray(depth, rays)
        all_points.append(points.reshape(-1, 3))
    
    return torch.cat(all_points, dim=0)


# Algorithm 8: Teacher Model (Synthetic → Real)

def train_teacher_model(synthetic_datasets):
    """
    Phase 1: Train on synthetic data only.
    Phase 2: Generate pseudo-labels for real data.
    """
    # Teacher: exponential depth representation
    model = DepthModel(backbone='DINOv2')
    
    # Train on synthetic
    for dataset in synthetic_datasets:
        train_on_synthetic(model, dataset)
    
    # Generate pseudo-labels
    pseudo_labels = []
    for real_image in real_datasets:
        depth = model.predict_depth(real_image)
        aligned = align_depth(depth, get_sparse_gt(real_image))
        pseudo_labels.append(aligned)
    
    return model, pseudo_labels
```

### Training Configuration

| Parameter | Value |
|-----------|-------|
| GPUs | 128 H100 |
| Steps | 200k (8k warmup) |
| Resolution | 504×504 |
| Views per batch | [2, 18] |
| Pose conditioning prob | 0.2 |
| Teacher transition | 120k steps |

### Results

| Benchmark | Improvement vs VGGT |
|-----------|-------------------|
| Pose accuracy | +35.7% |
| Geometric accuracy | +23.6% |
| Monocular depth | +2.1% (vs DA2) |

### Bounded Types

```purescript
-- Depth-Ray Representation
newtype DepthValue = DepthValue Number  -- R⁺ (positive)
newtype RayOrigin = RayOrigin (Vec3 Number)
newtype RayDirection = RayDirection (Vec3 Number)

data Ray = Ray
  { origin :: RayOrigin
  , direction :: RayDirection
  }

type RayMap = Array2D Ray  -- H×W

type DepthMap = Array2D DepthValue

-- Camera Parameters
newtype FocalLength = FocalLength Number  -- R²
newtype CameraQuaternion = CameraQuaternion (Vec4 Number)  -- S³

data CameraParams = CameraParams
  { intrinsics :: Mat3x3
  , rotation :: Mat3x3
  , translation :: Vec3
  }

-- Point cloud from fusion
type Point3D = Vec3 Number
type PointCloud = Array Point3D

-- Multi-view input
newtype NumViews = NumViews (BoundedInt 1 18)
newtype ImageResolution = ImageResolution (BoundedInt 64 1024)
```

### Grade Tracking

```purescript
data Effect
  = EstimateDepth
  | PredictRays
  | RecoverCamera
  | FusePointCloud

data CoEffect
  = NeedsNumViews NumViews
  | NeedsResolution ImageResolution
  | HasKnownPose Bool
  | NeedsSyntheticTraining
```

---

## GAMEFACTORY (Action-Controlled Video Generation)

### Classification
- **Domain**: Video Generation / Game AI / Interactive Media
- **Effect**: Generate(Video), Control(Actions), Generalize(Scenes)
- **Coeffect**: ActionSpace, VideoLength, SceneComplexity

### AST Schema
```json
{
  "algorithm": "GameFactory",
  "inputs": ["video_frames", "keyboard_actions", "mouse_actions", "prompt"],
  "outputs": ["generated_video"],
  "parameters": {
    "window_size": 4,
    "compression_ratio": 4,
    "lora_rank": 128,
    "resolution": [360, 640]
  }
}
```

### Key Formulas

**(1) Action-Conditioned Loss**
```
L_a(ϕ) = E[||ε_ϕ(Z_t, p, A, t) - ε||²₂]
```

**(2) Action Grouping (Sliding Window)**
```
For i-th feature: actions ∈ [a_{r×(i-w+1)}, ..., a_{r×i}]
```
Where r = compression ratio, w = window size.

**(3) Autoregressive Training**
```
Loss only on predicted frames (not condition frames)
Eliminates noise interference from already-generated frames
```

**(4) Multi-Phase Training**
```
Phase 1: LoRA for style adaptation
Phase 2: Action control module only
Phase 3: Remove LoRA → open-domain inference
```

---

### Core Algorithms

```python
# Algorithm 1: Action Grouping with Sliding Window

def group_actions(actions, feature_idx, window_size, compression_ratio):
    """
    Group actions to match temporal compression.
    
    actions: raw action sequence
    feature_idx: which feature to group for
    window_size: w
    compression_ratio: r
    """
    start_idx = compression_ratio * (feature_idx - window_size + 1)
    end_idx = compression_ratio * feature_idx
    
    grouped = []
    for j in range(start_idx, end_idx + 1):
        if j < 0:
            grouped.append(actions[0])
        elif j >= len(actions):
            grouped.append(actions[-1])
        else:
            grouped.append(actions[j])
    
    return grouped


# Algorithm 2: Mouse Movement Control (Concatenation)

def mouse_control(M_group, F):
    """
    Continuous signals: concatenation preserves magnitude.
    
    M_group: (n+1, rw, d₁) grouped mouse
    F: (n+1, l, c) features
    """
    M_reshaped = M_group.reshape(n+1, 1, rw * d1)
    M_repeat = M_reshaped.repeat(1, l, 1)
    F_fused = torch.cat([F, M_repeat], dim=-1)
    F_out = temporal_self_attention(mlp(F_fused))
    
    return F_out


# Algorithm 3: Keyboard Action Control (Cross-Attention)

def keyboard_control(K_group, F):
    """
    Discrete signals: cross-attention for similarity matching.
    
    K_group: (n+1, rw, c) grouped keyboard embeddings
    F: (n+1, l, c) features
    """
    Q = F
    K = K_group
    V = K_group
    
    attention_weights = softmax(Q @ K.transpose(-2, -1) / sqrt(c))
    F_out = attention_weights @ V
    
    return F_out


# Algorithm 4: Autoregressive Training

def autoregressive_training(latents, k, N):
    """
    Train with varying condition/prediction split.
    
    k: first k+1 frames are conditions
    N-k: frames to predict
    """
    condition_frames = latents[:k+1 = latents[k]
    predict_frames+1:N+1]
    
    noisy_predict = add_noise(predict_frames, timestep=t)
    model_input = concat(condition_frames, noisy_predict)
    
    predicted_noise = model(model_input, prompt, actions, t)
    
    # CRITICAL: Loss only on predicted frames
    loss = mse_loss(predicted_noise[k+1:], actual_noise[k+1:])
    
    return loss


# Algorithm 5: Autoregressive Inference

def autoregressive_inference(initial_latents, actions, prompt, k, N):
    """
    Generate unlimited-length video.
    
    k: condition frames per iteration
    N-k: new frames per iteration
    """
    history = initial_latents
    
    while generating:
        condition = history[-k-1:]
        next_actions = get_next_actions()
        
        new_frames = diffusion_sample(
            condition_frames=condition,
            actions=next_actions,
            prompt=prompt,
            num_steps=50
        )
        
        history = concat(history, new_frames)
    
    return history


# Algorithm 6: Multi-Phase Training

def phase_1_style_adaptation(pretrained_model, game_data):
    """
    Tune LoRA to fit game style.
    """
    lora = LoRA(rank=128)
    pretrained_model.requires_grad_(False)
    lora.requires_grad_(True)
    
    for batch in game_data:
        loss = diffusion_loss(pretrained_model + lora, batch)
        loss.backward()
        optimizer.step()
    
    return lora


def phase_2_action_control(pretrained_model, lora, game_data_with_actions):
    """
    Freeze: pretrained_model + lora
    Train: only action_control_module
    """
    action_module = ActionControlModule()
    
    pretrained_model.requires_grad_(False)
    lora.requires_grad_(False)
    action_module.requires_grad_(True)
    
    for batch in game_data_with_actions:
        frames, actions, prompts = batch
        loss = action_conditioned_loss(
            pretrained_model + lora + action_module,
            frames, actions, prompts
        )
        loss.backward()
        optimizer.step()
    
    return action_module


def phase_3_inference(pretrained_model, action_module, prompt, actions):
    """
    Remove LoRA for open-domain generation.
    """
    model = pretrained_model + action_module
    video = generate(model, prompt, actions)
    return video


# Algorithm 7: Complete Action Control Module

class ActionControlModule:
    def __init__(self, config):
        self.window_size = config.window_size
        self.compression_ratio = config.compression_ratio
        self.keyboard_embedding = nn.Embedding(config.num_keys, config.channels)
        self.positional_encoding = PositionalEncoding(config.channels)
        self.mouse_mlp = nn.Linear(config.mouse_dim * config.window_size, config.channels)
        self.keyboard_cross_attn = CrossAttention(config.channels)
        self.temporal_self_attn = TemporalSelfAttention(config.channels)
    
    def forward(self, features, mouse_actions, keyboard_actions):
        n_plus_1 = features.shape[1]
        
        # Group actions
        mouse_grouped = self.group_with_window(mouse_actions, n_plus_1)
        keyboard_grouped = self.group_with_window(keyboard_actions, n_plus_1)
        
        # Keyboard: embed → positional → cross-attention
        keyboard_embedded = self.keyboard_embedding(keyboard_grouped.argmax(-1))
        keyboard_embedded = self.positional_encoding(keyboard_embedded)
        features = self.keyboard_cross_attn(query=features, key=keyboard_embedded, value=keyboard_embedded)
        
        # Mouse: reshape → repeat → concatenate → MLP → temporal
        mouse_flat = mouse_grouped.reshape(mouse_grouped.shape[0], n_plus_1, -1)
        mouse_repeated = mouse_flat.unsqueeze(2).expand(-1, -1, features.shape[2], -1)
        features_fused = torch.cat([features, mouse_repeated], dim=-1)
        features = self.temporal_self_attn(self.mouse_mlp(features_fused))
        
        return features
```

### Training Configuration

| Phase | What | LoRA | Action Module | Duration |
|-------|------|------|---------------|----------|
| 1 | Style | Train | Frozen | 2-4 days |
| 2 | Action | Frozen | Train | 2-4 days |
| 3 | Inference | Removed | Active | - |

### Results

| Metric | Multi-Phase | One-Phase |
|--------|-------------|------------|
| Cam (↓) | 0.0997 | 0.1134 |
| Flow (↓) | 54.13 | 76.02 |
| FID (↓) | 121.18 | 167.79 |

### Bounded Types

```purescript
-- Action Types
newtype NumKeys = NumKeys (BoundedInt 1 32)
newtype WindowSize = WindowSize (BoundedInt 1 16)
newtype CompressionRatio = CompressionRatio (BoundedInt 1 16)

data ActionType
  = KeyboardAction
      { key :: KeyCode
      , pressed :: Boolean
      }
  | MouseAction
      { dx :: Number  -- delta X
      , dy :: Number  -- delta Y
      }

newtype ActionSequence = ActionSequence (Array ActionType)

-- Video Generation
newtype VideoLength = VideoLength (BoundedInt 1 10000)
newtype FrameResolution = FrameResolution { width :: Pixel, height :: Pixel }

data GameVideo = GameVideo
  { frames :: Array Frame
  , actions :: ActionSequence
  , prompt :: Text
  }

-- Control signals
newtype LoRARank = LoRARank (BoundedInt 1 512)
newtype ControllerType = CrossAttention | Concatenation
```

### Grade Tracking

```purescript
data Effect
  = GenerateVideo
  | ControlActions
  | AdaptStyle
  | GeneralizeScene

data CoEffect
  = NeedsActionSpace NumKeys
  | NeedsVideoLength VideoLength
  | NeedsLoRARank LoRARank
  | NeedsMultiPhaseTraining
```

---

### Grade Tracking

Each algorithm entry:

```
## SPATIA_VIDEO_MEMORY (Video Generation with Spatial Memory)

### Classification
- **Domain**: Video Generation / Spatial Memory / 3D Vision
- **Effect**: Generate(Video), Update(Memory), Control(Camera)
- **Coeffect**: PointCloudDensity, ReferenceFrames, TemporalContext

### AST Schema
```json
{
  "algorithm": "Spatia",
  "inputs": ["initial_image", "text_instruction", "camera_path", "preceding_frames"],
  "outputs": ["generated_video_clips"],
  "parameters": {
    "backbone": "Wan2.2_5B",
    "controlnet_blocks": 8,
    "lora_rank": 64,
    "max_reference_frames": 7,
    "point_cloud_cube_side": 0.01,
    "window_size": 4,
    "compression_ratio": 4
  }
}
```

### Key Formulas

**(1) Flow Matching Loss**
```
L = E_{t,x₀,X_T}[||v_t - u_t||²]
```
where t ~ logit-normal, x_t = (1-t)x₀ + tX_T

**(2) 3D IoU for Reference Retrieval**
```
s(T_i, C_j) = 3DIoU(S_T_i, register(S_C_j, S_T_i))
```

**(3) Action Grouping for Temporal Compression**
```
For i-th feature: actions ∈ [a_{r×(i-w+1)}, ..., a_{r×i}]
```
Where r = compression ratio, w = window size.

**(4) Point Cloud Projection**
```
X_S = encoder(project(point_cloud, camera_pose))
```

**(5) Dynamic-Static Disentanglement**
```
Static: S_static = update_pointcloud(frame, exclude_masks)
Dynamic: V_dynamic = generate(frame, S_static, text)
```

---

### Core Algorithms

```python
# Algorithm 1: Spatial Memory Initialization

def init_spatial_memory(initial_image):
    """
    Initialize 3D scene point cloud from initial image.
    
    Uses MapAnything for universal metric 3D reconstruction.
    
    Args:
        initial_image: User-provided first frame
        
    Returns:
        Scene point cloud for spatial memory
    """
    # Estimate 3D structure
    point_cloud = MapAnything.reconstruct(initial_image)
    
    # Segment dynamic entities (for later disentanglement)
    dynamic_masks = SAM2.segment_all(initial_image)
    
    # Store in spatial memory
    memory = SpatialMemory(
        point_cloud=point_cloud,
        dynamic_masks=dynamic_masks,
        camera_poses=[initial_camera_pose]
    )
    
    return memory


def update_spatial_memory(memory, generated_frames):
    """
    Update spatial memory with newly generated frames.
    
    Iteratively refine point cloud using visual SLAM.
    
    Args:
        memory: Current spatial memory state
        generated_frames: Newly generated video frames
        
    Returns:
        Updated spatial memory
    """
    # Extract dynamic masks (to exclude from point cloud)
    static_mask = memory.get_static_mask()
    
    # Update point cloud using MapAnything
    new_point_cloud = MapAnything.update(
        memory.point_cloud,
        generated_frames,
        exclude_mask=static_mask
    )
    
    # Update camera poses
    new_poses = visual_slam.estimate(generated_frames)
    
    return SpatialMemory(
        point_cloud=new_point_cloud,
        dynamic_masks=memory.dynamic_masks,
        camera_poses=memory.camera_poses + new_poses
    )


def retrieve_reference_frames(target_frames, candidate_frames, 
                              target_point_clouds, candidate_point_clouds,
                              threshold=0.3, max_refs=7):
    """
    Reference Frame Retrieval based on 3D spatial overlap.
    
    Key innovation: select frames with maximum spatial overlap
    for consistency guidance.
    
    Args:
        target_frames: Frames to generate
        candidate_frames: Candidate reference frames
        target_point_clouds: Scene point clouds for targets
        candidate_point_clouds: Scene point clouds for candidates
        threshold: Minimum 3D IoU to consider
        max_refs: Maximum reference frames to retrieve
        
    Returns:
        Retrieved reference frames
    """
    retrieved = []
    
    for target_frame in target_frames:
        S_target = target_point_clouds[target_frame]
        best_candidate = None
        best_score = 0
        
        for candidate_frame in candidate_frames:
            S_candidate = candidate_point_clouds[candidate_frame]
            
            # Register candidate to target coordinate frame
            S_registered = register_point_clouds(S_candidate, S_target)
            
            # Compute 3D IoU
            score = compute_3d_iou(S_target, S_registered)
            
            if score > threshold and score > best_score:
                best_score = score
                best_candidate = candidate_frame
        
        if best_candidate:
            retrieved.append(best_candidate)
    
    # Limit to max_refs
    return retrieved[:max_refs]


def generate_video_clip(memory, text_instruction, camera_path, 
                       preceding_frames, reference_frames):
    """
    Generate video clip conditioned on spatial memory.
    
    Core generation algorithm combining:
    - Scene projection from point cloud
    - Text conditioning
    - Temporal context from preceding frames
    - Reference frames for consistency
    
    Args:
        memory: Current spatial memory
        text_instruction: User's text prompt
        camera_path: Desired camera trajectory
        preceding_frames: Previous generated frames
        reference_frames: Retrieved reference frames
        
    Returns:
        Generated video clip
    """
    # Encode inputs
    X_T = video_encoder.encode(target_frames)
    X_P = video_encoder.encode(preceding_frames)
    X_R = video_encoder.encode(reference_frames)
    
    # Render point cloud projection along camera path
    projections = []
    for pose in camera_path:
        projection = render_point_cloud(memory.point_cloud, pose)
        projections.append(projection)
    X_S = video_encoder.encode(projections)
    
    # Encode text
    X_text = text_encoder.encode(text_instruction)
    
    # Diffusion process with all conditioning
    for block in range(num_blocks):
        # ControlNet: scene projection conditioning
        controlnet_out = controlnet_blocks[block](X_S)
        
        # Main block: self-attention + cross-attention
        main_out = main_blocks[block](X_T, X_P, X_R)
        
        # Add controlnet residual
        output = main_out + controlnet_out
        
        # Cross-attention to text
        output = cross_attention(output, X_text)
        
        X_T = output
    
    # Decode to video
    video = decoder.decode(X_T)
    
    return video


def dynamic_static_disentangle(initial_image, memory):
    """
    Separate static scene from dynamic entities.
    
    Process:
    1. Segment dynamic entities with SAM2
    2. Exclude dynamic regions from point cloud updates
    3. Generate dynamic content while keeping static scene fixed
    
    Args:
        initial_image: Starting frame
        memory: Current spatial memory
        
    Returns:
        Static regions mask, dynamic regions mask
    """
    # Segment dynamic entities
    dynamic_masks = SAM2.track(initial_image)
    
    # Create static mask (inverse of dynamic)
    static_mask = invert_masks(dynamic_masks)
    
    # Update memory to exclude dynamic regions
    memory_static = memory.with_mask(static_mask)
    
    return static_mask, dynamic_masks, memory_static


def closed_loop_consistency_check(initial_image, final_frame, memory):
    """
    Test spatial memory effectiveness via closed-loop generation.
    
    Camera trajectory returns to initial viewpoint.
    Compare final frame to initial image.
    
    Args:
        initial_image: Starting frame
        final_frame: Frame when camera returns
        memory: Final spatial memory state
        
    Returns:
        Consistency metrics: PSNR, SSIM, LPIPS
    """
    # Compute metrics
    psnr = compute_psnr(initial_image, final_frame)
    ssim = compute_ssim(initial_image, final_frame)
    lpips = compute_lpips(initial_image, final_frame)
    
    # Check visual match
    match_accuracy = compute_match_accuracy(initial_image, final_frame)
    
    return {
        "psnr": psnr,
        "ssim": ssim,
        "lpips": lpips,
        "match_accuracy": match_accuracy
    }


def render_point_cloud_projection(point_cloud, camera_pose):
    """
    Render point cloud from specific camera viewpoint.
    
    Used as conditioning signal for camera-controllable
    video generation.
    
    Args:
        point_cloud: 3D scene point cloud
        camera_pose: Camera position and orientation
        
    Returns:
        2D projection image
    """
    # Project 3D points to 2D image plane
    points_2d = project_to_image(point_cloud.points, camera_pose)
    
    # Rasterize with depth
    depth_buffer = create_depth_buffer(points_2d, point_cloud.depth)
    
    # Color with point colors
    color_buffer = rasterize_points(points_2d, point_cloud.colors, depth_buffer)
    
    return color_buffer
```

### Agentic System Relevance

| Component | Swarm Scale Relevance |
|-----------|----------------------|
| Spatial Memory | Agents maintain persistent scene understanding |
| Dynamic-Static Disentangle | Separate environment state from actors |
| Reference Retrieval | Find relevant prior context efficiently |
| Closed-Loop Consistency | Verify action effects match expectations |

---

## COSYVOICE2_TTS (Streaming Speech Synthesis)

### Classification
- **Domain**: Speech Synthesis / Audio Generation / Streaming AI
- **Effect**: Generate(Speech), Tokenize(Audio), Match(Flow)
- **Coeffect**: Latency, SpeakerIdentity, Prosody

### AST Schema
```json
{
  "algorithm": "CosyVoice2",
  "inputs": ["text", "reference_audio", "speaker_prompt"],
  "outputs": ["speech_waveform"],
  "parameters": {
    "lm_backbone": "Qwen2.5-0.5B",
    "fsq_levels": 10,
    "token_rate_hz": 25,
    "mel_rate_hz": 50,
    "lookahead_conv_p": 4,
    "streaming_chunk_m": 15,
    "first_packet_latency_ms": 150
  }
}
```

### Key Formulas

**(1) Finite Scalar Quantization (FSQ)**
```
H_quantized = ROUND(ProjDown(H))
Token_Index = Σ_{j=0}^{D-1} ĥ_j × (2K + 1)^j
```
Where K = quantization level, D = dimension.

**(2) Optimal Transport Flow Matching**
```
φ_t(X_0, X_1) = (1 - t)X_0 + tX_1
```
t ∈ [0, 1] is flow time.

**(3) Chunk-Aware Causal Generation**
```
For chunk i: generate M tokens with lookahead P=4
Upsample: 25 Hz (tokens) → 50 Hz (Mel)
```

**(4) Sequence Construction**
```
Non-streaming: [S, text, T, speech, E]
Streaming: [S, text_1...text_N, speech_1...speech_M] × k
```

---

### Core Algorithms

```python
# Algorithm 1: FSQ Speech Tokenization

def fsq_encode(speech_signal):
    """
    Finite Scalar Quantization for speech tokens.
    
    Replaces VQ with differentiable quantization.
    
    Args:
        speech_signal: Raw audio waveform
        
    Returns:
        Discrete token indices at 25 Hz
    """
    # Encode to latent space
    H = encoder(speech_signal)  # (T, D)
    
    # Project down to low-rank space
    H_low = proj_down(H)  # (T, D_low)
    
    # Quantize to discrete levels
    H_quantized = round(H_low)  # Values in [-K, K]
    
    # Compute token indices
    token_indices = []
    for t in range(H_quantized.shape[0]):
        idx = 0
        for j in range(H_quantized.shape[1]):
            level = int(H_quantized[t, j])
            idx += (level + K) * (2 * K + 1) ** j
        token_indices.append(idx)
    
    # Reconstruct for loss computation
    H_reconstructed = proj_up(H_quantized)
    
    return token_indices, H_reconstructed


def fsq_decode(token_indices):
    """
    Decode FSQ tokens back to latent features.
    
    Args:
        token_indices: Discrete token indices
        
    Returns:
        Reconstructed latent features
    """
    D = quant_dim
    K = quantization_levels
    
    # Decode indices to quantized values
    H_quantized = []
    for idx in token_indices:
        h_row = []
        remaining = idx
        for j in range(D):
            level = remaining % (2 * K + 1)
            h_row.append(level - K)
            remaining //= (2 * K + 1)
        H_quantized.append(h_row)
    
    H_quantized = tensor(H_quantized)
    
    # Project up
    H_reconstructed = proj_up(H_quantized)
    
    return H_reconstructed


# Algorithm 2: Text-Speech Language Model

def generate_speech_tokens(text, speaker_prompt, lm_model, 
                          streaming=False, max_tokens=500):
    """
    Generate speech tokens from text using LLM backbone.
    
    Unified model for both streaming and non-streaming.
    
    Args:
        text: Input text string
        speaker_prompt: Reference audio for voice cloning
        lm_model: Qwen2.5-0.5B based LM
        streaming: Whether to use streaming mode
        max_tokens: Maximum tokens to generate
        
    Returns:
        Generated speech token sequence
    """
    # Tokenize text
    text_tokens = tokenizer.encode(text)
    
    # Extract speaker features from prompt
    speaker_features = speaker_encoder(speaker_prompt)
    
    if streaming:
        # Streaming mode: interleaved text/speech
        N = 5  # Text chunk size
        M = 15  # Speech chunk size
        
        tokens = [START_TOKEN]
        for text_chunk in chunk(text_tokens, N):
            # Append text tokens
            tokens.extend(text_chunk)
            
            # Generate M speech tokens
            for _ in range(M):
                next_token = lm_model.predict(
                    tokens,
                    speaker_features=speaker_features
                )
                tokens.append(next_token)
                
                if next_token == END_TOKEN:
                    break
    else:
        # Non-streaming: full sequence
        tokens = [START_TOKEN] + text_tokens + [TEXT_END]
        while len(tokens) < max_tokens:
            next_token = lm_model.predict(
                tokens,
                speaker_features=speaker_features
            )
            tokens.append(next_token)
            if next_token == END_TOKEN:
                break
    
    return tokens


# Algorithm 3: Chunk-Aware Causal Flow Matching

class ChunkAwareFlowMatching:
    """
    Causal flow matching for streaming speech synthesis.
    
    Key features:
    - Lookahead convolution (P=4) for context
    - Chunk-based generation (M tokens at a time)
    - Upsampling: 25 Hz → 50 Hz
    """
    
    def __init__(self, model, lookahead_p=4):
        self.model = model
        self.lookahead_p = lookahead_p
        self.buffer = None
    
    def generate_chunk(self, tokens, flow_steps=10):
        """
        Generate a chunk of mel spectrogram.
        
        Args:
            tokens: Speech tokens
            flow_steps: Number of flow matching steps
            
        Returns:
            Mel spectrogram chunk (at 50 Hz)
        """
        # Embed tokens
        token_embeds = self.model.embedding(tokens)
        
        # Add causal lookahead convolution
        # Pad right with P-1 zeros for future context
        padded = F.pad(token_embeds, (0, self.lookahead_p))
        causal_embeds = causal_conv1d(padded)
        
        # Flow matching denoising
        x_t = torch.randn_like(target_mel)  # Start from noise
        
        for t in torch.linspace(0, 1, flow_steps):
            # Predict velocity
            velocity = self.model(x_t, causal_embeds, t)
            
            # Update (OT flow: xt = (1-t)x0 + t*x1)
            x_t = x_t + velocity * (1 / flow_steps)
        
        # Upsample: 25 Hz → 50 Hz
        mel_upsampled = F.interpolate(
            x_t, 
            scale_factor=2, 
            mode='linear',
            align_corners=False
        )
        
        return mel_upsampled


# Algorithm 4: Streaming Synthesis Pipeline

def streaming_tts(text_stream, audio_context, cosyvoice_model):
    """
    Full streaming TTS pipeline.
    
    First packet: 150ms latency
    Subsequent: Real-time with buffer
    
    Args:
        text_stream: Iterator of text chunks
        audio_context: Speaker reference audio
        cosyvoice_model: Full CosyVoice2 model
        
    Returns:
        Stream of audio packets
    """
    # Initialize
    lm_model = cosyvoice_model.lm
    flow_model = cosyvoice_model.flow
    vocoder = cosyvoice_model.vocoder
    
    # Process first chunk (higher latency for context)
    first_text = next(text_stream)
    tokens = generate_speech_tokens(
        first_text, 
        audio_context, 
        lm_model,
        streaming=True
    )
    
    # Generate first mel chunk
    mel = flow_model.generate_chunk(tokens[:50])  # First ~1 second
    audio = vocoder.generate(mel)
    
    yield audio  # First packet: ~150ms
    
    # Stream remaining
    for text_chunk in text_stream:
        tokens = generate_speech_tokens(
            text_chunk,
            audio_context,
            lm_model,
            streaming=True
        )
        
        mel = flow_model.generate_chunk(tokens)
        audio = vocoder.generate(mel)
        
        yield audio
```

### Agentic System Relevance

| Component | Swarm Scale Relevance |
|-----------|----------------------|
| FSQ Tokenization | Efficient audio encoding for agent communication |
| Streaming Synthesis | Real-time voice for agent interaction |
| Unified LM | Single model handles all TTS modes |
| Speaker Cloning | Agents can adopt consistent voices |

---

## [PAPER_NAME]
- Bounds
- Constraints
