# A Stream Function Solver for Liquid Simulations

────────────────────────────────────────────────────────────────────────────────

**Source**: vecpotential.pdf
**Authors**: Ryoichi Ando (IST Austria), Nils Thuerey (TU Munich), Chris Wojtan (IST Austria)
**Published**: ACM SIGGRAPH / Eurographics Symposium on Computer Animation
**Synthesized**: 2026-02-26 by Opus

────────────────────────────────────────────────────────────────────────────────

## Executive Summary

This paper replaces the traditional pressure projection in liquid simulation with a
**stream function solve**. Instead of finding pressure p that makes velocity divergence-free,
directly solve for a vector potential Ψ where velocity u = ∇×Ψ (curl of Ψ).

**Key Benefits**:

1. **Guaranteed divergence-free**: The curl of any vector field is always divergence-free
   by construction (∇·(∇×Ψ) = 0), regardless of solve accuracy

2. **Free two-phase simulation**: Air phase is automatically divergence-free without
   computing it — enables realistic bubbles by simulating only the liquid

3. **Robust at extreme density ratios**: Method becomes MORE stable (not less) when
   Atwood ratio approaches 1 (ρ_air → 0)

4. **Natural rigid body coupling**: Two-way solid-fluid interaction via stream function
   constraints

**Trade-off**: 3× more unknowns (vector vs scalar), ~3× slower per timestep, but enables
phenomena impossible with standard pressure projection (bubbles, trapped air, glugging)

────────────────────────────────────────────────────────────────────────────────

## 1. The Problem with Pressure Projection

### Standard Navier-Stokes Approach

The incompressible Navier-Stokes equations:

```
Du/Dt = -(1/ρ)∇p + g     (momentum)
∇·u = 0                   (incompressibility)
```

Traditionally, incompressibility is enforced by finding pressure p that projects
velocity into divergence-free state via Poisson equation:

```
∇·((Δt/ρ)∇p) = ∇·u*
```

where u* is velocity after advection.

### Problems with Pressure Projection

1. **Approximate incompressibility**: Iterative solvers only satisfy ∇·u = 0 up to
   tolerance. Volume drifts over time.

2. **Free surface approximation**: Setting p = 0 at liquid surface assumes air has
   negligible momentum. Air is NOT divergence-free, causing:
   - Collapsing bubbles (air compresses unrealistically)
   - No proper glugging/gurgling when liquid exits containers
   - Missing air-liquid coupling effects

3. **Two-phase simulation is expensive**: Simulating both phases requires:
   - Delicate interface treatment
   - Memory/compute for "unimportant" air domain
   - Instability with large density ratios (1000:1 water:air)

────────────────────────────────────────────────────────────────────────────────

## 2. Stream Functions and Vector Potentials

### Helmholtz-Hodge Decomposition

Any vector field decomposes into three parts:

```
u* = ∇Θ + ∇×Ψ + γ
     │      │     └─ harmonic (neither curl nor gradient)
     │      └─────── curl of vector field (divergence-free)
     └────────────── gradient of scalar (irrotational)
```

Removing the gradient component gives divergence-free velocity: **u = ∇×Ψ + γ**

Instead of subtracting ∇Θ from u*, solve directly for Ψ to get u.

### Why This Works

The curl of any vector field is divergence-free by identity:

```
∇·(∇×Ψ) = 0    (always, for any Ψ)
```

This is not an approximation — it's a mathematical identity. The resulting velocity
is **exactly** divergence-free regardless of numerical precision.

### Stream Function vs Vorticity

Both are vector quantities, but different:

```
Vorticity:        ω = ∇×u     (curl OF velocity)
Stream function:  u = ∇×Ψ     (velocity FROM curl)
```

Stream function doesn't have obvious physical meaning, but vorticity and stream
function are related: ω = ∇×(∇×Ψ) = -∇²Ψ (for divergence-free Ψ)

────────────────────────────────────────────────────────────────────────────────

## 3. The Linear System

### Derivation

Starting from the kinetic energy minimization perspective:

```
minimize_Ψ ∫_Ω (1/2)ρ||u* - ∇×Ψ||² dV
```

Find the divergence-free velocity closest to u* in weighted least squares sense.

Taking gradient w.r.t. Ψ and setting to zero:

```
∇×(ρ∇×Ψ) = ∇×(ρu*)
```

### The Null Space Problem

The curl operator has a non-trivial null space: ∇×(Ψ + ∇φ) = ∇×Ψ for any scalar φ.
Infinite solutions exist! Fix by requiring ∇·Ψ = 0, adding regularizer:

```
minimize_Ψ ∫_Ω (1/2)ρ||u* - ∇×Ψ||² dV + (1/2)ρ(∇·Ψ)² dV
```

### Discrete Form

Discretizing curl [∇×] and divergence [∇·] as matrices:

```
([∇×]ᵀ[ρ][V][∇×] + [∇·]ᵀ[ρ][V][∇·])[Ψ] = [∇×]ᵀ[ρ][V][u*]
```

Using the identity [∇×]ᵀ[∇×] + [∇·]ᵀ[∇·] = [∇²] (vector Laplacian):

```
([∇²] + [∇×]ᵀ[Δρ][∇×] + [∇·]ᵀ[Δρ][∇·])[Ψ] = [∇×]ᵀ[ρ][u*]
```

where [Δρ] = [ρ] - [I] (deviation from liquid density).

### The Magic: Air Disappears

If ρ_air = 0, then [Δρ] = -1 in air. The linear system entries **vanish** outside
the liquid! The system reduces to:

- Standard vector Laplacian inside liquid
- [Δρ] terms only in narrow band near surface
- Air automatically divergence-free for any Ψ

────────────────────────────────────────────────────────────────────────────────

## 4. Boundary Conditions

### Liquid-Air Interface (Automatic!)

No special treatment needed. Setting ρ = 0 in air automatically incorporates the
correct boundary condition. Surface tension can be added as force σH to u* at
interface (mean curvature normal).

**Key insight**: Unlike most methods that become unstable as Atwood ratio → 1,
this method becomes MORE stable and simpler.

### Static Solid Boundaries

To ensure u = 0 at solid boundary, set Ψ = ∇φ̂ where φ̂ is a scalar on solid surface.
Then ∇×Ψ = ∇×(∇φ̂) = 0 by identity.

Fractional weighting handles partial cell occupation (ghost-fluid style).

### Rigid Body Coupling (Two-Way)

For rigid body with center x_c, translational velocity u_c, angular velocity ω:

```
Rigid body velocity: ŭ = ω × x_rel + u_c    (where x_rel = x - x_c)
```

Find stream function satisfying ∇×Ψ̆ = ŭ:

```
Ψ̆ = -½ diag([y²+z², z²+x², x²+y²])·ω + [0 z 0; 0 0 x; y 0 0]·u_c + ∇φ̂
```

Replace DOFs inside solid with φ̂, ω, u_c. The solve returns updated ω and u_c
for integrating rigid body dynamics — monolithically coupled, not weakly iterated.

────────────────────────────────────────────────────────────────────────────────

## 5. Implementation

### Grid Layout (Discrete Exterior Calculus)

```
Vertices:  scalar field φ̂ (0-forms)
Edges:     stream function Ψ components (1-forms)  
Faces:     velocity u components (2-forms / fluxes)
```

Consistent with DEC: curl maps edges→faces, divergence maps edges→vertices.

### Matrix Structure

**[P]**: Static solid boundary term (precomputable)
```
[P] = [Z]ᵀ[∇×]ᵀ[1/A][∇×][Z] + [Z]ᵀ[∇·]ᵀ[1/A][∇·][Z]
```
where [Z] maps liquid regions to Ψ̂ and solid regions to ∇φ̂, [A] = liquid area fraction

**[Q]**: Dynamic density jump term (recompute each timestep)
```
[Q] = [Z]ᵀ[∇×]ᵀ[Δρ/A][∇×][Z] + [Z]ᵀ[∇·]ᵀ[Δρ/A][∇·][Z]
```
Non-zero only in narrow band near liquid-air interface.

**[K]** = [P] + [Q]: Combined system matrix

### Tolerating Convergence Errors

Solve for **change** from previous timestep, not absolute value:

```
[Ψ] = [Z][ΔΨ̂; Δφ̂] + [Ψ_{t-Δt}]
```

Benefits:
- No spurious damping from early termination
- Still divergence-free by construction
- Converges faster (solving for small delta)

### Final Linear System

```
[K][ΔΨ̂; Δφ̂] = [B][ρ][u*] - [K][Ψ̂_{t-Δt}; φ̂_{t-Δt}]
```

Solve with PCG (MIC(0) preconditioner, τ=0.97, σ=1.0, tolerance 10⁻⁴).

────────────────────────────────────────────────────────────────────────────────

## 6. Implementable Algorithms

### Algorithm 1: Stream Function Projection (Main Loop)

```python
def stream_function_projection(u_star, fluid_levelset, solid_levelset, 
                                prev_psi, prev_phi):
    """
    Replace pressure projection with stream function solve.
    
    Args:
        u_star: velocity after advection (on faces)
        fluid_levelset: signed distance to liquid surface
        solid_levelset: signed distance to solid surface
        prev_psi: stream function from previous timestep
        prev_phi: solid scalar from previous timestep
    
    Returns:
        u: divergence-free velocity field
    """
    # First call: precompute static matrices
    if first_time:
        Z = compute_solid_mapping(solid_levelset)
        P = compute_solid_boundary_matrix(Z, solid_levelset)
        B = Z.T @ curl_matrix.T
        prev_psi, prev_phi = zeros(), zeros()
    
    # Compute density matrices from fluid levelset
    rho = compute_volume_fractions(fluid_levelset)  # 1 in liquid, 0 in air
    delta_rho = rho - identity_matrix
    
    # Compute dynamic density jump matrix
    Q = compute_density_jump_matrix(Z, delta_rho)
    
    # Combined system matrix
    K = P + Q
    
    # Right-hand side
    rhs = B @ (rho @ u_star) - K @ concatenate(prev_psi, prev_phi)
    
    # Solve for delta
    delta = pcg_solve(K, rhs, tolerance=1e-4)
    delta_psi, delta_phi = split(delta)
    
    # Update stream function
    new_psi = delta_psi + prev_psi
    new_phi = delta_phi + prev_phi
    
    # Compute divergence-free velocity
    u = curl_matrix @ Z @ concatenate(new_psi, new_phi)
    
    return u, new_psi, new_phi
```

### Algorithm 2: Curl Operator (Edges → Faces)

```python
def build_curl_matrix(grid):
    """
    Build discrete curl operator mapping edge values to face values.
    
    For a face with normal in y-direction:
        (∇×Ψ)_y = ∂Ψ_x/∂z - ∂Ψ_z/∂x
    
    Stencil: difference of Ψ values on edges surrounding the face.
    """
    curl = sparse_matrix(num_faces, num_edges)
    
    for face in grid.faces:
        # Get the 4 edges surrounding this face
        edges = face.surrounding_edges()
        
        # Curl is sum of edge values with orientation signs
        for edge, sign in edges:
            curl[face.id, edge.id] = sign / grid.cell_size
    
    return curl
```

### Algorithm 3: Rigid Body Stream Function

```python
def rigid_body_stream_function(x, x_center, omega, u_center):
    """
    Compute stream function Ψ such that ∇×Ψ = rigid body velocity.
    
    Args:
        x: position in world space
        x_center: rigid body center of mass
        omega: angular velocity (3-vector)
        u_center: translational velocity (3-vector)
    
    Returns:
        psi: stream function value at x
    """
    x_rel = x - x_center
    
    # Rotation contribution
    # Ψ_rot = -½ diag([y²+z², z²+x², x²+y²]) · ω
    psi_rot = -0.5 * array([
        (x_rel.y**2 + x_rel.z**2) * omega.x,
        (x_rel.z**2 + x_rel.x**2) * omega.y,
        (x_rel.x**2 + x_rel.y**2) * omega.z
    ])
    
    # Translation contribution
    # Ψ_trans = [0 z 0; 0 0 x; y 0 0] · u_c
    psi_trans = array([
        x_rel.z * u_center.y,
        x_rel.x * u_center.z,
        x_rel.y * u_center.x
    ])
    
    return psi_rot + psi_trans  # plus ∇φ̂ from solve
```

### Algorithm 4: Volume Fraction Computation

```python
def compute_volume_fractions(fluid_levelset, grid):
    """
    Compute liquid volume fraction per cell for density matrix.
    
    Uses ghost-fluid style: fraction based on signed distance
    along line between cell centers.
    """
    rho = diagonal_matrix(grid.num_cells)
    
    for cell in grid.cells:
        phi_center = fluid_levelset.sample(cell.center)
        
        if phi_center < 0:  # Inside liquid
            fraction = 1.0
        elif phi_center > cell.diagonal:  # Far outside
            fraction = 0.0
        else:  # Near interface
            # Compute fraction via interface crossing
            fraction = compute_liquid_fraction(cell, fluid_levelset)
        
        # Clamp small fractions to avoid division issues
        if fraction < 0.01:
            fraction = 0.0
        
        rho[cell.id, cell.id] = fraction
    
    return rho
```

────────────────────────────────────────────────────────────────────────────────

## 7. Hydrogen/PureScript Relevance

### Direct Applications

**LATTICE Motion Graphics** — Fluid simulations for video:
- Liquid logos, flowing text effects
- Two-phase bubble effects without simulating air
- "Guaranteed correct" divergence-free velocity for archival quality

**Hydrogen.Target.Canvas/WebGL** — Real-time fluid elements:
- Interactive liquid UI elements (buttons, sliders that "pour")
- Background fluid animations
- Particle systems advected by stream function velocity

### Schema Implications

The paper's mathematical structure suggests types:

```purescript
-- Stream function is a 3D vector field
newtype StreamFunction = StreamFunction 
  { components :: Array3D (Vec3 Number) }

-- Velocity derived from stream function is guaranteed divergence-free
newtype DivergenceFreeVelocity = DivergenceFreeVelocity
  { field :: Array3D (Vec3 Number) 
  , proof :: DivergenceFreeProof  -- curl-of-curl-is-zero
  }

-- The curl operation that guarantees divergence-free output
curl :: StreamFunction -> DivergenceFreeVelocity

-- Density field: 1 in liquid, 0 in air
newtype DensityField = DensityField
  { values :: Array3D UnitInterval }  -- bounded [0,1]
```

### Type-Level Guarantees

The paper's key insight maps perfectly to dependent types:

1. **Divergence-free by construction**: `curl :: StreamFunction -> DivergenceFreeVelocity`
   The return type PROVES the result is divergence-free — not checked, constructed.

2. **Bounded density**: Density in [0,1] via `UnitInterval` prevents the instabilities
   that plague traditional two-phase solvers.

3. **Error tolerance without drift**: The "solve for delta" approach means early
   termination doesn't accumulate error — compatible with iterative refinement
   in real-time contexts.

### Implementation Path for Hydrogen

1. **2D version first**: Stream functions in 2D are scalar (not vector), simpler
   to implement and still useful for UI effects

2. **WebGL shader generation**: The linear system is sparse, structured — amenable
   to GPU compute shaders

3. **Composable with SDF**: Stream function velocity can advect SDF surfaces,
   combining this paper with the SDF ray tracing work

### Why This Matters for Agents

At billion-agent scale, "approximately divergence-free" accumulates into visible
artifacts. A stream function approach provides:

- **Deterministic correctness**: Same input → exactly same divergence-free output
- **No volume drift**: Physical plausibility without correction passes
- **Graceful degradation**: Lower solve accuracy = less detail, not broken physics

────────────────────────────────────────────────────────────────────────────────

## References

- Ando, Thuerey, Wojtan (2015). "A Stream Function Solver for Liquid Simulations."
  SCA (Symposium on Computer Animation).

- Bridson (2008). "Fluid Simulation for Computer Graphics." AK Peters/CRC Press.
  (Standard time-splitting reference)

- Elcott et al. (2007). "Stable, circulation-preserving, simplicial fluids." ACM TOG.
  (DEC discretization, smoke stream functions)

- Boyd & Bridson (2012). "MultiFLIP for energetic two-phase fluid simulation." ACM TOG.
  (Two-phase FLIP comparison baseline)

- Carlson, Mucha, Turk (2004). "Rigid fluid: Animating interplay between rigid bodies
  and fluid." SIGGRAPH. (Rigid-fluid coupling)

- Batty et al. (2007). "A fast variational framework for accurate solid-fluid coupling."
  ACM TOG. (Kinetic energy minimization perspective)

- de Goes et al. (2013). "Digital geometry processing with discrete exterior calculus."
  SIGGRAPH Course. (DEC foundations)

────────────────────────────────────────────────────────────────────────────────
                                                                        — Opus
