# A Safe and Fast Repulsion Method for GPU-based Cloth Self Collisions

**Authors:** Longhua Wu, Botao Wu, Yin Yang, Huamin Wang (Ohio State, Frilly Inc., Clemson)

**Venue:** ACM Transactions on Graphics (SIGGRAPH 2020)

---

## Abstract

GPU-based cloth simulation achieving **38-72 FPS** with large time steps (Δt=1/100s) on complex garments (56K vertices, 112K triangles). Key innovations:

1. **Safe repulsion method**: Mathematically proven to prevent self-intersections
2. **Two-phase constraint enforcement**: Fast soft phase + guaranteed-safe hard phase
3. **Splitting method**: Decouples dynamics solver from collision handling
4. **Adaptive remeshing**: Maintains bounded edge lengths for constraint validity

**Core Insight**: Convert continuous-time collision constraints into discrete vertex distance + edge length + displacement constraints that can be enforced efficiently on GPU

## 1. Introduction

**Problem**: Existing GPU cloth simulators using vertex repulsion are unsafe — vertices can penetrate through triangles without getting close to any triangle vertex.

**Challenge**: Large time steps (needed for performance) cause large vertex displacements, breaking collision detection assumptions.

**Solution**: 
- Derive necessary distance conditions for self-intersections
- Convert to sufficient constraints for intersection-free states
- Two-phase enforcement: soft (fast) + hard (safe)
- Splitting method to integrate with any dynamics solver

## 2. Distance Conditions for Self Intersections

### 2.1 Vertex-Triangle Intersection

**Setup**: Vertex xᵢ potentially intersecting triangle with corners xⱼ, xₖ, xₗ

**Distance Metric**:
```
D(xᵢ, xⱼxₖxₗ) = min(‖xᵢⱼ‖, ‖xᵢₖ‖, ‖xᵢₗ‖)
```
where xᵢⱼ = xᵢ - xⱼ

**Upper Bound** (when vertex is inside triangle):
```
D(xᵢ, xⱼxₖxₗ) ≤ Bᵢ,ⱼₖₗ = {
    rⱼₖₗ (circumradius),           if triangle is acute
    max(‖xⱼₖ‖, ‖xₖₗ‖, ‖xₗⱼ‖)/2,   otherwise
}
```

**Circumradius formula**:
```
rⱼₖₗ = (‖xⱼₖ‖·‖xₖₗ‖·‖xₗⱼ‖) / √(lⱼₖₗ(lⱼₖₗ-2‖xⱼₖ‖)(lⱼₖₗ-2‖xₖₗ‖)(lⱼₖₗ-2‖xₗⱼ‖))
```
where lⱼₖₗ = ‖xⱼₖ‖ + ‖xₖₗ‖ + ‖xₗⱼ‖

**Key Property**: Bᵢ,ⱼₖₗ is monotonically increasing with edge lengths

### 2.2 Edge-Edge Intersection

**Setup**: Two edges xᵢxⱼ and xₖxₗ potentially intersecting

**Distance Metric**:
```
D(xᵢxⱼ, xₖxₗ) = min(‖xᵢₖ‖, ‖xᵢₗ‖, ‖xⱼₖ‖, ‖xⱼₗ‖)
```

**Upper Bound** (maximized when edges intersect perpendicularly at midpoints):
```
Bᵢⱼ,ₖₗ = ½√(‖xᵢⱼ‖² + ‖xₖₗ‖²)
```

**Global Bound**: Given constant edge length bound L:
```
B = max(Bᵢ,ⱼₖₗ, Bᵢⱼ,ₖₗ) = max(L/√3, L/√2) = L/√2
```

This B is the **minimum distance** required between any two non-adjacent vertices to guarantee intersection-free state

## 3. Constraint Formulation

### 3.1 Continuous vs Discrete Constraints

**Continuous Constraints** (must hold for all t ∈ [0,1]):
```
‖xᵢⱼ(t)‖² ≤ L²,     if {i,j} is an edge
‖xᵢⱼ(t)‖² ≥ B²,     otherwise
```
where x(t) = (1-t)x[k] + t·x[k+1] (linear interpolation)

**Problem**: Continuous constraints are hard to enforce directly

**Solution**: Convert to discrete constraints at each update x[k+1]

---

#### Algorithm 1: Continuous to Discrete Constraint Conversion

**For edges** (simple — convexity holds):
```
‖x[k]ᵢⱼ‖² ≤ L² ∧ ‖x[k+1]ᵢⱼ‖² ≤ L²  ⟹  ‖xᵢⱼ(t)‖² ≤ L² for all t
```

**For non-adjacent vertices** (needs displacement bound):

Given: t* minimizes ‖xᵢⱼ(t)‖²

We have:
```
‖xᵢⱼ(t)‖² ≥ min(‖x[k+1]ᵢⱼ‖², ‖x[k]ᵢⱼ‖²) - ¼‖x[k+1]ᵢⱼ - x[k]ᵢⱼ‖²
```

**Tightened discrete constraint**:
```
‖x[k]ᵢⱼ‖², ‖x[k+1]ᵢⱼ‖² ≥ (B + Bₜᵢₘₕₜ)²
```

**Displacement constraint**:
```
‖x[k+1]ᵢ - x[k]ᵢ‖² ≤ (B + Bₜᵢₘₕₜ)² - B²
```

**Combined guarantee**: Satisfying discrete + displacement constraints ensures continuous constraints

### 3.2 Vertex Displacement Constraints

**Key Insight**: Don't enforce displacement constraints explicitly — they slow down vertex movement.

**Instead**: Use small initial displacement to make soft phase successful most of the time.

**Theoretical role of displacement constraints**:
1. Justify small initial displacement assumption
2. Guarantee safe termination of hard phase via step size control

## 4. Constraint Enforcement

### 4.1 Soft Phase

**Goal**: Project xᵢₙᵢₜ onto feasible region c(x) ≥ 0

---

#### Algorithm 2: Soft Phase Constraint Enforcement

```python
def soft_phase(x_init, x_prev, constraints, I_soft=10, rho=1e6, epsilon_slack=1e-4):
    """
    Fast projection to feasible region via gradient descent.
    
    Returns: (x_new, success)
    """
    x = x_init.copy()
    
    for iteration in range(I_soft):
        # Compute penalty gradient
        grad = 2 * (x - x_init)  # Proximity term
        
        for (i, j) in constraints:
            c_ij = constraint_value(x, i, j)
            if c_ij < epsilon_slack:
                # Active constraint — add penalty gradient
                grad += -rho * constraint_gradient(x, i, j)
        
        # Gradient descent step
        x = x - step_size * grad
    
    # Check both continuous and discrete constraints
    success = check_discrete_constraints(x) and \
              check_continuous_constraints(x_prev, x)
    
    return x, success

def constraint_value(x, i, j):
    """
    Edge constraint: L² - ‖xᵢⱼ‖² ≥ 0
    Distance constraint: ‖xᵢⱼ‖² - (B + Bₜᵢₘₕₜ)² ≥ 0
    """
    dist_sq = np.sum((x[i] - x[j])**2)
    if is_edge(i, j):
        return L**2 - dist_sq
    else:
        return dist_sq - (B + B_tight)**2
```

**Failure Modes**:
1. Local minimum (rare in practice)
2. Discrete satisfied but continuous violated (addressed by small displacement)
3. Insufficient iterations (also addressed by small displacement)

### 4.2 Hard Phase

**Goal**: Guaranteed safe termination with bounded computational time

**Method**: Interior point with log barriers

---

#### Algorithm 3: Hard Phase (Interior Point)

```python
def hard_phase(x_init, x_prev, constraints, mu=1e-3, epsilon_slack=1e-4):
    """
    Interior point method with log barriers.
    
    Key property: Every iterate x[l] is acceptable — can terminate at any point.
    """
    x = x_prev.copy()  # Start from last safe state
    target = x_init
    
    while True:
        # Compute objective: proximity + log barriers
        objective = np.sum((x - target)**2)
        grad = 2 * (x - target)
        
        for (i, j) in constraints:
            c_ij = constraint_value(x, i, j)
            f_ij = smooth_log_barrier(c_ij, epsilon_slack)
            
            objective -= mu * np.log(f_ij)
            grad -= mu * barrier_gradient(x, i, j, c_ij, epsilon_slack)
        
        # Line search with safe step size
        alpha = compute_safe_step_size(x, grad, x_prev)
        x_new = x - alpha * grad
        
        # Check termination
        if check_all_constraints(x_prev, x_new):
            return x_new
        
        # Accept step (guaranteed safe by step size selection)
        x = x_new

def smooth_log_barrier(c, epsilon):
    """
    Piecewise C1-continuous barrier function.
    
    f(c, ε) = {
        c,                              if c ≤ 0
        a₃c³ + a₂c² + a₁c + a₀,        if 0 < c ≤ ε
        ε,                              if ε ≤ c
    }
    """
    if c <= 0:
        return c
    elif c <= epsilon:
        # Cubic interpolation for C1 continuity
        return cubic_interp(c, epsilon)
    else:
        return epsilon

def compute_safe_step_size(x, direction, x_prev):
    """
    Find step size α such that:
    1. All discrete constraints satisfied at x - α·direction
    2. All continuous constraints satisfied between x_prev and x - α·direction
    
    Uses bisection or analytical bounds.
    """
    alpha = 1.0
    while True:
        x_test = x - alpha * direction
        if check_discrete_constraints(x_test) and \
           check_continuous_constraints(x_prev, x_test):
            return alpha
        alpha *= 0.5
```

**Key Safety Guarantee**: Every iterate is acceptable — can terminate at any x[l]

## 5. Dynamics-Collision Integration (Splitting Method)

**Problem**: Modern cloth solvers need large time steps, but collision handling needs small displacements

**Solution**: Treat dynamics and collision as independent yet coupled processes

---

#### Algorithm 4: Splitting Method

```python
class ClothSimulator:
    def __init__(self):
        self.x_dynamics = initial_positions()  # Dynamics state
        self.x_collision = initial_positions()  # Collision state
        self.x_display = initial_positions()    # Display state
    
    def step(self, dt):
        # Dynamics solver runs freely (large time step OK)
        x_target = self.dynamics_solve(self.x_dynamics, dt)
        
        # Collision handling tries to catch up
        x_safe = self.collision_handle(self.x_collision, x_target)
        
        # Couple the two states
        self.x_dynamics = self.couple_states(x_target, x_safe)
        self.x_collision = x_safe
        
        # Display shows collision-handled result
        self.x_display = x_safe
    
    def collision_handle(self, x_prev, x_target):
        """
        Multiple collision steps to approach x_target while staying safe.
        """
        x_current = x_prev
        
        for collision_step in range(max_collision_steps):
            # Compute direction toward target
            direction = x_target - x_current
            
            # Limit displacement per collision step
            displacement = min(norm(direction), max_step_displacement)
            x_init = x_current + displacement * normalize(direction)
            
            # Two-phase enforcement
            x_new, success = soft_phase(x_init, x_current, constraints)
            if not success:
                x_new = hard_phase(x_init, x_current, constraints)
            
            x_current = x_new
            
            # Check if close enough to target
            if norm(x_current - x_target) < tolerance:
                break
        
        return x_current
    
    def couple_states(self, x_dynamics, x_collision):
        """
        Bring dynamics state toward collision state.
        
        Options:
        1. Direct copy: x_dynamics = x_collision
        2. Soft coupling: x_dynamics += α(x_collision - x_dynamics)
        3. Constraint-based: project x_dynamics onto collision constraints
        """
        # Option 2: Soft coupling (prevents jarring corrections)
        alpha = 0.5
        return x_dynamics + alpha * (x_collision - x_dynamics)
```

**Benefits**:
1. Dynamics solver unaware of collision handling
2. Can swap dynamics solvers freely
3. Collision handling at its own pace
4. Large time steps for dynamics, small steps for collision

## 6. Adaptive Remeshing

**Problem**: Analysis assumes all edges shorter than bound L. Overly stretched triangles violate this.

**Solution**: Adaptive edge splitting/merging to maintain uniform edge lengths

---

#### Algorithm 5: GPU-Friendly Adaptive Remeshing

```python
def adaptive_remesh(mesh, L_max, L_min):
    """
    Maintain edge lengths in [L_min, L_max] for constraint validity.
    
    GPU-parallel: Each edge processed independently.
    """
    # Phase 1: Mark edges for splitting/merging
    split_edges = []
    merge_edges = []
    
    for edge in mesh.edges:  # Parallel
        length = edge_length(edge)
        if length > L_max:
            split_edges.append(edge)
        elif length < L_min and can_merge(edge):
            merge_edges.append(edge)
    
    # Phase 2: Resolve conflicts (some edges share vertices)
    split_edges = resolve_conflicts(split_edges)
    merge_edges = resolve_conflicts(merge_edges)
    
    # Phase 3: Apply operations
    for edge in split_edges:  # Parallel (with conflict resolution)
        split_edge(mesh, edge)
    
    for edge in merge_edges:  # Parallel (with conflict resolution)
        merge_edge(mesh, edge)
    
    return mesh

def split_edge(mesh, edge):
    """
    Insert vertex at edge midpoint.
    
    v0 -------- v1    becomes    v0 ---- v_new ---- v1
    """
    v0, v1 = edge.vertices
    v_new = (mesh.positions[v0] + mesh.positions[v1]) / 2
    
    # Update topology
    mesh.add_vertex(v_new)
    mesh.split_triangles_at_edge(edge, v_new)

def merge_edge(mesh, edge):
    """
    Collapse edge to single vertex.
    
    v0 ---- v1    becomes    v_merged
    """
    v0, v1 = edge.vertices
    v_merged = (mesh.positions[v0] + mesh.positions[v1]) / 2
    
    # Update topology
    mesh.collapse_edge(edge, v_merged)
```

**Key for GPU**: Process edges in batches with conflict-free coloring

## 7. Hydrogen Integration Notes

### Relevance to Geometry Pillar

**Bounded Edge Lengths → Bounded Types**:
```purescript
-- Edge length constraint maps to bounded numeric type
type EdgeLength = BoundedFloat 0.0 L_MAX

-- Distance constraint
type VertexDistance = BoundedFloat B_MIN INFINITY
```

### Relevance to Material Pillar

**Cloth Material Properties**:
- Stretch resistance → edge length constraints
- Collision thickness → B_tight parameter
- Bending stiffness → affects dynamics, not collision

### Relevance to WebGPU Runtime

**GPU Parallelization Patterns**:
1. **Spatial hashing** for collision culling
2. **Parallel constraint evaluation** (each vertex independent)
3. **Conflict-free coloring** for topology changes

### Key Algorithms for Implementation

| Algorithm | Purpose | Parallelizable |
|-----------|---------|----------------|
| Distance bounds | Intersection detection | Yes (per vertex pair) |
| Soft phase | Fast projection | Yes (gradient descent) |
| Hard phase | Safe fallback | Limited (sequential line search) |
| Splitting | State coupling | N/A (structural) |
| Remeshing | Edge length bounds | Yes (with coloring) |

### Constraint System Design Pattern

```purescript
-- Hydrogen could model this constraint system
data CollisionConstraint
  = EdgeLength EdgeIdx (BoundedFloat 0 L)
  | VertexDistance VertexIdx VertexIdx (BoundedFloat B Infinity)
  | Displacement VertexIdx (BoundedFloat 0 MaxStep)

-- Constraint satisfaction check
satisfies :: State -> CollisionConstraint -> Boolean

-- Two-phase enforcement
enforce :: Array CollisionConstraint -> State -> State -> State
enforce constraints x_prev x_init =
  let soft_result = softPhase constraints x_prev x_init
  in if satisfies soft_result constraints
     then soft_result
     else hardPhase constraints x_prev x_init
```

## Appendix: Key Algorithms

### Complete Two-Phase Collision Handler

```python
class GPUClothCollisionHandler:
    """
    Complete collision handling system combining all algorithms.
    """
    def __init__(self, config):
        self.L = config.max_edge_length      # Edge length bound
        self.B = self.L / np.sqrt(2)          # Minimum vertex distance
        self.B_tight = config.tightening      # Safety margin
        self.I_soft = config.soft_iterations  # Soft phase iterations
        self.rho = config.penalty_strength    # Penalty constant
        self.mu = config.barrier_strength     # Log barrier constant
        self.epsilon_slack = config.slack     # Slack for barriers
    
    def handle_collisions(self, x_prev, x_init):
        """
        Main entry point: two-phase collision handling.
        """
        # Phase 1: Soft phase (fast, usually succeeds)
        x_soft, success = self.soft_phase(x_prev, x_init)
        
        if success:
            return x_soft
        
        # Phase 2: Hard phase (safe, guaranteed termination)
        return self.hard_phase(x_prev, x_init)
    
    def soft_phase(self, x_prev, x_init):
        """
        Gradient descent projection to feasible region.
        """
        x = x_init.copy()
        
        for _ in range(self.I_soft):
            grad = self.compute_soft_gradient(x, x_init)
            x = x - self.compute_step_size(grad) * grad
        
        success = (self.check_discrete(x) and 
                   self.check_continuous(x_prev, x))
        return x, success
    
    def hard_phase(self, x_prev, x_init):
        """
        Interior point with guaranteed safe iterates.
        """
        x = x_prev.copy()
        
        while not self.converged(x, x_init):
            grad = self.compute_hard_gradient(x, x_init)
            alpha = self.safe_step_size(x, grad, x_prev)
            x = x - alpha * grad
            
            # Update x_prev for next continuous constraint check
            if self.check_discrete(x):
                x_prev = x
        
        return x
    
    def compute_soft_gradient(self, x, x_init):
        """
        Gradient of soft phase objective:
        ‖x - x_init‖² - ρ Σ min(c_ij(x) - ε_slack, 0)
        """
        grad = 2 * (x - x_init)
        
        for (i, j, is_edge) in self.constraint_pairs:
            c = self.constraint_value(x, i, j, is_edge)
            if c < self.epsilon_slack:
                grad[i] -= self.rho * self.constraint_grad_i(x, i, j, is_edge)
                grad[j] -= self.rho * self.constraint_grad_j(x, i, j, is_edge)
        
        return grad
    
    def compute_hard_gradient(self, x, x_init):
        """
        Gradient of hard phase objective:
        ‖x - x_init‖² - μ Σ log(f(c_ij(x), ε_slack))
        """
        grad = 2 * (x - x_init)
        
        for (i, j, is_edge) in self.constraint_pairs:
            c = self.constraint_value(x, i, j, is_edge)
            f = self.smooth_barrier(c)
            
            if f > 0:
                grad[i] -= self.mu / f * self.barrier_grad_i(x, i, j, is_edge, c)
                grad[j] -= self.mu / f * self.barrier_grad_j(x, i, j, is_edge, c)
        
        return grad
    
    def constraint_value(self, x, i, j, is_edge):
        """
        c_ij(x) for edges: L² - ‖x_ij‖²
        c_ij(x) for non-edges: ‖x_ij‖² - (B + B_tight)²
        """
        dist_sq = np.sum((x[i] - x[j])**2)
        if is_edge:
            return self.L**2 - dist_sq
        else:
            return dist_sq - (self.B + self.B_tight)**2
    
    def check_discrete(self, x):
        """
        Check all discrete constraints at state x.
        """
        for (i, j, is_edge) in self.constraint_pairs:
            if self.constraint_value(x, i, j, is_edge) < 0:
                return False
        return True
    
    def check_continuous(self, x0, x1):
        """
        Check continuous constraints along linear path from x0 to x1.
        
        For edges: convexity guarantees satisfaction
        For non-edges: check minimum distance along path
        """
        for (i, j, is_edge) in self.constraint_pairs:
            if is_edge:
                continue  # Convexity handles this
            
            # Find t* that minimizes ‖x_ij(t)‖²
            x_ij_0 = x0[i] - x0[j]
            x_ij_1 = x1[i] - x1[j]
            delta = x_ij_1 - x_ij_0
            
            # t* = -dot(x_ij_0, delta) / ‖delta‖²
            denom = np.sum(delta**2)
            if denom > 1e-10:
                t_star = -np.dot(x_ij_0, delta) / denom
                t_star = np.clip(t_star, 0, 1)
            else:
                t_star = 0
            
            x_ij_t = (1 - t_star) * x_ij_0 + t_star * x_ij_1
            if np.sum(x_ij_t**2) < self.B**2:
                return False
        
        return True
    
    def safe_step_size(self, x, grad, x_prev):
        """
        Find largest α such that x - α·grad satisfies all constraints.
        Uses bisection starting from α = 1.
        """
        alpha = 1.0
        for _ in range(20):  # Max bisection iterations
            x_test = x - alpha * grad
            if (self.check_discrete(x_test) and 
                self.check_continuous(x_prev, x_test)):
                return alpha
            alpha *= 0.5
        return alpha
    
    def smooth_barrier(self, c):
        """
        C1-continuous barrier function.
        """
        if c <= 0:
            return c
        elif c <= self.epsilon_slack:
            # Cubic interpolation
            t = c / self.epsilon_slack
            return self.epsilon_slack * (3*t**2 - 2*t**3)
        else:
            return self.epsilon_slack
```

---

**Document Status**: COMPLETE
**Synthesis Date**: 2026-02-26
**Synthesized By**: Opus 4.5

