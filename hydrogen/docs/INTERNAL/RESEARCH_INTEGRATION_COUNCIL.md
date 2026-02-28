# Research Integration Council

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // council // deliberation
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

This document synthesizes research papers analyzed by agents and identifies
concrete integration points for the Hydrogen codebase. Each paper is evaluated
for algorithms, techniques, and theoretical foundations that strengthen our
provably correct design system.

**Evaluation Criteria:**
- How does it help Hydrogen's core mission?
- Where in the codebase should it integrate?
- What is the implementation priority?
- What are the key algorithms to extract?

────────────────────────────────────────────────────────────────────────────────
                                                              // batch // 1
────────────────────────────────────────────────────────────────────────────────

## Batch 1: Type-Based Numerical Analysis & FP4 Quantization

### Paper 1.1: TYPE_BASED_ROUNDING_ERROR_DISSERTATION

**Source:** PhD Dissertation, Cornell University (Ariel Kellison, 2025)
**arXiv:** 2501.14598

#### Core Contribution

Two novel programming languages for rounding error analysis:

| Language | Error Type | Type Mechanism | Semantic Model |
|----------|------------|----------------|----------------|
| **NumFuzz** | Forward error | Graded monad `M[ε]` | Neighborhood monad on Met |
| **Bean** | Backward error | Graded comonad `D^r` | Backward error lenses (Bel) |

#### Key Insight

Programs using finite-precision arithmetic are:
- **Producers** of rounding error (effects → graded monads)
- **Consumers/amplifiers** of rounding errors (coeffects → graded comonads)

This maps directly to Hydrogen's architecture where:
- Schema atoms **produce** bounded values
- Compositions **propagate** bounds through transformations

#### Algorithms to Extract

**1. Graded Monad M[ε] for Forward Error:**
```lean
-- Forward error tracking
structure ForwardError (ε : ℝ) (α : Type) where
  ideal : α
  approx : α  
  bound : dist ideal approx ≤ ε
```

**2. Sensitivity Inference (Linear Time):**
```
Algorithm: Bottom-up inference
1. For each subterm, compute minimal required sensitivity
2. Combine using context operations (+, ·, max)
3. Compare against declared bounds via subtyping
Complexity: O(n) where n = |program|
```

**3. Backward Error Lens Composition:**
```
Given lenses (f₁, f̃₁, b₁) : X → Y and (f₂, f̃₂, b₂) : Y → Z:

f   = f₁ ; f₂                           -- compose forwards
f̃   = f̃₁ ; f̃₂                           -- compose approximations  
b   = (x, z) ↦ b₁(x, b₂(f̃₁(x), z))      -- chain backward maps
```

#### Integration Points

```
proofs/Hydrogen/Schema/Numeric/
  ├── GradedMonad.lean         -- M[ε] forward error monad
  ├── GradedComonad.lean       -- D^r backward error comonad
  ├── BackwardErrorLens.lean   -- Bel category for roundtrip proofs
  ├── Sensitivity.lean         -- !s comonad for sensitivity scaling
  └── Inference.lean           -- Linear-time bound inference

src/Hydrogen/Schema/Numeric/
  ├── Bounded.purs             -- Bounded types with error grades
  └── Roundtrip.purs           -- Serialization with proven bounds
```

#### Hydrogen Applications

| Hydrogen Need | NumFuzz/Bean Solution |
|---------------|----------------------|
| Bounded Schema atoms | Graded types encode error bounds |
| Serialization roundtrip | Backward error lenses prove bounds |
| GPU shader verification | Type-check WGSL numerical operations |
| Color space conversion | Proven sRGB ↔ Oklab error bounds |

#### Priority: ⭐⭐⭐⭐⭐ CRITICAL

This is the **theoretical foundation** for proving all bounded types correct.
Without this, our ℝ/ℕ types in Lean have no connection to actual FP computation.

────────────────────────────────────────────────────────────────────────────────

### Paper 1.2: BEAN_BACKWARD_ERROR

**Source:** Cornell University + Imperial College London (Kellison et al., 2025)
**arXiv:** 2501.14550

#### Core Contribution

First static analysis tool for **backward error analysis**. Provides concrete
typing rules for arithmetic primitives with proven backward error bounds.

#### Key Insight

Backward error bounds ARE compositional when variables are not duplicated with
conflicting error assignments. This motivates **strict linearity**.

At billion-agent scale:
- Each Element must produce deterministic output
- Duplicating state creates divergent error bounds
- Linear types prevent this by construction

#### Typing Rules to Extract

| Operation | Typing Rule | Backward Error |
|-----------|-------------|----------------|
| **add** | `x: ε+r₁, y: ε+r₂ ⊢ add x y : R` | ε to both operands |
| **sub** | `x: ε+r₁, y: ε+r₂ ⊢ sub x y : R` | ε to both operands |
| **mul** | `x: ε/2+r₁, y: ε/2+r₂ ⊢ mul x y : R` | ε/2 per operand |
| **div** | `x: ε/2+r₁, y: ε/2+r₂ ⊢ div x y : R` | ε/2 per operand |
| **dmul** | `z: discrete, x: ε+r ⊢ dmul z x : R` | ε to linear only |

Where ε = u/(1-u) ≈ 2^-53 for IEEE binary64.

#### Olver's Rounding Model

Bean uses Olver's model instead of standard:
```
Standard:  fl(x op y) = (x op y)(1 + δ),    |δ| ≤ u
Olver:     fl(x op y) = (x op y)e^δ,        |δ| ≤ ε = u/(1-u)
```

**Why Olver?** Better compositional properties for error propagation.

#### Dual Context Pattern

```
Φ, z: α | Γ, x: r σ ⊢ e: τ

Where:
- Φ: Discrete context (no backward error, can duplicate)
- Γ: Linear context (has backward error, use exactly once)
```

This maps to Hydrogen's Theme | State separation:
```purescript
renderElement : 
  Theme        -- Φ: configuration (reusable, no error)
  | State :ε   -- Γ: current values (linear, has error)
  ⊢ Element
```

#### Integration Points

```
proofs/Hydrogen/Schema/Numeric/
  ├── Primitives.lean          -- Typing rules for add/mul/div
  ├── OlverModel.lean          -- Exponential rounding model
  └── DualContext.lean         -- Discrete | Linear separation

src/Hydrogen/Schema/Numeric/
  ├── Add.purs                 -- Typed addition with error
  ├── Mul.purs                 -- Typed multiplication
  └── Discrete.purs            -- Discrete promotion (!x)
```

#### Example: Dot Product

```bean
DotProd2 x y :=
  let (x0, x1) = x in
  let (y0, y1) = y in
  let v = mul x0 y0 in
  let w = mul x1 y1 in
  add v w
```

**Typing:** `∅ | x: (3ε/2) R², y: (3ε/2) R² ⊢ DotProd2 : R`

Each input component has backward error bounded by 3ε/2.

#### Priority: ⭐⭐⭐⭐⭐ CRITICAL

Provides concrete typing rules for all numeric operations. Required for
implementing the graded type system in Hydrogen.

────────────────────────────────────────────────────────────────────────────────

### Paper 1.3: ROUNDING_ERROR_TYPES (Extended Synthesis)

**Source:** Synthesis of NumFuzz + Bean with detailed categorical semantics

#### Core Contribution (Beyond Papers 1.1-1.2)

Three additional constructs for complete error tracking:

**1. Neighborhood Monad:**
```
T^r(X) = { (x, y) ∈ X × X | d(x, y) ≤ r }
```
Elements are pairs of (ideal, approximate) values within distance r.

**2. Relative Precision Metric:**
```
RP(x, x̃) = |ln(x/x̃)|    if sign(x) = sign(x̃) and x, x̃ ≠ 0
         = 0            if x = x̃ = 0
         = ∞            otherwise
```

Unlike relative error, RP is a proper metric (symmetric, triangle inequality).

**3. Additive vs Multiplicative Products:**
```
Additive (&):      sensitivity = max(s₁, s₂)
Multiplicative (⊗): sensitivity = s₁ + s₂
```

#### Algorithms to Extract

**Neighborhood Monad Operations:**
```lean
-- Unit: exact computation
def pure (x : α) : T 0 α := ⟨x, x, rfl⟩

-- Multiplication: compose errors
def join : T q (T r α) → T (q + r) α
  | ⟨⟨x, y, _⟩, ⟨_, z, _⟩, _⟩ => ⟨x, z, by linarith⟩
```

**Distance on T^r:**
```lean
-- Distance only considers ideal components
def dist_T (a b : T r α) : ℝ := dist a.ideal b.ideal
```

#### Integration Points

```
proofs/Hydrogen/Schema/Numeric/
  ├── NeighborhoodMonad.lean   -- T^r monad definition + laws
  ├── RelativePrecision.lean   -- RP metric with proofs
  └── Composition.lean         -- & vs ⊗ products

src/Hydrogen/Schema/Numeric/
  ├── Approximate.purs         -- (ideal, rendered, bound) triples
  └── Compose.purs             -- Additive vs multiplicative
```

#### Hydrogen Applications

**Neighborhood Monad for Rendering:**
```purescript
type RenderResult r = 
  { ideal    :: Element   -- What the designer specified
  , rendered :: Element   -- What actually appears on screen
  , bound    :: r         -- Proven error bound
  }

render :: Element -> RenderResult ε_render
```

**Additive vs Multiplicative Composition:**
```purescript
-- Shared state (additive): sensitivity = max
overlay :: (Element & Element) -> Element  -- max(err1, err2)

-- Independent state (multiplicative): sensitivity = sum  
beside :: (Element ⊗ Element) -> Element   -- err1 + err2
```

#### Priority: ⭐⭐⭐⭐ HIGH

Completes the theoretical foundation with proper metric spaces and composition.

────────────────────────────────────────────────────────────────────────────────

### Paper 1.4: MICROSCALING_FP4_QUANTIZATION

**Source:** ISTA, Red Hat AI, ETH Zürich (Castro et al., 2025)
**arXiv:** 2509.23202

#### Core Contribution

First comprehensive study of MXFP4 and NVFP4 for post-training quantization.

| Format | Group Size | Element | Scale | Bits/Element |
|--------|-----------|---------|-------|--------------|
| **MXFP4** | 32 | E2M1 | E8M0 (power-of-2) | 4.25 |
| **NVFP4** | 16 | E2M1 | E4M3 (full FP8) | 4.5 |

#### Key Findings

1. **NVFP4's small group size** neutralizes traditional outlier mitigation
2. **MXFP4's power-of-two scales** induce accuracy degradation
3. **MR-GPTQ** with Hadamard transforms recovers accuracy

#### Algorithms to Extract

**1. Block-wise Hadamard Transform:**
```python
def hadamard_transform(x, block_size=32):
    """Transform Laplace distribution to Normal for better quantization"""
    H = hadamard_matrix(block_size) / sqrt(block_size)
    return block_diagonal_multiply(x, H)
```

**2. MSE-Optimal Scale Search:**
```python
def find_optimal_scale(values, format='NVFP4'):
    """Find scale minimizing reconstruction MSE"""
    # Grid search over candidate scales
    best_scale, best_mse = None, inf
    for scale in candidate_scales(format):
        quantized = quantize(values / scale)
        reconstructed = quantized * scale
        mse = mean_squared_error(values, reconstructed)
        if mse < best_mse:
            best_scale, best_mse = scale, mse
    return best_scale
```

**3. MR-GPTQ (FP4-optimized GPTQ):**
```
1. Apply block-wise Hadamard to weights
2. Reorder columns by activation magnitude
3. Quantize column-by-column with error compensation
4. Use MSE-optimal scales per group
```

#### Error Bounds

```
NVFP4 (G=16, no rotation):    MSE_rel ≈ 0.01  (1%)
MXFP4 (G=32, with Hadamard):  MSE_rel ≈ 0.02  (2%)
INT4 (G=32, GPTQ):            MSE_rel ≈ 0.01  (1%)
```

#### Integration Points

```
src/Hydrogen/GPU/Quantization/
  ├── FP4.purs               -- E2M1 format definition
  ├── MXFP4.purs             -- MXFP4 with E8M0 scales
  ├── NVFP4.purs             -- NVFP4 with E4M3 scales
  ├── Hadamard.purs          -- Block-wise Hadamard transform
  └── MRGPTQ.purs            -- MSE-optimal quantization

proofs/Hydrogen/GPU/Quantization/
  ├── FP4Format.lean         -- E2M1 value representation
  ├── HadamardOrthogonal.lean -- Hadamard preserves norms
  └── QuantizationBounds.lean -- Error bound proofs
```

#### Hydrogen Applications

| Schema Atom | Quantization | Error Bound |
|-------------|--------------|-------------|
| Pixel (0-255) | UINT8 | 0 |
| Normalized (0-1) | FP4 | ~0.01 |
| Color (sRGB) | FP4 × 3 | ~0.02 |
| Position | NVFP4 | ~0.01 |

#### Priority: ⭐⭐⭐⭐ HIGH

Direct GPU memory/compute savings. Essential for efficient rendering at scale.

────────────────────────────────────────────────────────────────────────────────

### Paper 1.5: QUARTET_FP4_TRAINING

**Source:** ISTA, ETH Zürich (Castro et al., 2026)
**arXiv:** 2505.14669

#### Core Contribution

Demonstrates near-lossless FP4 training with 2× speedup over FP8.

**Novel Scaling Law:**
```
L(N, D, P_forward, P_backward) = 
  (A / (N · effN(P_forward))^α + 
   B / (D · effD(P_backward))^β)^γ + E
```

Where:
- effN(P): Parameter efficiency (forward precision impact)
- effD(P): Data efficiency (backward precision impact)

#### Key Insight

Different precision requirements for forward vs backward:
- **Forward:** Minimize MSE → QuEST (Hadamard + MSE-optimal)
- **Backward:** Maximize gradient alignment → RTN (round-to-nearest)

| Method | effN | MSE | effD | Misalignment |
|--------|------|-----|------|--------------|
| Stochastic Rounding | 0.42 | 2.77e-2 | 0.88 | 0 |
| RTN AbsMax | 0.59 | 1.37e-2 | 0.93 | 9.3e-3 |
| QuEST | 0.64 | 1.32e-2 | 0.83 | 1.3e-2 |

**Optimal:** QuEST (forward) + RTN (backward)

#### Algorithms to Extract

**1. QuEST Quantization (Forward):**
```python
def quest_quantize(x, hadamard_block=32):
    # Normalize with Hadamard
    x_rotated = hadamard_transform(x, hadamard_block)
    x_norm = x_rotated / norm(x_rotated)
    
    # MSE-optimal clipping
    scale = find_mse_optimal_scale(x_norm)
    
    # Quantize
    return round(x_norm / scale) * scale
```

**2. RTN Quantization (Backward):**
```python
def rtn_quantize(x):
    # Simple absmax scaling
    scale = max(abs(x))
    return round(x / scale) * scale
```

**3. Scaling Law Fitting:**
```python
def fit_scaling_law(experiments):
    """Fit effN, effD from training runs"""
    # experiments: list of (N, D, P_fwd, P_bwd, loss)
    return optimize(scaling_law_loss, experiments)
```

#### Integration Points

```
-- For future neural rendering components
proofs/Hydrogen/Neural/
  ├── ScalingLaw.lean          -- Scaling law parameters
  └── TrainingBounds.lean      -- FP4 training error bounds

src/Hydrogen/Neural/
  ├── QuEST.purs               -- Forward quantization
  ├── RTN.purs                 -- Backward quantization
  └── ScalingPredict.purs      -- Predict optimal precision
```

#### Hydrogen Applications

For learned components (neural rendering, learned color spaces):
1. Pre-train in FP4 using Quartet
2. Quantize using MR-GPTQ
3. Compose error bounds end-to-end

```purescript
theorem Schema_Error_Bound {s : Schema} :
  RP (inference (quantize (train s))) s ≤ ε_total
  where ε_total = ε_training + ε_quantization
```

#### Priority: ⭐⭐⭐ MEDIUM

Relevant when we add neural components. Lower priority than inference-focused papers.

────────────────────────────────────────────────────────────────────────────────
                                                    // integration // roadmap
────────────────────────────────────────────────────────────────────────────────

## Integration Roadmap: Batch 1

### Phase 1: Theoretical Foundation (Immediate)

**Week 1-2:**
```
proofs/Hydrogen/Schema/Numeric/
  ├── GradedMonad.lean         -- M[ε] type with laws
  ├── RelativePrecision.lean   -- RP metric proofs
  └── NeighborhoodMonad.lean   -- T^r construction
```

**Deliverables:**
- [ ] Define `ForwardError ε α` structure
- [ ] Prove RP is an extended pseudometric
- [ ] Define neighborhood monad unit/join

### Phase 2: Typing Rules (Short-term)

**Week 3-4:**
```
proofs/Hydrogen/Schema/Numeric/
  ├── Primitives.lean          -- add/mul/div rules
  ├── DualContext.lean         -- Discrete | Linear
  └── Composition.lean         -- & vs ⊗ products
```

**Deliverables:**
- [ ] Implement Bean typing rules for primitives
- [ ] Prove backward error composition
- [ ] Define additive/multiplicative products

### Phase 3: GPU Quantization (Medium-term)

**Week 5-8:**
```
src/Hydrogen/GPU/Quantization/
  ├── FP4.purs
  ├── Hadamard.purs
  └── MRGPTQ.purs

proofs/Hydrogen/GPU/Quantization/
  └── QuantizationBounds.lean
```

**Deliverables:**
- [ ] Implement E2M1 format
- [ ] Implement block-wise Hadamard
- [ ] Prove quantization error bounds

### Phase 4: Serialization Proofs (Long-term)

**Week 9-12:**
```
proofs/Hydrogen/Schema/
  └── Serialization/
      ├── BackwardErrorLens.lean
      └── Roundtrip.lean
```

**Deliverables:**
- [ ] Define Bel category in Lean
- [ ] Prove `deserialize ∘ serialize` bounds
- [ ] Connect to GPUStorable typeclass

────────────────────────────────────────────────────────────────────────────────
                                                              // references
────────────────────────────────────────────────────────────────────────────────

## References

### Primary Sources (Batch 1)

1. Kellison (2025). "Type-Based Approaches to Rounding Error Analysis"
   PhD Dissertation, Cornell University. arXiv:2501.14598

2. Kellison et al. (2025). "Bean: A Language for Backward Error Analysis"
   arXiv:2501.14550

3. Castro et al. (2025). "Microscaling FP4 Quantization"
   arXiv:2509.23202

4. Castro et al. (2026). "Quartet: Native FP4 Training"
   arXiv:2505.14669

### Foundational References

- Reed & Pierce (2010). "Fuzz: Sensitivity Type Systems"
- Higham (2002). "Accuracy and Stability of Numerical Algorithms"
- Olver (1978). "Relative Precision Metric"
- Katsumata (2014). "Graded Monads"

────────────────────────────────────────────────────────────────────────────────
                                                              // batch // 2
────────────────────────────────────────────────────────────────────────────────

## Batch 2: Agent Systems, World Models & Simulation

### Paper 2.1: ONLINE_SUBMODULAR_MAXIMIZATION

**Source:** NeurIPS 2020 (Harvey, Liaw, Soma)
**Domain:** Online Learning / Combinatorial Optimization

#### Core Contribution

Improved algorithms for **online submodular maximization** using first-order
regret bounds instead of second-order bounds.

| Setting | Previous | New Result |
|---------|----------|------------|
| Monotone + matroid | O(k√(nT)) | O(√(kT ln(n/k))) |
| Nonmonotone | O(n√T) | O(√(nT)) |

Where k = rank of matroid, n = ground set size, T = time steps.

#### Key Insight

First-order regret bounds exploit structure in OLO subproblems:
- Sum of rewards cannot be arbitrarily large
- Data-dependent bounds outperform worst-case bounds

This is critical for **streaming computation** where T is unknown in advance.

#### Algorithms to Extract

**1. Online Continuous Greedy (Monotone Case):**
```python
def online_continuous_greedy(matroid_polytope, T):
    """
    Online algorithm with (1 - 1/e - ε)-regret O(√(kT ln(n/k)))
    """
    x = zeros(n)  # Fractional solution
    for t in range(T):
        # Receive submodular function f_t
        # Compute gradient of multilinear extension
        grad = multilinear_gradient(f_t, x)
        
        # OLO with first-order regret bound
        direction = olo_oracle(grad, matroid_polytope)
        
        # Update fractional solution
        x = x + (1/T) * direction
        
        # Round to integral solution
        S_t = pipage_round(x)
        
    return S_t
```

**2. USM Balance via Blackwell Approachability:**
```python
def usm_balance(deltas):
    """
    Balance subproblem for unconstrained submodular maximization.
    Uses Blackwell approachability for first-order regret.
    
    Regret: O(√(nT)) vs previous O(n√T)
    """
    # Blackwell instance
    X = {p | p+ + p- = 1, p ∈ [0,1]²}  # Action set
    Y = {Δ | Δ+ + Δ- ≥ 0, Δ ∈ [-1,1]²}  # Adversary set
    S = R²_≤0  # Target set
    
    # Online dual averaging
    for t, delta in enumerate(deltas):
        p_t = project_to_X(cumulative_gradient / t)
        cumulative_gradient += payoff(p_t, delta)
        
    return p_t
```

#### Integration Points

```
proofs/Hydrogen/Optimize/Submodular/
  ├── OnlineContinuousGreedy.lean  -- Monotone case
  ├── USMBalance.lean              -- Nonmonotone balance
  └── FirstOrderRegret.lean        -- Regret bound proofs

src/Hydrogen/Optimize/
  ├── SubmodularOnline.purs        -- Streaming implementation
  └── MatroidPolytope.purs         -- Matroid constraint
```

#### Hydrogen Applications

| Application | Submodular Function | Constraint |
|-------------|--------------------| ------------|
| **GPU region allocation** | Coverage of viewport | Cardinality k |
| **Feature selection** | Information gain | Matroid |
| **Cache eviction** | Submodular coverage | Memory budget |
| **Attention heads** | Diverse selection | Budget |

#### Priority: ⭐⭐⭐⭐ HIGH

Critical for real-time resource allocation in rendering pipeline.

────────────────────────────────────────────────────────────────────────────────

### Paper 2.2: LARGE_POPULATION_MODELS

**Source:** MIT (Ayush Chopra, 2025)
**arXiv:** 2507.09901
**Domain:** Multi-Agent Systems / Society-Scale Simulation

#### Core Contribution

**Large Population Models (LPMs)** simulate millions of agents with three innovations:

1. **Compositional Design:** Tensorized execution on GPU
2. **Differentiable Specification:** End-to-end gradient learning
3. **Decentralized Computation:** Privacy-preserving protocols

Performance: **600x speedup** for NYC simulation (8.4M agents).

#### Key Insight

Traditional ABMs: 25-1,000 agents
Policy needs: Millions
LPMs bridge this 1000x+ gap.

#### Algorithms to Extract

**1. Compositional Agent Update:**
```python
def agent_update(states, messages, environment, params):
    """
    Tensorized update for millions of agents.
    
    s_i(t+1) = f(s_i(t), Σ_j m_ij(t), ℓ(·|s_i(t)), e(t;θ))
    """
    # Batch compute all messages
    messages = message_function(neighbor_states, edge_env, params)
    
    # Aggregate messages per agent (sparse scatter)
    aggregated = scatter_add(messages, target_indices)
    
    # Batch behavior decisions
    decisions = behavior_function(states, aggregated, params)
    
    # Batch state updates
    new_states = update_function(states, decisions, environment)
    
    return new_states
```

**2. Differentiable Calibration:**
```python
def calibrate(params, observations, forward_sim):
    """
    Gradient-based calibration of agent parameters.
    
    θ̂ = argmin_θ ||F(θ, s(0), e(0)) - y||²
    """
    for epoch in range(epochs):
        # Forward simulation (differentiable)
        predicted = forward_sim(params, initial_state, environment)
        
        # Loss against observations
        loss = mse_loss(predicted, observations)
        
        # Gradient update
        grad = backprop(loss, params)
        params = optimizer.step(params, grad)
        
    return params
```

**3. AgentTorch Architecture:**
```python
class AgentTorch:
    """
    GPU-accelerated multi-agent simulation framework.
    """
    
    def __init__(self, agent_count, state_dim):
        self.states = torch.zeros(agent_count, state_dim, device='cuda')
        self.adjacency = sparse_tensor(...)  # Interaction graph
        
    def step(self, actions, environment):
        # Tensorized message passing
        messages = self.compute_messages()
        
        # Batch update
        self.states = self.update(messages, actions, environment)
        
        return self.states
```

#### Integration Points

```
src/Hydrogen/Agent/
  ├── Population.purs           -- LPM-style population management
  ├── TensorizedUpdate.purs     -- GPU-accelerated updates
  ├── MessagePassing.purs       -- Sparse message aggregation
  └── DifferentiableCalibration.purs

proofs/Hydrogen/Agent/
  ├── PopulationInvariants.lean -- Population-level guarantees
  └── UpdateCorrectness.lean    -- Update function proofs
```

#### Hydrogen Applications

| Need | LPM Solution |
|------|--------------|
| Billion-agent swarms | Compositional tensorized execution |
| Real-time simulation | 600x speedup demonstrated |
| Learning from data | Differentiable calibration |
| Privacy | Decentralized protocols |

#### Priority: ⭐⭐⭐⭐⭐ CRITICAL

**This is the architectural foundation for Hydrogen's agent runtime.**

────────────────────────────────────────────────────────────────────────────────

### Paper 2.3: GAIA2_WORLD_MODEL

**Source:** Wayve (Russell et al., 2025)
**arXiv:** 2503.20523
**Domain:** Generative World Models / Autonomous Driving

#### Core Contribution

**GAIA-2**: 8.4B parameter latent diffusion world model for controllable
multi-view video generation.

| Component | Spec |
|-----------|------|
| Video Tokenizer | 285M params, ~400× compression |
| World Model | 8.4B params, flow matching |
| Resolution | 448×960 per camera, 5 views |
| Control | Speed, curvature, agents, weather, time |

#### Key Insight

**Latent space design** is critical for quality/speed trade-off:
- 32× spatial compression (vs typical 8×)
- 8× temporal compression
- Flow matching instead of DDPM for stable training

#### Algorithms to Extract

**1. Video Tokenizer (Encoder):**
```python
def encode_video(frames, temporal_window=8):
    """
    Compress video to latent space.
    
    Spatial: 32× compression
    Temporal: 8× compression
    Total: ~400×
    """
    # Downsample spatially
    x = conv3d(frames, stride=(2, 8, 8))  # [T, H/8, W/8]
    x = conv3d(x, stride=(2, 2, 2))       # [T/2, H/16, W/16]
    
    # Spatial transformer
    x = spatial_transformer(x, blocks=24)
    
    # Final compression
    x = conv3d(x, stride=(1, 2, 2))       # [T/2, H/32, W/32]
    
    # Sample latent
    mu, sigma = split(x, dim=-1)
    z = mu + sigma * randn_like(sigma)
    
    return z  # [T/8, H/32, W/32, 64]
```

**2. Flow Matching Training:**
```python
def flow_matching_loss(model, x_data, conditions):
    """
    Flow matching for stable generative training.
    
    Learns velocity field v = x - ε
    """
    # Sample flow time from bimodal logit-normal
    tau = sample_flow_time()  # Bimodal for structure + gradients
    
    # Interpolate between noise and data
    epsilon = randn_like(x_data)
    x_tau = tau * x_data + (1 - tau) * epsilon
    
    # Target velocity
    v_target = x_data - epsilon
    
    # Predict velocity
    v_pred = model(x_tau, conditions, tau)
    
    return mse_loss(v_pred, v_target)
```

**3. Adaptive Layer Norm Conditioning:**
```python
def adaptive_layer_norm(x, condition, time_emb):
    """
    Inject conditions into transformer via learned scale/shift.
    """
    # Learn scale and shift from conditions
    gamma = mlp(condition) + mlp(time_emb)
    beta = mlp(condition) + mlp(time_emb)
    
    # Normalize then scale/shift
    x_norm = (x - mean(x)) / std(x)
    return x_norm * (1 + gamma) + beta
```

**4. Symlog Transform for Actions:**
```python
def symlog(y, scale, y_max):
    """
    Symmetric logarithmic transform for unbounded inputs.
    
    Compresses large values while preserving sign.
    """
    return sign(y) * log(1 + scale * abs(y)) / log(1 + scale * abs(y_max))
```

#### Integration Points

```
src/Hydrogen/Video/
  ├── Tokenizer.purs           -- Video encoder/decoder
  ├── FlowMatching.purs        -- Generative training
  ├── AdaptiveLayerNorm.purs   -- Conditioning mechanism
  └── Symlog.purs              -- Action encoding

proofs/Hydrogen/Video/
  └── TokenizerBounds.lean     -- Compression error bounds
```

#### Hydrogen Applications

| Component | Application |
|-----------|-------------|
| Video tokenizer | Efficient latent representation for UI animations |
| Flow matching | Stable training for learned rendering |
| Adaptive LayerNorm | Conditioning generation on design tokens |
| Multi-view consistency | Consistent rendering across viewports |

#### Priority: ⭐⭐⭐ MEDIUM

Relevant for future video/animation capabilities, not core rendering.

────────────────────────────────────────────────────────────────────────────────

### Paper 2.4: VISUAL_THEORY_MIND

**Source:** Brown University (Spiegel et al., 2025)
**Domain:** Emergent Communication / Cognitive Science

#### Core Contribution

Multi-agent RL testbed (**Signification Game**) demonstrating how **visual
theory of mind** enables agents to invent proto-writing systems.

#### Key Insight

Agents with visual theory of mind can:
- Communicate actions using pictographs
- Develop shared symbolic representations
- Invent proto-writing without explicit supervision

#### Relevance to Hydrogen

| Insight | Application |
|---------|-------------|
| Emergent symbols | Agent communication protocols |
| Visual ToM | Agent reasoning about UI elements |
| Signification | Design system semantics |

#### Priority: ⭐⭐ LOW

Interesting for long-term agent communication research, not immediate priority.

────────────────────────────────────────────────────────────────────────────────

### Paper 2.5: STREAM_FUNCTION_FLUID

**Source:** IST Austria, TUM (Ando, Thuerey, Wojtan, 2025)
**Domain:** Fluid Simulation / Computer Graphics

#### Core Contribution

**Stream function solver** for liquid simulation instead of pressure projection.

Benefits:
- Guaranteed divergence-free regardless of solve accuracy
- Two-phase flow by computing single phase only
- Complex bubble formation without explicit gas phase

#### Key Algorithm

```python
def stream_function_solve(velocity_field, boundaries):
    """
    Solve for divergence-free velocity via stream function.
    
    Key: v = curl(ψ) is automatically divergence-free
    """
    # Stream function formulation
    # Instead of: ∇²p = ∇·v (pressure Poisson)
    # Solve: ∇²ψ = ω (stream function Poisson)
    
    omega = curl(velocity_field)
    psi = poisson_solve(omega, boundaries)
    
    # Velocity from stream function is divergence-free by construction
    v_divergence_free = curl(psi)
    
    return v_divergence_free
```

#### Priority: ⭐⭐ LOW

Specialized for fluid simulation, not core to design system.

────────────────────────────────────────────────────────────────────────────────
                                              // batch 2 // integration // summary
────────────────────────────────────────────────────────────────────────────────

## Batch 2 Integration Summary

| Paper | Priority | Key Takeaway | Integration Target |
|-------|----------|--------------|-------------------|
| **Online Submodular** | ⭐⭐⭐⭐ | First-order regret for streaming | `Optimize/Submodular/` |
| **Large Population Models** | ⭐⭐⭐⭐⭐ | Agent runtime architecture | `Agent/` |
| **GAIA-2** | ⭐⭐⭐ | Flow matching, adaptive LayerNorm | `Video/` |
| **Visual ToM** | ⭐⭐ | Emergent communication | Future research |
| **Stream Function** | ⭐⭐ | Divergence-free simulation | Physics only |

### Immediate Actions (Batch 2):

1. **LPM Architecture Study** — Design Hydrogen's agent runtime based on AgentTorch patterns
2. **Online Submodular Implementation** — Add first-order regret algorithms to existing `Optimize/Submodular/`
3. **Flow Matching Evaluation** — Consider for future learned rendering components

────────────────────────────────────────────────────────────────────────────────

────────────────────────────────────────────────────────────────────────────────
                                                              // batch // 3
────────────────────────────────────────────────────────────────────────────────

## Batch 3: Tera-Scale Agents, Reasoning, and Effect Systems

### Paper 3.1: TERAAGENT_SIMULATION

**Source:** ETH Zurich, TU Delft, CERN (Breitwieser et al., 2025)
**arXiv:** 2509.24063
**Domain:** Distributed Simulation / Agent-Based Modeling

#### Core Contribution

**TeraAgent**: Distributed agent-based simulation engine achieving **half a trillion agents** (501.51 billion).

| Metric | Previous SOTA | TeraAgent | Improvement |
|--------|--------------|-----------|-------------|
| Max Agents | 1.7B (BioDynaMo) | 501.51B | 250× |
| Agent Updates/sec/core | - | 8× Biocellion | 8× |
| Serialization | Baseline | 110× | 110× |
| Data Transfer | Baseline | 3.5× reduction | 3.5× |

#### Key Innovations

**1. Tailored Serialization:**
- Direct access to objects from receive buffer
- Maintains full mutability
- 110× faster serialization, 37× faster deserialization

**2. Delta Encoding:**
- Exploits iterative nature of ABM simulations
- Agents change gradually between steps
- Only transmit deltas, not full state

**3. Spatial Partitioning:**
- Simulation space divided across servers
- Border regions enable agent migration
- Aura exchange for local environment

#### Algorithms to Extract

**1. Delta Encoding for Agent State:**
```python
def encode_delta(prev_state, curr_state):
    """
    Only encode changed fields.
    
    Achieves 3.5× reduction in data transfer.
    """
    delta = {}
    for field in curr_state.fields():
        if curr_state[field] != prev_state[field]:
            delta[field] = curr_state[field]
    return delta

def apply_delta(prev_state, delta):
    """Reconstruct current state from previous + delta."""
    curr_state = copy(prev_state)
    for field, value in delta.items():
        curr_state[field] = value
    return curr_state
```

**2. Spatial Partitioning:**
```python
def partition_space(bounds, n_servers):
    """
    Divide simulation space into partitions.
    """
    # Grid-based partitioning
    partitions = []
    for i in range(n_servers):
        partition_bounds = compute_bounds(bounds, i, n_servers)
        partitions.append(Partition(partition_bounds))
    return partitions

def exchange_auras(partitions):
    """
    Exchange border regions for local interactions.
    """
    for p1, p2 in neighboring_partitions(partitions):
        # Send agents in border region
        border_agents = p1.get_border_agents(p2.bounds)
        p2.receive_aura(border_agents)
```

#### Integration Points

```
src/Hydrogen/Agent/
  ├── Distributed.purs         -- Scale-out architecture
  ├── DeltaEncoding.purs       -- State delta compression
  ├── SpatialPartition.purs    -- Space partitioning
  └── AuraExchange.purs        -- Border region exchange

proofs/Hydrogen/Agent/
  ├── DeltaCorrectness.lean    -- Delta encode/decode roundtrip
  └── PartitionCoverage.lean   -- Partitions cover full space
```

#### Hydrogen Applications

| Need | TeraAgent Solution |
|------|-------------------|
| Billion-agent scale | 501B agents demonstrated |
| Network efficiency | Delta encoding (3.5× reduction) |
| Serialization speed | Tailored format (110× faster) |
| Distributed execution | MPI-based scale-out |

#### Priority: ⭐⭐⭐⭐⭐ CRITICAL

**Direct architectural pattern for Hydrogen's distributed agent runtime.**

────────────────────────────────────────────────────────────────────────────────

### Paper 3.2: DEEPSEEK_R1_REASONING

**Source:** DeepSeek-AI (January 2026)
**arXiv:** 2501.12948
**Domain:** Large Language Models / Reinforcement Learning

#### Core Contribution

**DeepSeek-R1**: Reasoning capabilities through **pure reinforcement learning** without human-annotated reasoning trajectories.

**Key Breakthrough:** GRPO (Group Relative Policy Optimization) enables:
- Emergent self-reflection
- Verification behaviors
- Dynamic strategy adaptation
- SOTA on math, coding, STEM

#### Key Insight

> Human-defined reasoning patterns may limit model exploration

Pure RL allows models to discover reasoning strategies that humans wouldn't annotate.

#### Algorithms to Extract

**1. GRPO (Group Relative Policy Optimization):**
```python
def grpo_loss(policy, question, G=16):
    """
    Sample G outputs, compute advantage relative to group mean.
    
    More efficient than PPO: no critic network needed.
    """
    # Sample G outputs
    outputs = [policy.sample(question) for _ in range(G)]
    
    # Evaluate rewards (correctness only)
    rewards = [evaluate_correctness(o) for o in outputs]
    
    # Compute advantages relative to group mean
    mean_reward = mean(rewards)
    advantages = [r - mean_reward for r in rewards]
    
    # PPO-style clipped objective
    loss = 0
    for output, advantage in zip(outputs, advantages):
        ratio = policy.prob(output) / policy_old.prob(output)
        clipped = clip(ratio, 1-eps, 1+eps) * advantage
        loss += min(ratio * advantage, clipped)
    
    return -loss  # Maximize expected advantage
```

**2. Emergent Reasoning Detection:**
```python
def detect_emergent_behaviors(outputs):
    """
    Identify emergent reasoning patterns.
    """
    patterns = {
        'self_reflection': [],
        'verification': [],
        'alternative_exploration': [],
        'longer_chains': []
    }
    
    for output in outputs:
        if contains_reflection(output):
            patterns['self_reflection'].append(output)
        if contains_verification(output):
            patterns['verification'].append(output)
        # ... etc
    
    return patterns
```

#### Integration Points

```
src/Hydrogen/Agent/
  ├── GRPO.purs                -- Group Relative Policy Optimization
  ├── ReasoningLoop.purs       -- Self-correcting agent loops
  └── EmergentStrategy.purs    -- Dynamic strategy selection

proofs/Hydrogen/Agent/
  └── GRPOConvergence.lean     -- GRPO convergence guarantees
```

#### Hydrogen Applications

| Need | R1 Solution |
|------|------------|
| Agent reasoning | Pure RL emergent reasoning |
| Self-verification | Models learn to check work |
| Scalable training | GRPO more efficient than PPO |
| No human annotation | Correctness-only reward |

#### Priority: ⭐⭐⭐ MEDIUM

Relevant for future learned agent behaviors, not immediate rendering focus.

────────────────────────────────────────────────────────────────────────────────

### Paper 3.3: FP4_ALL_THE_WAY

**Source:** Intel, NVIDIA, Technion (Chmiel et al., 2025)
**arXiv:** 2505.19115
**Domain:** Low-Precision Training / Quantization

#### Core Contribution

First demonstration of **Fully Quantized Training (FQT)** using FP4 for weights, activations, AND gradients on datasets up to 200B tokens.

| Component | Precision | Format |
|-----------|-----------|--------|
| Weights | FP4 | NVFP4 (E2M1 + E4M3 scale) |
| Activations | FP4 | NVFP4 |
| Gradients | FP4 | NVFP4 |

#### Key Findings

**1. NVFP4 is Optimal:**
- Block size 16 (vs MXFP4's 32)
- E4M3 scale format (vs E8M0)
- Better granularity for outliers

**2. Split Rounding Strategy:**
| Pass | Method | Reason |
|------|--------|--------|
| Forward | Round-to-Nearest (RtN) | Lower MSE |
| Backward | Stochastic Rounding (SR) | Reduces gradient bias |

**3. Gradient Noise Threshold:**
```
σ_gradient < √3 × σ_quantization
```
When gradient norm falls below this, apply Quantization-Aware Finetuning (QAF).

#### Algorithms to Extract

**1. Split Rounding:**
```python
def forward_quantize(x, format='NVFP4'):
    """Round-to-nearest for forward pass."""
    scale = compute_scale(x, block_size=16, scale_format='E4M3')
    return round(x / scale) * scale  # RtN

def backward_quantize(grad, format='NVFP4'):
    """Stochastic rounding for backward pass."""
    scale = compute_scale(grad, block_size=16, scale_format='E4M3')
    normalized = grad / scale
    floor_val = floor(normalized)
    prob = normalized - floor_val
    rounded = floor_val + (random() < prob)  # SR
    return rounded * scale
```

**2. Gradient Noise Detection:**
```python
def should_apply_qaf(gradients, quantization_error):
    """
    Detect when gradient noise exceeds quantization threshold.
    """
    grad_norm = norm(gradients)
    threshold = sqrt(3) * quantization_error
    return grad_norm < threshold
```

#### Integration Points

```
src/Hydrogen/GPU/Quantization/
  ├── FQT.purs                 -- Fully quantized training
  ├── SplitRounding.purs       -- Forward RtN, Backward SR
  └── GradientNoise.purs       -- Threshold detection

proofs/Hydrogen/GPU/Quantization/
  ├── SplitRoundingBias.lean   -- SR eliminates bias
  └── NoiseThreshold.lean      -- √3 threshold proof
```

#### Hydrogen Applications

Extends Paper 1.4 (MICROSCALING_FP4_QUANTIZATION) with:
- Full training support (not just inference)
- Split rounding strategy
- Gradient noise threshold for QAF timing

#### Priority: ⭐⭐⭐⭐ HIGH

Direct extension of FP4 quantization work. Enables efficient GPU training.

────────────────────────────────────────────────────────────────────────────────

### Paper 3.4: EFFECT_INFERENCE_HIGHER_RANK

**Source:** University of Wrocław (Balik, Jędras, Polesiuk, 2025)
**arXiv:** 2510.20532
**Domain:** Programming Languages / Type Systems

#### Core Contribution

**Sound and complete effect inference algorithm** for type-and-effect systems with:
- Subtyping
- Higher-rank polymorphism
- Set-like semantics of effects

**Key Innovation:** Transform effect constraints into propositional logic formulae.

#### Key Insight

Higher-rank polymorphism creates scoping issues for effect variables. Solution:
**Delay solving** by encoding constraints as propositional formulae.

#### Algorithms to Extract

**1. Two-Stage Effect Inference:**
```
Stage 1: Type Reconstruction (Hindley-Milner)
         Γ ⊢ e : τ | C_type
         
Stage 2: Effect Constraint Solving
         C_effect → PropLogic → SAT → Substitution
```

**2. Constraint Transformation:**
```python
def transform_to_proplogic(effect_constraints):
    """
    Transform effect constraints to propositional formulae.
    
    ε₁ ⊆ ε₂  →  ∀x. x ∈ ε₁ → x ∈ ε₂
    ε₁ = ε₂  →  ε₁ ⊆ ε₂ ∧ ε₂ ⊆ ε₁
    """
    formulae = []
    for constraint in effect_constraints:
        if isinstance(constraint, Subset):
            formulae.append(subset_to_implication(constraint))
        elif isinstance(constraint, Equality):
            formulae.append(equality_to_biconditional(constraint))
    return And(formulae)
```

**3. Higher-Rank Effect Scoping:**
```haskell
-- Rank-2 polymorphism for effect scoping
withFile :: ∀β. Filepath → (∀α. File α → α·β Unit) → IO·β Unit

-- The ∀α ensures File handle can't escape its scope
-- Effect α is bound within the callback
```

#### Integration Points

```
proofs/Hydrogen/Schema/Effect/
  ├── EffectInference.lean     -- Sound + complete algorithm
  ├── HigherRank.lean          -- Rank-N polymorphism support
  ├── SetLikeEffects.lean      -- Union/intersection semantics
  └── ConstraintSolving.lean   -- PropLogic transformation

src/Hydrogen/Schema/Effect/
  ├── Infer.purs               -- Effect inference implementation
  └── HigherRank.purs          -- Higher-rank effect types
```

#### Hydrogen Applications

| Hydrogen Need | This Paper's Solution |
|--------------|----------------------|
| Effect tracking for Elements | Type-and-effect system |
| Compositional effect bounds | Set-like semantics |
| Scope-restricted resources | Higher-rank polymorphism |
| Automatic inference | Sound + complete algorithm |

#### Direct Connection to Bean (Paper 1.2)

Bean uses dual contexts (Discrete | Linear). This paper provides the inference algorithm for such systems with higher-rank polymorphism.

#### Priority: ⭐⭐⭐⭐⭐ CRITICAL

**Provides the inference algorithm for Hydrogen's graded effect system.**

────────────────────────────────────────────────────────────────────────────────

### Paper 3.5: PAN_WORLD_MODEL

**Source:** MBZUAI (PAN Team, 2025)
**arXiv:** 2511.09057
**Domain:** World Models / Video Generation

#### Core Contribution

**PAN**: General, interactable, long-horizon world model using **Generative Latent Prediction (GLP)** architecture:

| Component | Model | Purpose |
|-----------|-------|---------|
| Vision Encoder | Qwen2.5-VL-7B | Observations → Latents |
| World Model | Autoregressive LLM | Predict latent dynamics |
| Video Decoder | Wan2.1-T2V-14B | Latents → Video |

#### Key Insight

**GLP Architecture** unifies:
- Latent space reasoning (LLM backbone)
- Perceptual grounding (video diffusion)
- Action conditioning (natural language)

#### Algorithms to Extract

**1. GLP Joint Distribution:**
```python
def glp_predict(observation, action):
    """
    Generative Latent Prediction.
    
    p(o_{t+1} | o_t, a_t) = Σ p_h(ŝ_t|o_t) · p_f(ŝ_{t+1}|ŝ_t,a_t) · p_g(o_{t+1}|ŝ_{t+1})
    """
    # Encode observation to latent
    latent_t = encoder(observation)  # p_h
    
    # Predict next latent given action
    latent_t1 = world_model(latent_t, action)  # p_f
    
    # Decode to observation
    observation_t1 = decoder(latent_t1)  # p_g
    
    return observation_t1
```

**2. Causal Swin-DPM for Long Horizon:**
```python
def long_horizon_generate(initial_obs, actions, chunk_size=8):
    """
    Chunk-wise causal attention for stable long-horizon generation.
    """
    chunks = []
    prev_chunk = None
    
    for i, action_chunk in enumerate(chunk(actions, chunk_size)):
        if prev_chunk is not None:
            # Condition on slightly noised last frame
            conditioning = add_noise(prev_chunk[-1], sigma=0.1)
        else:
            conditioning = initial_obs
            
        # Generate chunk with causal attention mask
        chunk_i = generate_chunk(
            conditioning, 
            action_chunk,
            causal_mask=True
        )
        chunks.append(chunk_i)
        prev_chunk = chunk_i
    
    return concatenate(chunks)
```

#### Integration Points

```
src/Hydrogen/WorldModel/
  ├── GLP.purs                 -- Generative Latent Prediction
  ├── CausalSwinDPM.purs       -- Long-horizon generation
  └── ActionConditioning.purs  -- Natural language actions

proofs/Hydrogen/WorldModel/
  └── GLPComposition.lean      -- Encoder/predictor/decoder compose
```

#### Hydrogen Applications

| Component | Application |
|-----------|-------------|
| GLP architecture | UI state prediction |
| Causal Swin-DPM | Smooth animation generation |
| Action conditioning | Natural language UI control |

#### Priority: ⭐⭐⭐ MEDIUM

Relevant for future predictive UI and animation capabilities.

────────────────────────────────────────────────────────────────────────────────
                                               // batch 3 // integration // summary
────────────────────────────────────────────────────────────────────────────────

## Batch 3 Integration Summary

| Paper | Priority | Key Takeaway | Integration Target |
|-------|----------|--------------|-------------------|
| **TeraAgent** | ⭐⭐⭐⭐⭐ | 501B agent scale-out | `Agent/Distributed/` |
| **DeepSeek-R1** | ⭐⭐⭐ | GRPO for emergent reasoning | `Agent/Reasoning/` |
| **FP4 All The Way** | ⭐⭐⭐⭐ | Split rounding for FQT | `GPU/Quantization/` |
| **Effect Inference** | ⭐⭐⭐⭐⭐ | Sound+complete effect inference | `Schema/Effect/` |
| **PAN World Model** | ⭐⭐⭐ | GLP architecture | `WorldModel/` |

### Immediate Actions (Batch 3):

1. **TeraAgent Architecture** — Study delta encoding and spatial partitioning for distributed Hydrogen runtime
2. **Effect Inference Integration** — Implement propositional constraint solving for graded effects
3. **FP4 Split Rounding** — Extend quantization module with forward RtN / backward SR

### Cross-Batch Synergies:

| Batch 1-2 Paper | Batch 3 Paper | Synergy |
|-----------------|---------------|---------|
| NumFuzz/Bean | Effect Inference | Inference algorithm for graded types |
| LPM (AgentTorch) | TeraAgent | Complementary scale-out approaches |
| FP4 Quantization | FP4 All The Way | Training + inference complete story |

────────────────────────────────────────────────────────────────────────────────
                                                              // batch // 4
────────────────────────────────────────────────────────────────────────────────

## Batch 4: Multimodal Systems, Voice, and Information Theory

### Paper 4.1: QWEN25_OMNI

**Source:** Alibaba Qwen Team (March 2025)
**arXiv:** 2503.20215
**Domain:** Multimodal Models / Speech Synthesis

#### Core Contribution

**Qwen2.5-Omni**: End-to-end multimodal model that perceives text/images/audio/video
and generates text + natural speech **simultaneously and in real-time**.

| Capability | Performance |
|------------|-------------|
| Voice instruction | 95% of text performance |
| Multimodal reasoning | SOTA on OmniBench (56.13%) |
| Speech naturalness | 4.62 NMOS (exceeds human 4.51) |

#### Key Innovations

**1. Thinker-Talker Architecture:**
```
Thinker (Brain): Understanding + text generation
    │
    ├── Shared representations
    │
Talker (Mouth): Speech token generation
```

- End-to-end training with shared context
- Concurrent text + speech output
- No interference between modalities

**2. TMRoPE (Time-aligned Multimodal RoPE):**
```python
def tmrope_position(modality, timestamp):
    """
    Time-aligned position embedding for multimodal sync.
    """
    if modality == 'text':
        return (text_pos, text_pos, text_pos)  # 1D equivalent
    elif modality == 'audio':
        temporal_id = timestamp // 40  # 40ms per frame
        return (temporal_id, audio_pos, audio_pos)
    elif modality == 'video':
        temporal_id = frame_number * frame_duration
        return (temporal_id, height_pos, width_pos)
```

**3. Block-wise Streaming:**
- Audio: 2-second blocks
- Vision: 2×2 token merging
- Sliding window DiT: 4-block receptive field (2 lookback, 1 lookahead)

#### Integration Points

```
src/Hydrogen/Multimodal/
  ├── ThinkerTalker.purs       -- Dual-track architecture
  ├── TMRoPE.purs              -- Time-aligned position encoding
  └── BlockwiseStream.purs     -- Chunked processing

proofs/Hydrogen/Multimodal/
  └── TemporalSync.lean        -- Prove audio/video alignment
```

#### Hydrogen Applications

| Component | Application |
|-----------|-------------|
| Thinker-Talker | Separate Element understanding from rendering |
| TMRoPE | Temporal coherence in animations |
| Block-wise streaming | Real-time rendering pipeline |

#### Priority: ⭐⭐⭐ MEDIUM

Relevant for future voice-enabled UI, not immediate rendering focus.

────────────────────────────────────────────────────────────────────────────────

### Paper 4.2: GAMEFACTORY

**Source:** HKU + Kuaishou (Yu et al., 2025)
**arXiv:** 2501.08325
**Domain:** Generative Video / Interactive Media

#### Core Contribution

**GameFactory**: Scene-generalizable action-controlled game video generation.

| Challenge | Solution |
|-----------|----------|
| Action controllability | Keyboard/mouse input conditioning |
| Scene generalization | Domain adapter for new game styles |
| Autoregressive generation | Unlimited-length interactive videos |

#### Key Insight

Decouple **game style** from **action control**:
- Style: Learned from reference frames
- Actions: Conditioned on input stream

#### Integration Points (Brief)

```
src/Hydrogen/Interactive/
  └── ActionConditioned.purs   -- Input-conditioned generation
```

#### Priority: ⭐⭐ LOW

Game-specific, limited applicability to design system.

────────────────────────────────────────────────────────────────────────────────

### Paper 4.3: LAWNDAUER_PRECISION

**Source:** Anonymous (December 2025)
**Domain:** Quantization / Thermodynamics / Information Theory

#### Core Contribution

Thermodynamic framework for neural network precision using **Landauer's principle**.

**Key Insight:**
> "The only costly operation is forgetting — and the only difficult problem is forgetting precisely the right amount."

#### Fundamental Principle

```
Minimum energy cost = kT ln 2 per bit erased
```

Precision is not a hyperparameter to optimize — it's a **physical quantity to measure**.

#### Key Findings

**1. Codebook Injectivity:**
Bijective mappings are gauge symmetries that conserve task information.

**2. Epilogue Optimization:**
The fused post-accumulator (epilogue) is the **last place** where gauge freedom can be exercised for precision reduction.

**3. Unification:**
Shows GPTQ, AWQ, SmoothQuant are implicit **Landauer minimization**.

#### Algorithms to Extract

**1. Information-Theoretic Precision Assignment:**
```python
def optimal_precision(layer, task_information):
    """
    Precision = measured bits of task-relevant information.
    
    Not a hyperparameter to tune, but a quantity to measure.
    """
    # Measure mutual information with task
    I_task = mutual_information(layer.output, task.target)
    
    # Precision = ceiling of measured bits
    precision = ceil(I_task)
    
    return precision
```

**2. Epilogue Gauge Freedom:**
```python
def optimize_epilogue(accumulator, output_format):
    """
    The epilogue (post-accumulator) is the last reversible opportunity.
    
    Apply gauge transformations here for optimal precision.
    """
    # Measure information content
    bits_needed = measure_information(accumulator)
    
    # Apply bijective transform preserving information
    transformed = gauge_transform(accumulator, bits_needed)
    
    # Quantize to output format
    return quantize(transformed, output_format)
```

#### Integration Points

```
proofs/Hydrogen/Information/
  ├── Landauer.lean            -- kT ln 2 bound formalization
  ├── GaugeFreedom.lean        -- Bijective invariance proofs
  └── PrecisionMeasure.lean    -- Information-theoretic precision

src/Hydrogen/GPU/Quantization/
  └── InformationPrecision.purs -- Measured precision assignment
```

#### Hydrogen Applications

| Insight | Application |
|---------|-------------|
| Precision = information | Schema atoms have measured bounds |
| Gauge freedom | Equivalent representations for same information |
| Epilogue optimization | Post-render quantization |

#### Connection to NumFuzz/Bean (Papers 1.1-1.2)

Landauer provides the **physical justification** for why bounded types matter:
- Forward error = bits produced by forgetting
- Backward error = bits consumed by approximation
- Landauer bound = minimum energy cost of these operations

#### Priority: ⭐⭐⭐⭐ HIGH

Provides theoretical foundation connecting quantization to information theory.

────────────────────────────────────────────────────────────────────────────────

### Paper 4.4: MULTIMODAL_GUI

**Source:** uxx.ai (van Dam, 2025)
**arXiv:** 2510.06223
**Domain:** Human-Computer Interaction / Voice Interfaces

#### Core Contribution

Architecture for GUI↔LLM integration via **Model Context Protocol (MCP)**:
- Application navigation graph exposed through MCP
- ViewModel exposes tools for current view
- Full voice accessibility

#### Key Insight

GUIs should expose **semantic structure** (navigation graph + available tools)
rather than requiring visual parsing.

#### Architecture Pattern

```
GUI (View) ←── ViewModel (State) ←── MCP ←── LLM Assistant
                    │
                    ├── getLocalTools()      // Current view tools
                    ├── getGlobalTools()     // App-wide tools  
                    └── getNavigationGraph() // Reachable views
```

#### Algorithms to Extract

**1. Tool Exposure via ViewModel:**
```typescript
interface ViewModel {
  // Tools scoped to current view
  getLocalTools(): Tool[];
  
  // Application-global tools
  getGlobalTools(): Tool[];
  
  // Navigation graph for semantic understanding
  getNavigationGraph(): NavigationNode[];
}

interface Tool {
  name: string;
  description: string;
  parameters: Parameter[];
  execute: (args: any) => Promise<Result>;
}
```

**2. MCP Navigation Graph:**
```typescript
interface NavigationNode {
  id: string;
  label: string;
  children: NavigationNode[];
  tools: Tool[];
  currentView: boolean;
}

function buildNavigationGraph(rootView: View): NavigationNode {
  return {
    id: rootView.id,
    label: rootView.title,
    children: rootView.subviews.map(buildNavigationGraph),
    tools: rootView.viewModel.getLocalTools(),
    currentView: rootView.isVisible
  };
}
```

#### Integration Points

```
src/Hydrogen/Accessibility/
  ├── MCP.purs                 -- Model Context Protocol adapter
  ├── NavigationGraph.purs     -- Expose Element tree as nav graph
  └── ToolExposure.purs        -- Derive tools from Element structure

proofs/Hydrogen/Accessibility/
  └── ToolSoundness.lean       -- Tool execution preserves invariants
```

#### Hydrogen Applications

| Need | MCP Solution |
|------|--------------|
| Voice accessibility | Semantic tool exposure |
| Agent navigation | Navigation graph |
| LLM integration | Standardized MCP protocol |
| Discoverability | Tools derived from view structure |

#### Priority: ⭐⭐⭐⭐ HIGH

**Direct applicability to making Hydrogen UIs accessible to AI agents.**

────────────────────────────────────────────────────────────────────────────────

### Paper 4.5: COSYVOICE2_TTS

**Source:** Alibaba (Du et al., 2024)
**arXiv:** 2412.10117
**Domain:** Speech Synthesis / Streaming TTS

#### Core Contribution

**CosyVoice 2**: Streaming zero-shot TTS with human-parity naturalness.

| Metric | Value |
|--------|-------|
| First packet latency | 150ms |
| WER (test-en) | 2.57% |
| Streaming quality loss | ~0% |

#### Key Innovations

**1. Finite Scalar Quantization (FSQ):**
```python
def fsq_forward(hidden, proj_down, proj_up, K):
    """
    FSQ replaces VQ with bounded round operation.
    
    No codebook lookup - just round to nearest integer in [-K, K].
    """
    low_rank = proj_down(hidden)           # Project to low dimension D
    quantized = round(low_rank)            # Round to integers
    quantized = clamp(quantized, -K, K)    # Bound to [-K, K]
    return proj_up(quantized)              # Project back up

def compute_token_index(quantized, D, K):
    """
    Convert quantized vector to single token index.
    
    Token space: (2K + 1)^D
    """
    index = 0
    for j in range(D):
        index += quantized[j] * (2*K + 1)**j
    return index
```

**2. Chunk-Aware Causal Flow Matching:**
```python
def chunk_aware_flow(tokens, chunk_size=15):
    """
    Generate mel spectrogram in chunks for streaming.
    
    Lookahead convolution: P=4 (1D conv, right-padded)
    """
    mel_chunks = []
    for chunk in chunks(tokens, chunk_size):
        # Causal attention within chunk
        context = causal_attention(chunk)
        
        # Flow matching: tokens → mel
        mel = flow_match_decode(context)
        mel_chunks.append(mel)
    
    return concat(mel_chunks)
```

**3. Unified Streaming/Non-Streaming:**
Single model handles both modes via sequence construction:
- Non-streaming: `[S, text, T, speech, E]`
- Streaming: `[S, text_1...text_N, speech_1...speech_M] × k`

Where N=5 (text), M=15 (speech) is fixed ratio.

#### Integration Points

```
src/Hydrogen/Voice/
  ├── FSQ.purs                 -- Finite Scalar Quantization
  ├── ChunkAwareFlow.purs      -- Chunk-aware flow matching
  ├── StreamingTTS.purs        -- Unified streaming synthesis
  └── ZeroShotVoice.purs       -- Voice cloning from reference

proofs/Hydrogen/Voice/
  ├── FSQBounds.lean           -- Token index within bounds
  └── ChunkConsistency.lean    -- Chunks produce consistent output
```

#### Hydrogen Applications

| Component | Application |
|-----------|-------------|
| FSQ | Bounded speech tokenization |
| Chunk-aware flow | Streaming audio generation |
| Zero-shot voice | Brand voice synthesis |

#### FSQ Connection to Schema Atoms

FSQ is essentially a **Schema atom for speech**:
- Bounded: values in `[-K, K]^D`
- Deterministic: round operation is reproducible
- Composable: token index = polynomial combination

```purescript
-- FSQ as Schema atom
data FSQToken (d :: Int) (k :: Int)
  = FSQToken (Vec d (BoundedInt (-k) k))

-- Compute token index
tokenIndex :: forall d k. FSQToken d k -> Nat
tokenIndex (FSQToken vec) = 
  sum $ mapWithIndex (\j v -> v * (2*k + 1)^j) vec
```

#### Priority: ⭐⭐⭐ MEDIUM

Relevant for future voice interface, FSQ pattern applicable to other domains.

────────────────────────────────────────────────────────────────────────────────
                                               // batch 4 // integration // summary
────────────────────────────────────────────────────────────────────────────────

## Batch 4 Integration Summary

| Paper | Priority | Key Takeaway | Integration Target |
|-------|----------|--------------|-------------------|
| **Qwen2.5-Omni** | ⭐⭐⭐ | Thinker-Talker architecture | `Multimodal/` |
| **GameFactory** | ⭐⭐ | Action-conditioned generation | Low priority |
| **Landauer Precision** | ⭐⭐⭐⭐ | Precision = information | `Information/` |
| **Multimodal GUI** | ⭐⭐⭐⭐ | MCP for agent accessibility | `Accessibility/` |
| **CosyVoice 2** | ⭐⭐⭐ | FSQ tokenization | `Voice/` |

### Immediate Actions (Batch 4):

1. **MCP Integration** — Expose Hydrogen Element trees as navigation graphs for agent accessibility
2. **Landauer Framework** — Formalize information-theoretic precision in `proofs/Hydrogen/Information/`
3. **FSQ Pattern** — Apply finite scalar quantization to other bounded domains

### Cross-Batch Synergies:

| Earlier Paper | Batch 4 Paper | Synergy |
|---------------|---------------|---------|
| NumFuzz/Bean | Landauer | Physical justification for bounded types |
| FP4 Quantization | Landauer | Precision = measured information |
| LPM (AgentTorch) | Multimodal GUI | Agent ↔ UI interaction |

────────────────────────────────────────────────────────────────────────────────
                                                              // batch // 5
────────────────────────────────────────────────────────────────────────────────

## Batch 5: Program Synthesis, Spatial Memory, and 3D Worlds

### Paper 5.1: DESIGN2GARMENTCODE

**Source:** Zhejiang Universities + Style3D (Zhou et al., 2024)
**arXiv:** 2412.08603
**Domain:** Program Synthesis / Computer Graphics

#### Core Contribution

**Design2GarmentCode**: Turns design concepts into **parametric programs** (GarmentCode DSL)
via LMM-based program synthesis, achieving **centimeter-level precision**.

| Approach | Precision | Validity | Editability |
|----------|-----------|----------|-------------|
| Neural generation | Statistical | 65% SSR | Limited |
| **Program synthesis** | Exact | 100% SSR | Full |

#### Key Insight

> Use LLMs to generate **programs** (not patterns directly).

Programs provide:
- Precise geometric control
- Semantic meaning
- Editability
- Composability

#### Algorithms to Extract

**1. Neurosymbolic Pipeline:**
```
Multi-Modal Input (text/image/sketch)
         │
         ▼
    ┌─────────────┐
    │  MMUA       │  ← Understand design
    │  (LMM)      │
    └─────────────┘
         │
         ▼
    ┌─────────────┐
    │  DSL-GA     │  ← Synthesize program
    │  (Fine-tuned)│
    └─────────────┘
         │
         ▼
    DSL Program → Execute → Precise Output
```

**2. Parameter Quantization:**
```python
def quantize_parameter(value, param_type):
    """
    Quantize to bounded representations.
    
    Centimeter precision = λ = 100 scaling.
    """
    if isinstance(value, bool):
        return 0 if not value else 1
    elif isinstance(value, int):
        return value
    elif isinstance(value, float):
        return int(value * 100)  # λ = 100
    elif isinstance(value, Enum):
        return value.index()  # Discrete index
```

**3. Two-Agent System:**
```python
class DSL_GA:
    """DSL Generation Agent - synthesizes programs."""
    
    def generate_prompts(self, design):
        """Generate questions about design parameters."""
        return self.llm.prompt_synthesis(design)
    
    def synthesize_program(self, answers):
        """Generate DSL program from answers."""
        return self.llm.program_synthesis(answers)

class MMUA:
    """Multi-Modal Understanding Agent - interprets inputs."""
    
    def extract_features(self, input):
        """Extract topological and geometric features."""
        return self.lmm.feature_extraction(input)
    
    def answer_questions(self, prompts, features):
        """Answer DSL-GA's questions using features."""
        return self.lmm.qa(prompts, features)
```

#### Integration Points

```
src/Hydrogen/Synthesis/
  ├── DSLGeneration.purs       -- Program synthesis from intent
  ├── MultiModalInput.purs     -- Text/image/sketch handling
  └── ParametricSchema.purs    -- Schema as parametric programs

proofs/Hydrogen/Synthesis/
  ├── ProgramCorrectness.lean  -- Generated programs satisfy spec
  └── QuantizationBounds.lean  -- Parameter precision proofs
```

#### Hydrogen Applications

| GarmentCode | Hydrogen Schema |
|-------------|-----------------|
| Symbolic programs | Schema atoms |
| Design parameters | Atom properties |
| Body measurements | Context/dimensions |
| Garment assembly | Compound elements |
| Centimeter precision | Bounded types |

#### Direct Schema Mapping

```purescript
-- GarmentCode-style parametric Schema
data SchemaProgram
  = Component ComponentType Config
  | Compose SchemaProgram SchemaProgram
  | Configure Config SchemaProgram

-- Execute to get Element
execute :: SchemaProgram -> Context -> Element msg
execute (Component t cfg) ctx = renderComponent t cfg ctx
execute (Compose a b) ctx = overlay (execute a ctx) (execute b ctx)
execute (Configure cfg prog) ctx = execute prog (applyConfig cfg ctx)
```

#### Priority: ⭐⭐⭐⭐⭐ CRITICAL

**Exact pattern for Hydrogen: LLM + DSL = precise, editable design.**

────────────────────────────────────────────────────────────────────────────────

### Paper 5.2: MATERIAL_STATES_ZERO_SHOT

**Source:** University of Toronto, Vector Institute (Eppel et al., 2025)
**Domain:** Computer Vision / Material Segmentation

#### Core Contribution

Zero-shot material state segmentation by infusing natural image patterns into synthetic data.

| Aspect | Details |
|--------|---------|
| Problem | Collecting data for material states is complex |
| Solution | Extract patterns from real → map to synthetic |
| Dataset | 300,000 extracted textures |
| Domains | Food, soils, construction, plants, liquids |

#### States Covered

- Wet/Dry
- Infected/Healthy
- Cooked/Raw
- Burned/Unburned
- Ripe/Unripe

#### Integration Points (Brief)

```
src/Hydrogen/Material/
  └── StateSegmentation.purs   -- Material state classification
```

#### Priority: ⭐⭐ LOW

Domain-specific (materials), limited applicability to UI design system.

────────────────────────────────────────────────────────────────────────────────

### Paper 5.3: SPATIA_VIDEO_MEMORY

**Source:** Sydney, Microsoft Research, HKUST (Zhao et al., 2025)
**arXiv:** 2512.15716
**Domain:** Video Generation / 3D Memory

#### Core Contribution

**Spatia**: Video generation with **explicit 3D spatial memory** (point cloud).

| Metric | Previous SOTA | Spatia |
|--------|---------------|--------|
| WorldScore | 66.08 (Voyager) | 69.73 |
| Closed-loop PSNR | 17.66 | 19.38 |
| Camera Control | 85.95 | 75.66 |

#### Key Insight

Maintain an **explicit 3D point cloud** as spatial memory:
1. Generate video conditioned on point cloud
2. Update point cloud from generated frames
3. Repeat for long-horizon consistency

#### Algorithms to Extract

**1. Spatial Memory Update Loop:**
```python
def spatia_generate(initial_image, actions, n_iterations):
    """
    Generate long-horizon video with spatial memory.
    """
    # Initialize spatial memory from first image
    point_cloud = estimate_point_cloud(initial_image)
    
    all_frames = [initial_image]
    
    for i in range(n_iterations):
        # Render point cloud along camera path
        camera_path = actions[i].camera_trajectory
        projection = render_point_cloud(point_cloud, camera_path)
        
        # Retrieve reference frames (spatially relevant)
        references = retrieve_references(
            all_frames, 
            point_cloud, 
            camera_path,
            k=7  # Max 7 reference frames
        )
        
        # Generate video chunk conditioned on projection + refs
        chunk = video_model(
            conditioning=projection,
            references=references,
            text=actions[i].text
        )
        
        # Update spatial memory with new frames
        point_cloud = update_point_cloud(
            point_cloud, 
            chunk,
            exclude_dynamic=True  # SAM2 segmentation
        )
        
        all_frames.extend(chunk)
    
    return all_frames
```

**2. Reference Frame Retrieval:**
```python
def retrieve_references(candidates, point_cloud, target_poses, k=7, threshold=0.1):
    """
    Select spatially relevant frames based on 3D IoU.
    """
    references = []
    
    for target_pose in target_poses:
        target_pc = render_view(point_cloud, target_pose)
        
        best_score, best_frame = 0, None
        for frame, frame_pc in candidates:
            # Compute 3D IoU between point clouds
            registered = register_point_clouds(frame_pc, target_pc)
            iou = compute_3d_iou(target_pc, registered)
            
            if iou > best_score and iou > threshold:
                best_score = iou
                best_frame = frame
        
        if best_frame is not None:
            references.append(best_frame)
    
    return references[:k]
```

**3. Dynamic-Static Disentanglement:**
```python
def update_point_cloud(pc, new_frames, exclude_dynamic=True):
    """
    Update point cloud, excluding dynamic entities.
    """
    if exclude_dynamic:
        # Segment dynamic entities with SAM2
        masks = sam2_track(new_frames)
        static_frames = apply_masks(new_frames, ~masks)
    else:
        static_frames = new_frames
    
    # Reconstruct point cloud from static regions only
    new_pc = reconstruct_point_cloud(static_frames)
    
    # Merge with existing
    return merge_point_clouds(pc, new_pc)
```

#### Integration Points

```
src/Hydrogen/Spatial/
  ├── PointCloudMemory.purs    -- 3D spatial memory
  ├── ViewRetrieval.purs       -- Reference frame selection
  ├── DynamicStatic.purs       -- Entity disentanglement
  └── CameraControl.purs       -- Explicit camera trajectories

proofs/Hydrogen/Spatial/
  ├── MemoryConsistency.lean   -- Closed-loop consistency proofs
  └── IoUProperties.lean       -- 3D IoU is a metric
```

#### Hydrogen Applications

| Component | Application |
|-----------|-------------|
| Spatial memory | Scene state persistence |
| Reference retrieval | Temporal consistency in animations |
| Dynamic-static split | Separate UI state from layout |
| Camera control | Viewport transformations |

#### Priority: ⭐⭐⭐⭐ HIGH

Spatial memory pattern directly applicable to 3D UI and animations.

────────────────────────────────────────────────────────────────────────────────

### Paper 5.4: WORLDGEN_3D

**Source:** Meta Reality Labs (Wang et al., 2025)
**arXiv:** 2511.16825
**Domain:** 3D Generation / Game Development

#### Core Contribution

**WorldGen**: Text → traversable, interactive 3D worlds.

Four-stage pipeline:
1. **Scene Planning:** LLM → procedural blockout → navmesh
2. **Reconstruction:** Image-to-3D (AssetGen2)
3. **Decomposition:** AutoPartGen for objects
4. **Enhancement:** Per-object refinement

#### Key Insight

**Hybrid generation:**
| Component | Method | Purpose |
|-----------|--------|---------|
| Layout | Procedural | Functional constraints |
| Details | Diffusion | Visual richness |
| Objects | Compositional | Editability |

#### Algorithms to Extract

**1. LLM → Procedural Parameters:**
```python
def plan_scene(text_prompt, llm):
    """
    LLM interprets prompt into procedural generation parameters.
    """
    # LLM extracts semantic structure
    scene_spec = llm.interpret(text_prompt)
    
    # Map to procedural parameters
    params = {
        'terrain': scene_spec.terrain_type,
        'buildings': scene_spec.building_specs,
        'vegetation': scene_spec.vegetation_density,
        'paths': scene_spec.connectivity
    }
    
    # Generate blockout
    blockout = procedural_generate(params)
    
    # Extract navmesh
    navmesh = extract_navmesh(blockout)
    
    return blockout, navmesh
```

**2. Navmesh-Conditioned Generation:**
```python
def reconstruct_scene(blockout, navmesh, reference_image):
    """
    Generate detailed scene while preserving traversability.
    """
    # Image-to-3D for base mesh
    base_mesh = assetgen2(reference_image)
    
    # Warp to fit navmesh constraints
    constrained_mesh = navmesh_constrain(base_mesh, navmesh)
    
    # Generate textures
    textures = texture_generate(constrained_mesh)
    
    return constrained_mesh, textures
```

#### Integration Points

```
src/Hydrogen/World/
  ├── ProceduralLayout.purs    -- LLM → procedural params
  ├── NavmeshConstrained.purs  -- Traversability constraints
  └── SceneDecomposition.purs  -- Object extraction
```

#### Priority: ⭐⭐⭐ MEDIUM

Relevant for 3D UI environments, not immediate 2D focus.

────────────────────────────────────────────────────────────────────────────────

### Paper 5.5: INTERACTIVE_GAME_VIDEO

**Source:** HKU, HKUST, Kuaishou (Yu et al., 2025)
**arXiv:** 2503.17359
**Domain:** Position Paper / Generative Game Engines

#### Core Contribution

Position paper: **Interactive Generative Video (IGV)** is foundation for
**Generative Game Engines (GGE)**.

#### Maturity Roadmap (L0-L4)

| Level | Description | Capability |
|-------|-------------|------------|
| L0 | Single prompt | Static generation |
| L1 | Multiple prompts | Sequential generation |
| L2 | Basic control | Action-conditioned |
| L3 | World model | Physics + memory |
| L4 | Full GGE | Reasoning + planning |

#### Four Core IGV Capabilities

1. **User Control** — Actions affect generated content
2. **Memory** — Video context retention
3. **Physics** — World rule understanding
4. **Causal Reasoning** — Action-consequence understanding

#### Integration Points (Brief)

```
src/Hydrogen/Interactive/
  └── GenerativeEngine.purs    -- IGV-style generation loop
```

#### Priority: ⭐⭐ LOW

Position paper, no concrete algorithms. Conceptual framework only.

────────────────────────────────────────────────────────────────────────────────
                                               // batch 5 // integration // summary
────────────────────────────────────────────────────────────────────────────────

## Batch 5 Integration Summary

| Paper | Priority | Key Takeaway | Integration Target |
|-------|----------|--------------|-------------------|
| **Design2GarmentCode** | ⭐⭐⭐⭐⭐ | LLM + DSL = precise design | `Synthesis/` |
| **Material States** | ⭐⭐ | Zero-shot segmentation | Low priority |
| **Spatia** | ⭐⭐⭐⭐ | 3D spatial memory | `Spatial/` |
| **WorldGen** | ⭐⭐⭐ | Hybrid procedural + generative | `World/` |
| **IGV Position** | ⭐⭐ | Maturity roadmap concept | Conceptual only |

### Immediate Actions (Batch 5):

1. **Design2GarmentCode Pattern** — Implement Schema as parametric programs with LLM synthesis
2. **Spatial Memory** — Study point cloud persistence for UI state
3. **Hybrid Generation** — Combine procedural constraints with generative detail

### Cross-Batch Synergies:

| Earlier Paper | Batch 5 Paper | Synergy |
|---------------|---------------|---------|
| NumFuzz/Bean | Design2GarmentCode | Bounded parameters from program synthesis |
| Effect Inference | Design2GarmentCode | Infer effects of synthesized programs |
| PAN World Model | Spatia | Both use latent + explicit 3D |
| TeraAgent | WorldGen | Distributed world generation |

────────────────────────────────────────────────────────────────────────────────
                                                              // batch // 6
────────────────────────────────────────────────────────────────────────────────

## Batch 6: Voice, Animation, and Policy Alignment

### Paper 6.1: MinMo_Voice

**Source:** Alibaba FunAudioLLM (2025)
**arXiv:** 2501.06282
**Domain:** Multimodal LLM / Voice Interaction

#### Core Contribution

**MinMo**: ~8B parameter model for seamless voice interaction.

| Metric | Value |
|--------|-------|
| Speech-to-Text latency | ~100ms |
| Full-duplex latency | ~600-800ms |
| Training data | 1.4M hours |

#### Key Innovations

**1. Four-Stage Training:**
1. Speech-to-Text alignment (understanding)
2. Text-to-Speech alignment (generation)
3. Speech-to-Speech alignment (end-to-end)
4. Duplex interaction alignment (real-time)

**2. Full-Duplex Conversation:**
- Simultaneous two-way communication
- User can interrupt while system speaks
- System responds to new queries mid-stream

**3. Voice Decoder:**
- Autoregressive streaming Transformer
- Mixes LLM hidden states with speech tokens
- Fixed ratio mixing (simpler than prior work)

#### Integration Points (Brief)

```
src/Hydrogen/Voice/
  ├── FullDuplex.purs          -- Two-way conversation
  └── StreamingDecoder.purs    -- AR speech generation
```

#### Priority: ⭐⭐⭐ MEDIUM

Relevant for future voice UI, not immediate rendering focus.

────────────────────────────────────────────────────────────────────────────────

### Paper 6.2: VA_PI_PIXEL_AWARE_AR

**Source:** HUST, NUS (Liao et al., 2025)
**arXiv:** 2512.19680
**Domain:** Generative Models / RL Alignment

#### Core Contribution

**VA-π**: Variational Policy Alignment for pixel-aware autoregressive generation.

| Metric | Before | After VA-π |
|--------|--------|------------|
| FID | 14.36 | 7.65 |
| IS | 86.55 | 116.70 |
| Training | Full | 1% data, 25 min |

#### Key Insight

**The Off-Manifold Problem:**
- Tokenizers train on clean images (pixel reconstruction)
- AR generators train on token likelihood only
- Result: "off-manifold" tokens — high likelihood, low pixel quality

**Solution:** Formulate as variational optimization with ELBO.

#### Algorithms to Extract

**1. VA-π ELBO:**
```
log p(x) ≥ E[q(z|x)] [log p(x|z)] - KL[q(z|x) || p(z)]

Where:
  x = pixel image (rendered output)
  z = token sequence (Element spec)
  q(z|x) = encoder (Schema)
  p(x|z) = decoder (Renderer)
  p(z) = generator (Element builder)
```

**2. RL Alignment:**
```python
def va_pi_update(generator, tokenizer, image):
    """
    Variational Policy Alignment.
    """
    # Encode to tokens
    z = tokenizer.encode(image)
    
    # Add context noise
    z_noisy = corrupt(z, ratio=0.1)
    
    # Teacher-forcing forward
    logits = generator(z_noisy)
    
    # Sample tokens
    z_sample = sample(logits)
    
    # Decode to image
    x_recon = tokenizer.decode(z_sample)
    
    # Compute reconstruction reward
    reward = similarity(image, x_recon)
    
    # GRPO update
    generator = grpo_update(generator, z_sample, reward)
    
    # Regularize with token likelihood
    generator = ce_regularize(generator, logits, z)
    
    return generator
```

#### Integration Points

```
src/Hydrogen/Alignment/
  ├── VariationalPolicy.purs   -- VA-π alignment
  ├── ReconstructionReward.purs -- Pixel-space rewards
  └── OffManifold.purs         -- Manifold detection

proofs/Hydrogen/Alignment/
  ├── ELBODerivation.lean      -- ELBO derivation
  └── ManifoldBounds.lean      -- On-manifold guarantees
```

#### Hydrogen Applications

| VA-π Concept | Hydrogen Equivalent |
|--------------|-------------------|
| Tokenizer | Schema definition |
| AR Generator | Element builder |
| Pixel reconstruction | Rendered output |
| Off-manifold tokens | Invalid Elements |
| ELBO | Schema verification |

#### Schema-Element Alignment Pattern

```purescript
-- VA-π style alignment for Hydrogen
alignElement :: Schema -> Element -> ValidationResult
alignElement schema element = do
  -- Encode to canonical form
  canonical <- encode schema element
  
  -- Add noise/corruption (robustness)
  corrupted <- corrupt canonical
  
  -- Generate element
  generated <- buildElement corrupted
  
  -- Decode to rendered output
  rendered <- render generated
  
  -- Compute reconstruction reward
  reward <- schemaFidelity schema rendered
  
  -- Return alignment score
  pure (AlignmentScore reward)
```

#### Priority: ⭐⭐⭐⭐ HIGH

**Direct pattern for ensuring generated Elements stay on Schema manifold.**

────────────────────────────────────────────────────────────────────────────────

### Paper 6.3: TTM_VIDEO_MOTION

**Source:** Technion, NVIDIA (Singer et al., 2025)
**arXiv:** 2511.08633
**Domain:** Video Generation / Motion Control

#### Core Contribution

**Time-to-Move (TTM)**: Training-free, plug-and-play motion control for I2V models.

| Capability | Details |
|------------|---------|
| Training | None required |
| Backbone | Any I2V model |
| Control | Joint motion + appearance |

#### Key Innovation: Dual-Clock Denoising

Different noise levels for different regions:

| Region | Noise Level | Behavior |
|--------|-------------|----------|
| Masked (controlled) | Strong (tstrong) | Follows motion signal |
| Unmasked (background) | Weak (tweak) | Natural generation |

#### Algorithms to Extract

**1. Motion Signal from User Interaction:**
```python
def generate_motion_signal(image, mask_sequence, trajectory):
    """
    Generate crude animation from drag/trajectory.
    """
    # Forward warp image along trajectory
    warped = forward_warp(image, trajectory)
    
    # Apply mask sequence
    motion_signal = apply_masks(warped, mask_sequence)
    
    # Simple inpainting for disocclusion
    motion_signal = inpaint_holes(motion_signal)
    
    return motion_signal
```

**2. Dual-Clock Denoising:**
```python
def dual_clock_denoise(I, Vw, M, tweak, tstrong):
    """
    Region-dependent denoising.
    
    tweak: noise level for background (high, e.g. 0.8)
    tstrong: noise level for controlled regions (low, e.g. 0.4)
    """
    # Initialize from warped reference at tweak
    xt = add_noise(Vw, tweak)
    
    for t in range(tweak, 0, -1):
        # Standard denoising
        x_pred = denoiser(xt, t, I)
        
        if t >= tstrong:
            # Override masked regions with warped reference
            xw_tm1 = add_noise(Vw, t-1)
            xt = (1 - M) * x_pred + M * xw_tm1
        else:
            # Standard sampling for all
            xt = x_pred
    
    return xt
```

#### Integration Points

```
src/Hydrogen/Animation/
  ├── MotionSignal.purs        -- User interaction → motion
  ├── DualClock.purs           -- Region-dependent control
  └── TrainingFree.purs        -- Plug-and-play adaptation

proofs/Hydrogen/Animation/
  └── DualClockCorrectness.lean -- Dual-clock preserves quality
```

#### Hydrogen Applications

| TTM Concept | Hydrogen Equivalent |
|-------------|-------------------|
| Motion signal | Animation trajectory |
| Dual-clock | Region-based interpolation |
| Mask regions | Element hierarchy |
| Appearance preservation | Style persistence |

#### Animation System Pattern

```purescript
-- TTM-style animation in Hydrogen
animateElement :: 
     Element msg              -- Source element
  -> Trajectory               -- Motion path
  -> AnimationMask            -- Controlled regions
  -> AnimationConfig          -- tweak, tstrong params
  -> Stream (Element msg)     -- Animated frames

data AnimationConfig = AnimationConfig
  { tWeak :: Float            -- Background noise (0.7-0.9)
  , tStrong :: Float          -- Controlled noise (0.3-0.5)
  , interpolation :: InterpolationType
  }
```

#### Priority: ⭐⭐⭐⭐ HIGH

**Training-free animation control directly applicable to Hydrogen UI.**

────────────────────────────────────────────────────────────────────────────────

### Paper 6.4: EFFICIENT_OBJECT_RECONSTRUCTION

**Source:** Zhejiang, Brown, Style3D (Gao et al., 2025)
**Venue:** SIGGRAPH Asia 2025
**Domain:** 3D Reconstruction / Inverse Rendering

#### Core Contribution

Active area lighting for efficient BRDF/material capture.

| Metric | Improvement |
|--------|-------------|
| Relighting PSNR | +3 dB |
| Photos required | 1/5 |

#### Key Insight

Area lights provide wider lighting angle coverage per photo:
- Better material roughness estimation
- More accurate BRDF reconstruction
- Works with mesh and 3D Gaussian Splatting

#### Integration Points (Brief)

```
src/Hydrogen/Material/
  └── AreaLightReconstruction.purs -- BRDF capture
```

#### Priority: ⭐⭐ LOW

Domain-specific (3D capture), limited applicability to UI rendering.

────────────────────────────────────────────────────────────────────────────────

### Paper 6.5: DREAMONTAGE_VIDEO

**Source:** ByteDance (Liu et al., 2025)
**arXiv:** 2512.21252
**Domain:** Video Generation / One-Shot Video

#### Core Contribution

**DreaMontage**: Seamless long-duration one-shot video from diverse inputs.

Three innovations:
1. **Intermediate-conditioning** in DiT with Adaptive Tuning
2. **Visual Expression SFT** + Tailored DPO
3. **Segment-wise Auto-Regressive (SAR)** inference

#### Key Insight

"One-shot" (long take) cinematic technique is expensive in reality.
Generative models can create seamless transitions across keyframes.

#### Integration Points (Brief)

```
src/Hydrogen/Video/
  └── LongFormGeneration.purs  -- SAR inference for long videos
```

#### Priority: ⭐⭐ LOW

Video generation specific, limited applicability to UI design system.

────────────────────────────────────────────────────────────────────────────────
                                               // batch 6 // integration // summary
────────────────────────────────────────────────────────────────────────────────

## Batch 6 Integration Summary

| Paper | Priority | Key Takeaway | Integration Target |
|-------|----------|--------------|-------------------|
| **MinMo** | ⭐⭐⭐ | Full-duplex voice | `Voice/` |
| **VA-π** | ⭐⭐⭐⭐ | Schema-Element alignment | `Alignment/` |
| **TTM** | ⭐⭐⭐⭐ | Training-free animation | `Animation/` |
| **Efficient Reconstruction** | ⭐⭐ | Area light BRDF | Low priority |
| **DreaMontage** | ⭐⭐ | Long-form video | Low priority |

### Immediate Actions (Batch 6):

1. **VA-π Alignment** — Implement ELBO-based Schema-Element verification
2. **TTM Animation** — Add dual-clock denoising for region-based animation control
3. **Full-Duplex Voice** — Study for future voice-enabled UI

### Cross-Batch Synergies:

| Earlier Paper | Batch 6 Paper | Synergy |
|---------------|---------------|---------|
| NumFuzz/Bean | VA-π | Both address generator-decoder alignment |
| Design2GarmentCode | VA-π | Program synthesis + pixel verification |
| Spatia | TTM | Spatial memory + motion control |
| CosyVoice 2 | MinMo | Complementary TTS approaches |

────────────────────────────────────────────────────────────────────────────────
                                                              // batch // 7
────────────────────────────────────────────────────────────────────────────────

## Batch 7: Agent Communication, Video Control, and Domain-Specific Applications

### Paper 7.1: AI_MOTHER_TONGUE

**Source:** PARRAWA AI (Liu Hung Ming, 2025)
**arXiv:** 2507.10566
**Domain:** Multi-Agent RL / Emergent Communication

#### Core Contribution

**AI Mother Tongue (AIM)**: Framework for emergent communication in MARL using
VQ-VAE as endogenous symbol system. **No artificial inductive biases required.**

#### Key Insight

> Neural networks inherently encode the potential for efficient communication.
> Research should shift towards providing symbolic tools rather than inductive mechanisms.

#### Algorithms to Extract

**1. VQ-VAE Codebook as Shared Vocabulary:**
```python
def quantize(ze, codebook):
    """
    Quantize continuous representation to discrete symbol.
    
    Codebook = {e_k}^K for K symbols.
    """
    # Find nearest codebook entry
    distances = [||ze - e_k||² for e_k in codebook]
    k = argmin(distances)
    
    # Return discrete symbol
    return k, codebook[k]
```

**2. Reflection Strategies (Theory of Mind):**
```python
def reflection_loss(agent, opponent_action, joint_reward):
    """
    Agents predict opponent behavior → Theory of Mind.
    """
    # Predict opponent's reward from my action
    predicted_opp_reward = agent.predict_opponent_reward(agent.action)
    
    # Loss encourages accurate prediction
    return mse(predicted_opp_reward, opponent_actual_reward)
```

#### Integration Points

```
src/Hydrogen/Agent/Communication/
  ├── VQCodebook.purs          -- Shared symbol vocabulary
  ├── ReflectionStrategy.purs  -- Theory of Mind
  └── EmergentProtocol.purs    -- No predefined structure

proofs/Hydrogen/Agent/Communication/
  └── NashEquilibrium.lean     -- Semantic convergence proofs
```

#### Hydrogen Applications

| Need | AIM Solution |
|------|--------------|
| Billion-agent communication | VQ-VAE codebook as shared vocabulary |
| Decentralized coordination | No centralized training required |
| Scalable protocols | Emergent without predefined structures |

#### Priority: ⭐⭐⭐⭐ HIGH

**Directly applicable to Hydrogen's agent communication layer.**

────────────────────────────────────────────────────────────────────────────────

### Paper 7.2: WAN_ANIMATE

**Source:** Alibaba HumanAIGC (2025)
**arXiv:** 2509.14055
**Domain:** Character Animation / Video Generation

#### Core Contribution

**Wan-Animate**: Unified character animation + replacement.
- **Animation Mode:** Reference video → animate static image
- **Replacement Mode:** Integrate animated character into video

#### Key Innovation

Skeleton + face control combined with relighting LoRA for environmental integration.

#### Priority: ⭐⭐ LOW

Domain-specific (character animation), not immediate UI focus.

────────────────────────────────────────────────────────────────────────────────

### Paper 7.3: BINDWEAVE_VIDEO

**Source:** ByteDance + USTC (Li et al., 2025)
**arXiv:** 2510.00438
**Domain:** Video Generation / Subject Consistency

#### Core Contribution

**BindWeave**: Subject-consistent video via **MLLM reasoning** before generation.

| Problem | Solution |
|---------|----------|
| Identity confusion | MLLM binds text to visual entities |
| Action misplacement | Deep cross-modal reasoning |
| Attribute blending | Role disentanglement |

#### Key Insight

Use MLLM (Qwen2.5-VL) as intelligent instruction parser, not just separate encoders.

#### Priority: ⭐⭐⭐ MEDIUM

Relevant for future video generation, not immediate rendering focus.

────────────────────────────────────────────────────────────────────────────────

### Paper 7.4: ANCHORWEAVE_VIDEO

**Source:** UNC Chapel Hill + NTU + AI2 (Wang et al., 2026)
**arXiv:** 2602.14941
**Domain:** Video Generation / World Consistency

#### Core Contribution

**AnchorWeave**: World-consistent video via **local geometric memories**.

| Approach | Problem |
|----------|---------|
| Global 3D memory | Errors accumulate → ghosting |
| **Local memories** | Clean signals, reconcile via controller |

#### Key Algorithm: Coverage-Driven Retrieval

```python
def retrieve_anchors(target_trajectory, memory_bank, max_anchors=7):
    """
    Select local memories maximizing visibility coverage.
    """
    selected = []
    uncovered = compute_visibility(target_trajectory)
    
    while len(selected) < max_anchors and uncovered.any():
        # Find memory maximizing additional coverage
        best_memory = max(memory_bank, key=lambda m: coverage(m, uncovered))
        
        if coverage(best_memory, uncovered) < threshold:
            break
            
        selected.append(best_memory)
        uncovered = update_coverage(uncovered, best_memory)
    
    return selected
```

#### Integration Points

```
src/Hydrogen/Spatial/
  └── LocalMemory.purs         -- Per-frame local memories

proofs/Hydrogen/Spatial/
  └── CoverageMaximization.lean -- Coverage-driven retrieval proofs
```

#### Priority: ⭐⭐⭐ MEDIUM

Related to Spatia, provides complementary local memory approach.

────────────────────────────────────────────────────────────────────────────────

### Paper 7.5: ATI_TRAJECTORY_VIDEO

**Source:** ByteDance (Wang et al., 2025)
**arXiv:** 2505.22944
**Domain:** Video Generation / Motion Control

#### Core Contribution

**ATI (Any Trajectory Instruction)**: Unified motion control via trajectory points.

| Motion Type | Representation |
|-------------|----------------|
| Camera | Points at infinity |
| Object translation | Bounding box corners |
| Local deformation | Keypoints on object |

#### Key Algorithm: Gaussian Motion Injection

```python
def inject_motion(image_latent, trajectory, sigma=1/440):
    """
    Inject motion via Gaussian-weighted feature distribution.
    """
    # Sample feature at trajectory start
    f = bilinear_sample(image_latent, trajectory[0])
    
    # For each frame, distribute feature along trajectory
    guided_features = []
    for t, (x_t, y_t) in enumerate(trajectory):
        # Gaussian mask centered at trajectory position
        mask = gaussian_2d(x_t, y_t, sigma)
        guided_features.append(f * mask)
    
    return stack(guided_features)
```

#### Priority: ⭐⭐⭐ MEDIUM

Unified trajectory representation applicable to animation system.

────────────────────────────────────────────────────────────────────────────────

### Paper 7.6: FIRE_X_SIMULATION

**Source:** Kiel University + KAUST (Wrede et al., 2025)
**Venue:** SIGGRAPH Asia 2025
**Domain:** Physical Simulation / Combustion

#### Core Contribution

Multi-species fire simulation with stoichiometric heat release:
- Premixed and diffusive flames
- Extinguishing scenarios
- SPH-grid hybrid

#### Priority: ⭐ VERY LOW

Domain-specific physics simulation, not applicable to UI.

────────────────────────────────────────────────────────────────────────────────

### Paper 7.7: MATERIAL_STATE_SEGMENTATION

**Source:** University of Toronto, Vector Institute (Eppel et al., 2024)
**arXiv:** 2403.03309
**Domain:** Computer Vision / Material Segmentation

#### Core Contribution

**MatSeg**: Zero-shot material state segmentation via pattern infusion.

| Component | Details |
|-----------|---------|
| Benchmark | 1,220 real-world images |
| Training data | Synthetic with real patterns infused |
| Output | 128-d descriptor per pixel |
| Accuracy | 0.92 triplet accuracy (vs 0.69 SAM) |

#### Key Algorithm: Pattern Infusion

```python
def extract_pattern_map(image):
    """
    Extract material-correlated pattern from real image.
    """
    # Select random channel
    channel = random.choice(['R', 'G', 'B', 'H', 'S', 'V'])
    values = image[channel]
    
    # Apply random ramp threshold
    t_low, t_high = random.uniform(0, 1), random.uniform(0, 1)
    t_low, t_high = min(t_low, t_high), max(t_low, t_high)
    
    # Linear interpolation
    pattern = (values - t_low) / (t_high - t_low)
    pattern = clamp(pattern, 0, 1)
    
    return pattern
```

#### Integration Points

```
src/Hydrogen/Material/
  ├── PatternInfusion.purs     -- Real → synthetic pattern transfer
  └── MaterialDescriptor.purs  -- 128-d per-pixel embeddings
```

#### Hydrogen Applications

| Need | MatSeg Solution |
|------|-----------------|
| Material recognition | 128-d descriptor similarity |
| Zero-shot generalization | Pattern infusion training |
| Soft boundaries | Handles gradual transitions |

#### Priority: ⭐⭐⭐ MEDIUM

Applicable to material-aware rendering and asset generation.

────────────────────────────────────────────────────────────────────────────────

### Papers 7.8-7.11: Domain-Specific (Low Priority)

| Paper | Domain | Priority |
|-------|--------|----------|
| KNOTS_CLOTH | Cloth/knot simulation | ⭐ |
| FASHION_R2R | Rendered→real fashion | ⭐ |
| EMBROIDERY_LORA | Embroidery synthesis | ⭐ |
| OPTIMAL_CLOTH_RESOLUTION | Cloth mesh resolution | ⭐ |

These are highly domain-specific to fashion/textile applications and have
limited applicability to the core Hydrogen design system.

────────────────────────────────────────────────────────────────────────────────
                                               // batch 7 // integration // summary
────────────────────────────────────────────────────────────────────────────────

## Batch 7 Integration Summary

| Paper | Priority | Key Takeaway | Integration Target |
|-------|----------|--------------|-------------------|
| **AI Mother Tongue** | ⭐⭐⭐⭐ | VQ-VAE emergent communication | `Agent/Communication/` |
| **Wan-Animate** | ⭐⭐ | Character animation | Low priority |
| **BindWeave** | ⭐⭐⭐ | MLLM for subject consistency | `Video/` |
| **AnchorWeave** | ⭐⭐⭐ | Local spatial memories | `Spatial/` |
| **ATI** | ⭐⭐⭐ | Unified trajectory control | `Animation/` |
| **Fire-X** | ⭐ | Fire simulation | Not applicable |
| **MatSeg** | ⭐⭐⭐ | Material state segmentation | `Material/` |
| **Fashion/Textile** | ⭐ | Domain-specific | Not applicable |

────────────────────────────────────────────────────────────────────────────────
                                                    // final // synthesis
────────────────────────────────────────────────────────────────────────────────

## Final Synthesis: Priority Rankings

### ⭐⭐⭐⭐⭐ CRITICAL (Implement Immediately)

| Paper | Key Contribution | Integration Target |
|-------|------------------|-------------------|
| **NumFuzz/Bean** | Graded monads for error bounds | `Schema/Numeric/` |
| **Large Population Models** | Billion-agent architecture | `Agent/` |
| **TeraAgent** | 501B agent scale-out | `Agent/Distributed/` |
| **Effect Inference** | Sound+complete effect inference | `Schema/Effect/` |
| **Design2GarmentCode** | LLM + DSL = precise design | `Synthesis/` |

### ⭐⭐⭐⭐ HIGH (Implement Soon)

| Paper | Key Contribution | Integration Target |
|-------|------------------|-------------------|
| **FP4 Quantization** | NVFP4 GPU efficiency | `GPU/Quantization/` |
| **Online Submodular** | Streaming allocation | `Optimize/` |
| **Landauer Precision** | Information-theoretic bounds | `Information/` |
| **Multimodal GUI** | MCP for agent accessibility | `Accessibility/` |
| **VA-π** | Schema-Element alignment | `Alignment/` |
| **TTM** | Training-free animation | `Animation/` |
| **Spatia** | 3D spatial memory | `Spatial/` |
| **AI Mother Tongue** | Emergent agent communication | `Agent/Communication/` |

### ⭐⭐⭐ MEDIUM (Evaluate Later)

| Paper | Key Contribution |
|-------|------------------|
| GAIA-2 | Flow matching, video tokenizer |
| PAN World Model | GLP architecture |
| Qwen2.5-Omni | Thinker-Talker |
| CosyVoice 2 | FSQ tokenization |
| WorldGen | Hybrid procedural + generative |
| DeepSeek-R1 | GRPO for reasoning |
| BindWeave | MLLM subject consistency |
| AnchorWeave | Local memory consistency |
| ATI | Unified trajectory control |
| MatSeg | Material state segmentation |

### ⭐⭐ LOW and ⭐ VERY LOW (Reference Only)

Domain-specific papers (fire, fashion, cloth, embroidery, etc.) — useful for
specific applications but not core to the design system.

────────────────────────────────────────────────────────────────────────────────
                                                    // implementation // roadmap
────────────────────────────────────────────────────────────────────────────────

## Implementation Roadmap

### Phase 1: Theoretical Foundation (Weeks 1-4)

**Goal:** Establish graded type system for bounded Schema atoms.

```
proofs/Hydrogen/Schema/Numeric/
  ├── GradedMonad.lean         -- M[ε] forward error (NumFuzz)
  ├── GradedComonad.lean       -- D^r backward error (Bean)
  ├── RelativePrecision.lean   -- RP metric (Olver model)
  ├── Primitives.lean          -- add/mul/div typing rules
  └── EffectInference.lean     -- PropLogic constraint solving
```

**Papers:** NumFuzz, Bean, Effect Inference

### Phase 2: Agent Infrastructure (Weeks 5-8)

**Goal:** Build distributed agent runtime for billion-scale.

```
src/Hydrogen/Agent/
  ├── Population.purs          -- LPM-style tensorized updates
  ├── Distributed.purs         -- TeraAgent scale-out
  ├── DeltaEncoding.purs       -- State compression
  ├── Communication/
  │   ├── VQCodebook.purs      -- AIM symbol vocabulary
  │   └── EmergentProtocol.purs
  └── SpatialPartition.purs    -- Space partitioning
```

**Papers:** Large Population Models, TeraAgent, AI Mother Tongue

### Phase 3: GPU Efficiency (Weeks 9-12)

**Goal:** Implement FP4 quantization for efficient rendering.

```
src/Hydrogen/GPU/Quantization/
  ├── FP4.purs                 -- E2M1 format
  ├── NVFP4.purs               -- Block size 16, E4M3 scale
  ├── SplitRounding.purs       -- Forward RtN, Backward SR
  └── InformationPrecision.purs -- Landauer-informed

proofs/Hydrogen/GPU/Quantization/
  ├── FP4Format.lean
  └── QuantizationBounds.lean
```

**Papers:** FP4 Quantization, FP4 All The Way, Landauer Precision

### Phase 4: Schema Synthesis (Weeks 13-16)

**Goal:** Enable LLM-based Schema generation with precision guarantees.

```
src/Hydrogen/Synthesis/
  ├── DSLGeneration.purs       -- Program synthesis
  ├── MultiModalInput.purs     -- Text/image/sketch
  └── ParametricSchema.purs    -- Schema as programs

src/Hydrogen/Alignment/
  ├── VariationalPolicy.purs   -- VA-π alignment
  └── ReconstructionReward.purs
```

**Papers:** Design2GarmentCode, VA-π

### Phase 5: Animation & Spatial (Weeks 17-20)

**Goal:** Add animation primitives and spatial memory.

```
src/Hydrogen/Animation/
  ├── DualClock.purs           -- TTM region control
  ├── TrajectoryUnified.purs   -- ATI format
  └── MotionSignal.purs

src/Hydrogen/Spatial/
  ├── PointCloudMemory.purs    -- Spatia
  ├── LocalMemory.purs         -- AnchorWeave
  └── ViewRetrieval.purs
```

**Papers:** TTM, ATI, Spatia, AnchorWeave

### Phase 6: Accessibility & Voice (Weeks 21-24)

**Goal:** Enable agent accessibility and voice interfaces.

```
src/Hydrogen/Accessibility/
  ├── MCP.purs                 -- Model Context Protocol
  ├── NavigationGraph.purs     -- Element tree as nav graph
  └── ToolExposure.purs

src/Hydrogen/Voice/
  ├── FSQ.purs                 -- Finite Scalar Quantization
  └── StreamingTTS.purs
```

**Papers:** Multimodal GUI, CosyVoice 2, MinMo

────────────────────────────────────────────────────────────────────────────────
                                                               // batch // 8 // ref
────────────────────────────────────────────────────────────────────────────────

## Batch 8: Rendering Primitives, Quantization, and Constraint Transport

**Document:** `docs/BATCH_8_RENDERING_PRIMITIVES.md`
**Papers Analyzed:** 7
**Focus:** SDF rendering, FP4 quantization, depth-ray geometry, fluid simulation

### Papers

| # | Paper | Priority | Domain |
|---|-------|----------|--------|
| 8.1 | Distance Field Textures (Valve) | ⭐⭐⭐⭐⭐ | Text/icon rendering |
| 8.2 | Ray Tracing SDF Grids (NVIDIA) | ⭐⭐⭐⭐ | 3D SDF ray tracing |
| 8.3 | NVFP4 Pretraining | ⭐⭐⭐⭐ | FP4 training at scale |
| 8.4 | Four Over Six Adaptive Scaling | ⭐⭐⭐⭐ | Adaptive block scaling |
| 8.5 | Depth Anything 3 | ⭐⭐⭐⭐ | Depth-ray geometry |
| 8.6 | Stream Function Solver | ⭐⭐⭐ | Fluid simulation |
| 8.7 | VA-π Pixel Alignment | ⭐⭐⭐ | Token-pixel alignment |

### Key Insights

1. **SDF is the correct representation for resolution-independent rendering**
   - Distance is linear (interpolates correctly), coverage is not
   - 64:1 compression with quality preservation
   - All visual effects (outline, glow, shadow) are threshold operations

2. **FP4 quantization requires four components working together**
   - Mixed precision (~15% BF16)
   - Random Hadamard Transform (Wgrad only)
   - 2D block scaling (16×16)
   - Stochastic rounding (gradients only)

3. **Depth + ray suffices for all 3D tasks**
   - No rotation matrices needed
   - Per-pixel rays preserve projection scale
   - Point cloud = element-wise fusion

4. **Divergence-free is constructible, not checkable**
   - `∇·(∇×Ψ) = 0` is mathematical identity
   - Solve for stream function, take curl
   - Result is divergence-free by construction

### Implementation Targets

See `docs/BATCH_8_RENDERING_PRIMITIVES.md` for complete implementation plan:
- Target 1: SDF Text Rendering (Week 1-2) — CRITICAL
- Target 2: FP4 Quantization Module (Week 2-3) — HIGH
- Target 3: Depth-Ray Spatial Types (Week 3-4) — HIGH
- Target 4: SDF Grid Ray Tracing (Week 4-5) — HIGH
- Target 5: Stream Function Types (Week 5-6) — MEDIUM

────────────────────────────────────────────────────────────────────────────────

*Council Deliberation Document*
*Session: 2026-02-26*
*Batches: 1-8 (Complete)*
*Papers Analyzed: 48*

────────────────────────────────────────────────────────────────────────────────
