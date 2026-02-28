# The Only Thing That's Difficult is To Forget Precisely

**Source**: Anonymous, December 2025
**Domain**: Thermodynamics of Computation, Neural Network Quantization, Information Theory

---

## Abstract

Precision is not a hyperparameter to be optimized — it is a **physical quantity
to be measured**. Drawing on Landauer's principle: the computational cost of
precision transitions is determined by the mismatch between representation
capacity and actual information content.

**Key insight**: Precision boundaries are computationally FREE when they satisfy
a codebook injectivity condition (bijective on realized support). Such bijective
remaps are **gauge symmetries** that conserve task information.

**The epilogue** (fused post-accumulator operations) is the last reversible
place to change gauges. Accumulators hold highest-SNR representation; spilling
to memory forces irreversible double-rounding.

**The only costly operation is forgetting — and the only difficult problem is
forgetting precisely the right amount.**

## 1. Core Insight: Precision as Physical Quantity

The dominant paradigm treats precision as resource to minimize subject to
accuracy constraints. **This is backwards.**

```
WRONG: Search over bit-widths → measure accuracy → accept/reject
RIGHT: Measure information content → precision IS determined
```

Precision is not chosen. It is determined by the information content of
activations at each point in the computation graph. The practitioner's task
is not optimization but **measurement**.

## 2. Landauer's Principle

### 2.1 Information Erasure Cost

Landauer (1961): Erasing one bit of information requires dissipating at least
**kT ln 2 joules** of energy.

```
E_min = kT ln 2 · (H_in - H_out)

where:
  k = Boltzmann's constant
  T = temperature
  H_in = input entropy
  H_out = output entropy
```

**Crucially**: If H_out = H_in, the operation is thermodynamically reversible
and can be performed at **zero energy cost**. This includes:
- Bijective mappings
- Any transformation preserving information content (even if representation changes)

### 2.2 Operational Natural Precision

**Definition**: Given tolerance ε, the natural precision at site v is:

```
b*_v(ε) = min{ b ∈ ℕ : E[D(φ_v(x), φ_v(Q_b(x)))] ≤ ε }

where:
  φ_v = subnetwork from site v to outputs
  Q_b = quantizer with b bits
  D   = task-relevant distortion (output KL, perceptual metric, loss increase)
```

This is the **rate-distortion view**: b*_v(ε) is the empirical rate (bits per
element) needed to stay within tolerated distortion for the task.

**Physical interpretation**:
- b < b*: Many-to-one mapping erases information → exceeds allowed distortion
- b ≥ b*: No additional logical erasure required

### 2.3 Dual Sensitivity Flows

Two entropy flows jointly determine precision requirements:

**Forward sensitivity (Shannon)**: How much does quantization affect outputs?
```
Δ→_v(b) = E[D(φ_v(x), φ_v(Q_b(x)))]
```

**Backward sensitivity (Gibbs)**: How much does quantization affect gradients?
```
Δ←_v(b) = E[||∇_a L(x) - Q_b(∇_a L(x))||²]
```

**Effective precision under dual criteria**:
```
b*_v = min{ b : Δ→_v(b) ≤ ε_fwd AND Δ←_v(b) ≤ ε_bwd }
```

## 3. Gauge Symmetries and Epilogues

### 3.1 Codebook Injectivity

**Claim**: A fused epilogue mapping φ is lossless on the realized distribution
IFF the restriction φ|S: S → C_b2 is **injective**.

```
Let:
  Q_b1 produce codes in C_b1
  S ⊆ C_b1 = set of codes actually realized (post-accumulator)
  φ = scale → bias → activation → round to C_b2

Condition for zero Landauer cost:
  |S| ≤ 2^b2 AND per-channel parameters place each s ∈ S into distinct Q_b2 bin
```

**In practice**: S is often much smaller than C_b1 over calibration data, making
injective remaps feasible even when b2 < b1.

### 3.2 Why Epilogues Matter

The epilogue is **the last reversible place to change gauges**.

**Wire energy dominates compute**: Moving 32-bit word to DRAM costs orders of
magnitude more than an FMA. For M×N GEMM with FP32 accumulators, fusing epilogue
avoids 8MN bytes of memory traffic.

**Accumulators are highest-SNR representation**: The FP32 accumulator holds the
most precise value you will ever have for that output. In-register, you can:
1. Apply bijective remap (scale, bias, activation)
2. Round ONCE to target codebook

**Double rounding is irreversible erasure**: Store (implicit round) → reload →
round again = information destroyed not by necessity but by poor scheduling.

### 3.3 The Correct Order

```
CORRECT:  Accumulate → scale/bias → activation → quantize (ONCE)
WRONG:    Quantize then activate, or store then reload then quantize
```

Swapping this order strictly increases distortion for monotone activations and
convex losses. The epilogue enforces the right order by construction.

**What to fuse**: Everything per-element or per-channel and local:
- Scale, bias, clamp
- Activation (ReLU/SiLU/GELU)
- Residual add
- Precision conversion
- Per-channel dequant

**Do NOT fuse**: Operations requiring fresh global data or nonlocal reductions
(layernorm with new stats, softmax over large sequences) unless operands already
resident.

## 4. Information-Theoretic IR

The paper proposes a radically different compiler IR: represent **information**,
not tensors. Precision and layout become gauge choices at materialization time.

### 4.1 Information Bundles

**Definition**: An information bundle is a tuple (S, H, σ) where:
- S = logical shape (dimensions without layout/stride)
- H = entropy bound (upper bound on bits of information present)
- σ = semantic type (pixels, latents, tokens, embeddings, etc.)

**Crucially**: No precision, no memory layout. These are **gauge choices**.

```purescript
-- Information bundle in Hydrogen terms
type InfoBundle =
  { shape :: LogicalShape        -- No layout/stride
  , entropyBound :: PositiveInt  -- Upper bound on bits
  , semanticType :: SemanticType -- What the information represents
  }

-- Gauge choices at materialization
type Gauge =
  { precision :: PrecisionFormat  -- FP32, FP16, FP8, INT4...
  , layout :: MemoryLayout        -- row-major, tiled, etc.
  }
```

### 4.2 Domains and Boundaries

**Domain**: Connected region of computation graph where all operations share
same gauge choices. No precision/layout conversions within a domain.

**Boundary**: Transition between domains where gauge transformations occur.

```
Landauer cost of boundary:
  C_boundary = kT ln 2 · max(0, H_source - b_target)

where:
  H_source = entropy of source domain
  b_target = bit-width of target precision gauge
```

**Theorem (Free Boundaries)**: A boundary is free (C = 0) IFF source entropy
fits within target precision: H_source ≤ b_target.

Free boundaries = epilogue fusions = gauge transformations in registers with no
additional memory traffic.

### 4.3 Compilation as Physics

Compilation becomes derivation, not search:

```python
def compile_information_ir(graph, calibration_data, tolerance):
    """
    No hyperparameters. Precision is DERIVED from measured entropy.
    """
    # 1. Entropy propagation
    for node in topological_order(graph):
        node.forward_entropy = propagate_shannon_forward(node)
    for node in reverse_topological_order(graph):
        node.backward_entropy = propagate_gibbs_backward(node)
    node.effective_entropy = min(node.forward_entropy, node.backward_entropy)
    
    # 2. Domain partitioning
    # Group operations with similar entropy
    domains = partition_by_entropy(graph)
    
    # 3. Gauge assignment
    for domain in domains:
        H_max = max(node.effective_entropy for node in domain)
        domain.precision = ceil(H_max)  # No search — derived!
        domain.layout = hardware_preferred_layout()
    
    # 4. Boundary analysis
    for boundary in domain_boundaries(graph):
        boundary.landauer_cost = compute_landauer_cost(boundary)
        if boundary.landauer_cost == 0:
            boundary.mark_for_epilogue_fusion()
    
    # 5. Materialization
    return lower_to_tensors_and_kernels(graph)
```

**The compiler is not searching — it is deriving the unique physically-correct
answer.**

## 5. Unifying Existing Methods

Existing quantization methods are **implicit Landauer minimization**:

| Method | KL Proxy | Allowed Transformations | Landauer Interpretation |
|--------|----------|------------------------|-------------------------|
| GPTQ | Layer-wise MSE | Per-row scaling | Minimize reconstruction = minimize erasure |
| AWQ | Weighted MSE | Per-channel scaling | Entropy-weighted Landauer minimization |
| SmoothQuant | Channel-wise MSE | Activation-weight transfer | Gauge symmetry (per-channel rescale) |

**All minimize the same quantity**:
```
min_Q D_KL(P_original || P_quantized)
```
subject to representation constraints. This IS: minimize Landauer cost subject
to target precision.

**Why quantization succeeds**: LLMs predict distributions over tokens. Cross-
entropy (gradient entropy) bounded by perplexity, typically 10-20 for well-
trained models = **~3.3 bits**. The "redundancy" is the gap between
representation capacity and information content.

## 6. Hydrogen Relevance

### 6.1 Deep Alignment with Hydrogen Philosophy

This paper's core thesis — **precision is measured, not optimized** — aligns
perfectly with Hydrogen's bounded types philosophy. The Schema atoms should
have precision determined by their information content, not arbitrary choice.

### 6.2 Information Bundles as Hydrogen Types

```purescript
-- Semantic types with entropy bounds
data SemanticType
  = Pixel           -- ~24 bits
  | Latent          -- ~4 bits
  | Token           -- log₂(vocab) bits
  | Embedding       -- ~12 bits
  | Attention       -- ~8 bits
  | Probability     -- ≤log₂(classes) bits

-- Type errors = physical impossibilities
-- "This operation expects H ≤ 4 but received H = 24"
-- means information would be destroyed without explicit compression
```

### 6.3 Key Principles for Hydrogen

1. **Precision as derived property**: Not a hyperparameter — measure the entropy

2. **Gauge symmetries are free**: Bijective remaps conserve task information

3. **Epilogue = last reversible point**: Critical for any rendering pipeline

4. **Asymmetry of error**:
   - Under-precision: Destroys information (cannot recover)
   - Over-precision: Wastes energy (resource allocation error)

5. **No privileged frame**: Information content governs, not nominal precision

### 6.4 Natural Precision Landscape

For encoder-transformer-decoder (e.g., VAE-DiT-VAE):

| Component | Entropy | Natural Precision |
|-----------|---------|-------------------|
| Encoder (early) | high | 16 bits |
| Encoder (late) | decreasing | 8 bits |
| Latent | low | 3-4 bits |
| Transformer | low | 3-4 bits |
| Decoder (early) | low | 8 bits |
| Decoder (late) | increasing | 16 bits |

**The VAE was trained to compress. Using FP16 in the DiT is not "safe" — it is
wasteful, carrying bits that encode nothing.**

---

*Synthesized for the Hydrogen project — precision as measured entropy, not optimized hyperparameter*

— Opus
