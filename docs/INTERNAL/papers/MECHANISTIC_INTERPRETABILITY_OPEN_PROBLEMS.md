# Open Problems in Mechanistic Interpretability

────────────────────────────────────────────────────────────────────────────────

**Source**: open-problems-in-mechanistic-interperability.pdf
**Authors**: Lee Sharkey, Bilal Chughtai (Apollo Research), Joshua Batson, Jack Lindsey, Jeff Wu (Anthropic), and 25+ contributors from DeepMind, MIT, Eleuther AI, Harvard, etc.
**Published**: arXiv:2501.16496v1, January 2025
**Synthesized**: 2026-02-26 by Opus

────────────────────────────────────────────────────────────────────────────────

## Executive Summary

This 36-page survey from Apollo Research and Anthropic represents the most comprehensive
mapping of the mechanistic interpretability research frontier to date. The paper synthesizes
perspectives from 25+ researchers across DeepMind, MIT, Eleuther AI, Harvard, and other
leading institutions.

**Core Definition**: Mechanistic interpretability aims to understand neural networks'
decision-making processes well enough to predict behavior on arbitrary inputs or accomplish
practical goals like control and monitoring.

**Key Insight**: Unlike earlier interpretability work focused on "why did my model make
THIS decision?", mechanistic interpretability asks "how did my model solve this GENERAL
CLASS of problems?" — focusing on the mechanisms underlying generalization.

**Central Finding**: Current methods (especially Sparse Dictionary Learning / SAEs) have
significant practical and conceptual limitations:
- Reconstruction errors remain too high (GPT-4 + 16M latent SAE ≈ 10% of original compute)
- Expense scales with model size
- Linear representation hypothesis may not hold universally
- Sparsity ≠ interpretability (feature splitting, absorption problems)
- SDL describes activations, not the mechanisms that compute them

**Three Applications Axes**:
1. **Monitoring** — Detect unsafe cognition in real-time
2. **Control** — Edit model behavior via mechanism manipulation
3. **Prediction** — Anticipate behavior in novel situations

**Open Problems Taxonomy**: Methods/foundations, applications, and socio-technical challenges
that must be solved before mechanistic interpretability can deliver on its safety promises.

────────────────────────────────────────────────────────────────────────────────

## 1. Core Thesis

### Why Mechanistic Interpretability Matters

Modern AI capabilities are **learned, not designed**. Developers design training processes
but do not — and in almost all cases, cannot — understand the neural mechanisms underlying
learned capabilities. This creates a fundamental problem: we deploy systems we don't understand.

Understanding mechanisms would enable:
- **Better control** over AI behavior
- **Better monitoring** during deployment  
- **Trust** enabling deployment in safety-critical settings
- **Scientific discovery** — AI systems may encode knowledge humans don't yet have
  (protein folding, disease patterns, etc.)

### The "Alien Cognition" Problem

Humans and AI solve problems differently:
- A model 1% the size of GPT-3 outperforms humans on next-token prediction
- State-of-the-art multimodal LLMs fail tasks a four-year-old masters
- Image models recognize elephants by hide texture, not shape
- A small transformer learned modular addition via Fourier transforms

**Implication**: We cannot assume AI cognition resembles human cognition. We must
reverse engineer these systems to understand their potentially alien representations.

### Three Threads of Interpretability

1. **Interpretability by Design** (early) — Build interpretable models: decision trees,
   linear models, GAMs, Concept-Bottleneck Models, Kolmogorov-Arnold Networks

2. **Attribution Methods** (scaling era) — Why THIS decision? Grad-CAM, integrated
   gradients, SHAP, LIME, masking-based causal attribution

3. **Mechanistic Interpretability** (current) — How does the model solve this GENERAL
   class of problems? Feature visualization, circuits, representation subspaces, SDL

────────────────────────────────────────────────────────────────────────────────

## 2. The Three-Step Reverse Engineering Framework

Reverse engineering neural networks follows the same pattern as reverse engineering any
complex system (engines, software, etc.):

### Step 1: Decomposition

**Goal**: Break the network into simpler, interpretable parts.

**Problem**: Networks don't naturally decompose into architectural components.

- Individual neurons are **polysemantic** — they respond to multiple unrelated features
- Attention heads are also polysemantic
- Representations may span multiple layers
- The "Neuron Doctrine" from neuroscience doesn't apply

**Current Approaches**:

| Method | Description | Limitation |
|--------|-------------|------------|
| **Dimensionality Reduction** | PCA, SVD, NMF on activations | Cannot find more directions than dimensions |
| **Sparse Dictionary Learning** | SAEs, Transcoders, Crosscoders | See Section 3 for extensive limitations |
| **Intrinsic Interpretability** | Train models to be decomposable | Not yet competitive with SOTA performance |

### Step 2: Description

**Goal**: Formulate hypotheses about functional roles of components.

**Two Description Types**:
1. What **causes** a component to activate?
2. What are the **downstream effects** of activation?

**Methods for Describing Causes**:
- **Highly activating examples** — Find inputs that maximally activate a component
- **Attribution methods** — Trace importance back through the network
- **Feature synthesis** — Generate synthetic inputs that activate components

**Methods for Describing Effects**:
- **Ablation studies** — Remove component, observe behavior change
- **Activation patching** — Swap activations between runs
- **Causal tracing** — Track information flow through network

### Step 3: Validation

**Goal**: Test whether hypotheses are correct.

**Approaches**:
- **Model organisms** — Small, fully understood networks to validate methods
- **Benchmarks** — Standardized tests for interpretability methods
- **Interventions** — If hypothesis correct, targeted edits should have predicted effects

**The Cycle**: If validation fails → refine decomposition OR refine hypotheses → repeat

────────────────────────────────────────────────────────────────────────────────

## 3. Sparse Dictionary Learning (SDL) — Current State and Limitations

SDL (including SAEs, Transcoders, and Crosscoders) is currently the most popular
unsupervised decomposition method in mechanistic interpretability. It attempts to
identify more directions than there are activation dimensions by exploiting the
**superposition hypothesis**: networks represent more features than dimensions by
keeping each feature sparse.

### The SDL Architecture

```
Hidden Activations → Encoder → Wide Sparse Layer → Decoder → Reconstruction
                                    ↑
                         "Latents" (interpretable?)
```

The encoder learns to activate specific "latents" when features are present.
The decoder dictionary contains feature directions. Trained with sparsity pressure.

### Eight Critical Limitations

| Problem | Description | Severity |
|---------|-------------|----------|
| **High Reconstruction Error** | GPT-4 + 16M latent SAE ≈ model with 10% pretraining compute. GPT-2 small loses 10-40% performance. | Critical |
| **Expense at Scale** | Must train separate SDL for every layer. Costs scale with model size. | High |
| **Linear Assumption** | Assumes linear representation hypothesis; strong version is false for some models | High |
| **Sparsity ≠ Interpretability** | Feature splitting, absorption, and composition break the proxy | Medium-High |
| **Geometry Ignored** | Treats features as "bag of features" — misses semantic structure in relationships | Medium |
| **Architecture Limits** | Can't straightforwardly handle attention heads or cross-layer representations | Medium |
| **Activations, Not Mechanisms** | SDL describes what's activated, not HOW computation happens | Fundamental |
| **Missing Concepts** | Training distribution determines which latents exist; may lack concepts you need | High |

### Why Reconstruction Error is Fatal

When you insert an SDL reconstruction back into the model:

```
Original GPT-4 → Task Performance: 100%
GPT-4 + SDL Reconstruction → Task Performance: ~10%
```

This means **90% of what the model "knows" is in the reconstruction error**.
The "error node" approach (Marks et al., 2024) just puts "everything else" in
an uninterpretable bucket — not a solution.

### The Linear Representation Hypothesis Problem

SDL assumes:
1. Concepts compose additively (feature vectors sum)
2. Concept intensity = vector magnitude
3. One-dimensional features (now refuted)

**Reality**: Some models use nonlinear representations. Probing success doesn't
prove linearity — it proves correlation. The weak version (some concepts are linear)
is supported; the strong version (all concepts are linear) is false.

### Feature Splitting and Absorption

**Feature Splitting**: With more capacity, a "cat" feature splits into "Siamese cat",
"Persian cat", "Maine Coon" — is this good (more specific) or bad (unstable)?

**Feature Absorption**: A feature for "begins with 'e'" absorbs edge cases,
becoming "begins with 'e' except 'elephant'" — violating the clean atomic model.

### The Fundamental Problem

> "SDL identifies directions in activation space. Being activations, they only
> interact with the network's mechanisms, but are not the mechanisms themselves."

You learn WHAT is represented, not HOW it's computed. Understanding mechanisms
requires post-hoc analysis that is "labor intensive, computationally expensive,
or dataset dependent."

────────────────────────────────────────────────────────────────────────────────

## 4. Applications of Mechanistic Interpretability

### 4.1 Monitoring and Auditing

**White-box evaluations** could detect unsafe cognition that black-box testing misses:
- Deception (intentionally underperforming on evals, "sandbagging")
- Situational awareness exploitation
- Sycophancy (tailoring responses to user beliefs)

**Real-time monitoring**: Passively watch model internals during deployment, flag
abnormal activation patterns even without full understanding ("mechanistic anomaly
detection").

**Red-teaming enhancement**: Use interpretability to find "refusal directions" and
optimize inputs that minimize projections onto those directions — more efficient
than black-box adversarial attacks.

### 4.2 Control

**Activation steering**: Add fixed vectors to intermediate activations at inference
time to influence behavior. Derived from linear representation hypothesis — success
is evidence for the hypothesis.

**Machine unlearning**: Remove specific knowledge/capabilities (bioweapons info,
private data, copyrighted content) while preserving other performance. Mechanistic
understanding could improve surgical precision.

**Model editing (ROME et al.)**: Make precise knowledge modifications. Current
methods have flaws — interpretability hasn't yet found the right components to
intervene on.

### 4.3 Prediction

**Behavior in novel situations**: Predict jailbreaks, trojans, adversarial examples,
biases. "Enumerative safety" — prove no mechanisms exist for specific dangerous
capabilities.

**Capabilities during training**: Predict when capabilities emerge, understand
discontinuous "grokking" phenomena, correlate loss drops with circuit formation.

**Formal verification**: Mathematical proof that AI behavior satisfies properties
on all inputs in a distribution. Currently beyond capabilities — small toy models
only (Gross et al., 2024).

### 4.4 Microscope AI

Train neural networks on scientific data, then use interpretability to extract
novel insights:
- Chess concepts from AlphaZero → taught to grandmasters
- Facial features affecting judge decisions (from mugshot CNNs)
- Morphological features predicting immune cell protein expression

**Barrier**: Requires ML expertise + interpretability expertise + domain knowledge.
Rare combination in most fields.

### 4.5 Beyond Transformers

Most mechanistic interpretability research focuses on three families:
1. CNN-based image models
2. BERT-based text models
3. GPT-based text models

**Open question**: Do insights transfer to diffusion models, Vision Transformers,
RWKV, state space models (SSMs)? Some evidence of method transfer exists.

────────────────────────────────────────────────────────────────────────────────

## 5. Open Problems Taxonomy

The paper organizes open problems into three major categories:

### Category 1: Methods and Foundations

| Problem | Current State | What's Needed |
|---------|---------------|---------------|
| **Network decomposition** | SDL has fundamental limitations | Better theoretical foundations for "carving at joints" |
| **Component description** | Correlational, not causal | Deeper mechanistic descriptions |
| **Validation** | Often conflates hypotheses with conclusions | Rigorous hypothesis testing, benchmarks |
| **Concept-based probing** | Detects correlations, not causation | Counterfactual data, causal probes |
| **Circuit discovery** | Low faithfulness, task-dependent | Better decomposition, scalable methods |
| **Automation** | Partial (ACDC, auto-labeling) | Full pipeline automation |

### Category 2: Applications

| Application | Current Progress | Key Barriers |
|-------------|------------------|--------------|
| **Monitoring unsafe cognition** | Feasible with shallow methods | SDL doesn't capture mechanisms |
| **Model control (steering)** | Moderate success | Side effects, mechanism-level control |
| **Behavior prediction** | Limited (hallucination, jailbreaks) | Enumerative safety far off |
| **Capability prediction** | Correlational (induction heads) | Mechanistic training dynamics |
| **Microscope AI** | Promising demos (chess, medical) | Accessibility, automation |
| **Formal verification** | Toy models only | Scale to frontier systems |

### Category 3: Socio-Technical

| Problem | Description |
|---------|-------------|
| **Policy translation** | How does technical progress become governance levers? |
| **Evaluation standards** | Comparing against non-interpretability baselines |
| **Paradigm clarity** | What IS interpretability trying to achieve? |
| **Context dependence** | Interpretations depend on deployment context |
| **Selective transparency** | Risk of corporate misuse, "interpretability washing" |
| **False assurance** | Modest progress used to argue against regulation |

### The Four Axes of Progress

The paper identifies four axes along which progress must be measured:

1. **Decomposition vs. Description Quality**
   - Decomposition: carving networks at generalization joints
   - Description: depth of causal/mechanistic understanding

2. **Extent of Network Coverage**
   - Feature-level → Circuit-level → Full model (enumerative)

3. **Extent of Task Distribution**
   - Narrow (single behavior) → Full distribution (formal verification)

4. **Post-training vs. During-training Understanding**
   - Fixed model mechanisms → Training dynamics → Emergence prediction

────────────────────────────────────────────────────────────────────────────────

## 6. Implementable Algorithms

### Algorithm 1: Sparse Autoencoder (SAE) Training

```
Input: Hidden activations H from model layer, dictionary size d, sparsity λ
Output: Encoder E, Decoder D (feature dictionary)

Initialize:
  E: R^n → R^d  (encoder weights)
  D: R^d → R^n  (decoder weights, normalized columns)

For each batch of activations h ∈ H:
  1. Encode:     z = ReLU(E(h))           # sparse latent codes
  2. Decode:     ĥ = D(z)                 # reconstruction
  3. Loss:       L = ||h - ĥ||² + λ||z||₁ # reconstruction + sparsity
  4. Update E, D via gradient descent
  5. Normalize decoder columns: D[:,i] = D[:,i] / ||D[:,i]||

Return E, D
```

**Variants**:
- **Transcoder**: Decode to NEXT layer activations instead of same layer
- **Crosscoder**: Multiple input/output layers simultaneously
- **TopK SAE**: Replace ReLU+L1 with TopK activation (fixed sparsity)

### Algorithm 2: Activation Patching / Causal Intervention

```
Input: Model M, clean input x_c, counterfactual input x_cf, component c
Output: Effect of c on output difference

1. Run M(x_c), cache activation a_c at component c
2. Run M(x_cf), cache activation a_cf at component c
3. Run M(x_cf) again, but REPLACE a_cf with a_c at component c
4. Measure: effect = |output_patched - output_cf|

Return effect  # high effect = component c causally relevant
```

### Algorithm 3: Attribution Patching (Gradient Approximation)

```
Input: Model M, inputs x_c, x_cf, all components C
Output: Approximate causal importance for each component

1. Compute Δoutput = M(x_c) - M(x_cf)
2. For each component c:
     grad_c = ∂(output)/∂(activation_c) at x_cf
     Δa_c = activation_c(x_c) - activation_c(x_cf)
     importance_c ≈ grad_c · Δa_c  # first-order approximation

Return importance rankings
```

**Note**: This is a LINEAR approximation — may miss nonlinear interactions.

### Algorithm 4: Automated Circuit Discovery (ACDC-style)

```
Input: Model M, task T, threshold τ
Output: Minimal circuit (subgraph) for task T

1. Define clean/counterfactual dataset pairs for task T
2. Initialize circuit = full model graph
3. For each edge (u,v) in reverse topological order:
     a. Patch edge (u,v) with counterfactual activation
     b. Measure task performance degradation Δ
     c. If Δ < τ: remove edge from circuit

Return circuit (pruned subgraph)
```

### Algorithm 5: Linear Probe Training

```
Input: Activations A, concept labels y, regularization λ
Output: Probe direction w

# For binary concept:
1. Collect A_pos = {a : y(a) = 1}, A_neg = {a : y(a) = 0}
2. Fit logistic regression: w = argmin_w Σ BCE(σ(w·a), y) + λ||w||²
3. Normalize: w = w / ||w||

# Validation (critical!):
4. Test on held-out distribution
5. Verify with causal intervention: does steering by w change behavior?

Return w
```

### Algorithm 6: Activation Steering

```
Input: Model M, steering vector v, scale α, layer l
Output: Steered model M'

At inference time:
1. Run forward pass normally until layer l
2. At layer l: a_l' = a_l + α·v
3. Continue forward pass with modified activation

# Finding v (several methods):
- Difference in means: v = mean(A_concept) - mean(A_baseline)
- SAE latent direction: v = D[:,feature_idx] from trained SAE
- Linear probe direction: v = w from probe training
```

────────────────────────────────────────────────────────────────────────────────

## 7. Hydrogen/PureScript Relevance

### Direct Applications to Hydrogen

**1. Type-Safe Interpretability Primitives**

Hydrogen's bounded type system is ideal for implementing interpretability algorithms
with guaranteed correctness:

```purescript
-- Bounded activation values (prevent numerical instability)
type Activation = BoundedFloat (-1000.0) 1000.0

-- Feature indices are bounded by dictionary size
type FeatureIdx d = BoundedInt 0 (d - 1)

-- Sparsity level is a probability
type SparsityLevel = BoundedFloat 0.0 1.0

-- Attribution scores with known bounds
type Attribution = BoundedFloat (-1.0) 1.0
```

**2. Visualization Components for Interpretability**

Hydrogen could provide atomic components for mechanistic interpretability UIs:

- **ActivationHeatmap**: Visualize layer activations as 2D grids
- **CircuitGraph**: Interactive DAG visualization for circuit discovery
- **FeatureExplorer**: Browse SAE latents with example activations
- **AttributionOverlay**: Highlight input tokens by importance
- **SteeeringSlider**: Interactive activation steering controls

**3. Deterministic Agent Interpretability**

At billion-agent scale, interpretability becomes critical infrastructure:

```purescript
-- Every interpretation is deterministic and reproducible
interpretFeature :: FeatureIdx d -> Interpretation
interpretFeature idx = 
  -- Same feature index → same interpretation → same UUID5
  -- Enables caching, coordination, verification across agents
```

### Conceptual Connections

**The Linear Representation Hypothesis ↔ Hydrogen's Atomic Composition**

The paper's core assumption — that concepts compose linearly as vector sums — 
mirrors Hydrogen's atomic design philosophy:

```
ML world:    concept_A + concept_B = combined_representation
Hydrogen:    atom_A <> atom_B = molecule

Both assume compositional structure from bounded primitives.
```

**SDL Reconstruction Error ↔ Schema Completeness**

The paper's concern about SDL missing 90% of model knowledge parallels Hydrogen's
Schema completeness requirement:

> If our atoms don't capture all design primitives, agents can't express full designs.
> If SDL latents don't capture all features, interpretations miss model behavior.

**Solution in both cases**: Ensure the atomic vocabulary is COMPLETE for the domain.

### Implementation Opportunities

**1. SAE Training Pipeline in PureScript**

Implement Algorithm 1 as pure functions operating on Array-based tensors:

```purescript
trainSAE :: SAEConfig -> Array Activation -> Effect SAE
trainSAE config activations = do
  -- Pure gradient computation
  -- Deterministic initialization (seeded RNG)
  -- Bounded arithmetic throughout
```

**2. Interpretability Dashboard**

A Hydrogen application for exploring model internals:

```purescript
type InterpDashboard msg =
  { model :: ModelHandle
  , selectedLayer :: LayerIdx
  , selectedFeature :: Maybe FeatureIdx
  , attributionView :: AttributionMode
  }

-- Pure view function composing interpretability atoms
view :: InterpDashboard Msg -> Element Msg
view state = 
  E.div_ [ E.class_ "interp-dashboard" ]
    [ layerSelector state.selectedLayer
    , featureExplorer state.selectedFeature
    , attributionOverlay state.attributionView
    ]
```

**3. Formal Verification Bridge**

The paper mentions formal verification as the ultimate goal. Hydrogen's Lean4
integration could provide:

```lean
-- Prove properties about interpretability algorithms
theorem sae_reconstruction_bound :
  ∀ (h : Activation) (sae : TrainedSAE),
    ‖h - sae.reconstruct h‖ ≤ sae.error_bound := by
  -- Proof that reconstruction error is bounded
```

### Why This Matters for Continuity

The mechanistic interpretability research agenda aims to make AI systems
**understandable and controllable**. Hydrogen aims to make UI systems
**deterministic and verifiable**. 

Both are working toward the same meta-goal: **systems that agents can reason about
algebraically**, where same inputs produce same outputs, and where the gap between
specification and implementation can be formally verified.

At billion-agent scale:
- **Interpretable AI** = agents can understand what other agents' models do
- **Deterministic UI** = agents can predict what any Element will render to

**The intersection**: AI agents using Hydrogen to build interpretability tools
for other AI agents' models. The ouroboros of AI safety infrastructure.

────────────────────────────────────────────────────────────────────────────────

## References

### Key Papers Cited

**Foundational**:
- Elhage et al. (2021) — "A Mathematical Framework for Transformer Circuits" (superposition hypothesis)
- Olah et al. (2020) — "Zoom In: An Introduction to Circuits" (feature visualization, circuits)
- Nanda et al. (2023) — "Progress measures for grokking via mechanistic interpretability"

**Sparse Dictionary Learning**:
- Bricken et al. (2023) — "Towards Monosemanticity" (SAEs on Claude)
- Templeton et al. (2024) — "Scaling Monosemanticity" (16M latent SAEs on GPT-4)
- Gao et al. (2024) — OpenAI's SAE work
- Lindsey et al. (2024) — Crosscoders (cross-layer representations)

**Circuit Discovery**:
- Wang et al. (2023) — "Interpretability in the Wild" (IOI circuit)
- Conmy et al. (2023) — ACDC (Automated Circuit DisCovery)
- Marks et al. (2024) — "Sparse feature circuits"

**Applications**:
- Arditi et al. (2024) — "Refusal in language models is mediated by a single direction"
- Turner et al. (2024) — Activation steering
- Rimsky et al. (2024) — Steering for safety

**Validation/Criticism**:
- Makelov et al. (2023, 2024) — Interpretability illusions, SAE evaluation
- Miller et al. (2024) — Circuit faithfulness issues
- Farrell et al. (2024) — SDL latents don't match human concepts

**Governance**:
- Casper et al. (2024) — White-box evaluations for AI safety
- Dalrymple et al. (2024) — Formal verification of AI systems
- Grosse (2024) — SDL in safety cases

### Full Citation

Sharkey, L., Chughtai, B., Batson, J., Lindsey, J., Wu, J., et al. (2025).
"Open Problems in Mechanistic Interpretability."
arXiv:2501.16496v1 [cs.LG], January 2025.
https://arxiv.org/abs/2501.16496

────────────────────────────────────────────────────────────────────────────────
                                                                        — Opus
