# VA-π: Variational Policy Alignment for Pixel-Aware Autoregressive Generation

────────────────────────────────────────────────────────────────────────────────

**Source**: pixelawareaugoregressivegens.pdf
**Authors**: Xinyao Liao, Qiyuan He, Kai Xu et al. (NUS, HUST)
**Published**: arXiv:2512.19680v1, December 2025
**Synthesized**: 2026-02-26 by Opus

────────────────────────────────────────────────────────────────────────────────

## Executive Summary

This paper addresses a fundamental problem in autoregressive (AR) image generation:
**token-level likelihood doesn't guarantee pixel-level quality**. The solution treats
AR generation as reinforcement learning, using pixel reconstruction as intrinsic reward.

**Key Innovation**: Derive an ELBO (evidence lower bound) that unifies:
- Token-level next-token prediction (AR model's native objective)
- Pixel-level reconstruction quality (what we actually care about)

Then optimize it via RL policy gradients, treating the AR generator as a policy.

**Results** (25 minutes of training on 1% of ImageNet):
- FID: 14.36 → 7.65 (47% improvement)
- IS: 86.55 → 116.70 (35% improvement)
- No external reward model needed
- 86.6% cheaper than conventional RL fine-tuning (AR-GRPO)

**Core Insight**: High token likelihood can produce "off-manifold" sequences that
decode to garbage images. VA-π provides direct pixel-level supervision to prevent this.

**Applicability**: Works on visual generation models (LlamaGen) and unified multimodal
models (Janus-Pro), improving both class-to-image and text-to-image generation.

────────────────────────────────────────────────────────────────────────────────

## 1. The Problem: Token-Pixel Misalignment

### The Two-Stage Pipeline

Standard AR visual generation has two stages:

```
Stage 1: Train Tokenizer
  Image I → Encoder E → Quantizer Q → Tokens x
  Tokens x → Decoder D → Reconstructed Image Î
  Objective: Pixel reconstruction (MSE + perceptual + VQ loss)

Stage 2: Train AR Model
  Tokens x → AR Model πθ → Next token prediction
  Objective: Token likelihood (cross-entropy)
```

**The Problem**: These objectives are DIFFERENT. The AR model is never directly
optimized for pixel quality.

### Off-Manifold Token Sequences

The AR model can produce high-likelihood token sequences that decode into garbage:

```
Token sequence with high πθ(x) likelihood
        ↓
    Decoder D
        ↓
Visually incoherent image with artifacts
```

These "off-manifold" sequences:
- Have plausible token statistics
- Deviate from the image manifold
- Produce artifacts, blur, wrong structures

### Why Previous Solutions Fail

| Approach | Method | Problem |
|----------|--------|---------|
| **Generator-centric** | Add noise during AR training | Doesn't directly optimize pixels |
| **Tokenizer-centric** | Make decoder robust to noise | Tolerates bad tokens instead of preventing them |
| **Post-train tokenizer** | More noise robustness training | Oversmooths decoder, reduces sharpness |

None directly address the root cause: **AR model receives no pixel-level feedback**.

────────────────────────────────────────────────────────────────────────────────

## 2. The Solution: Variational Policy Alignment

### Core Idea

Treat the discrete token sequence as a **latent variable** of the pixel-level image.
This allows deriving a tractable ELBO that combines token and pixel objectives.

```
True objective: max log p(I)  (pixel-level likelihood)
                     ↓ intractable
Variational bound: max ELBO = Reconstruction + Prior regularization
```

### The Two Components

**1. Reconstruction Term**
- Measures: Can sampled tokens decode back to original image?
- Provides: Direct pixel-level supervision

**2. Prior Regularization Term**  
- Measures: KL divergence between teacher-forced and free-running distributions
- Provides: Preserves AR model's learned token distribution, prevents collapse

### Why RL Instead of Backprop?

The reconstruction term is non-differentiable due to:
1. **Quantizer**: Discrete codebook lookup
2. **Sampling**: Categorical distribution over tokens

Straight-Through Estimator (STE) only propagates gradients along ground-truth path.
**RL distributes gradients across ALL sampled sequences** according to their rewards.

### The RL Formulation

```
Policy:     AR generator πθ (outputs token probabilities)
Action:     Sample next token
State:      Previous tokens + condition
Reward:     Pixel reconstruction quality R(x, x*) = -reconstruction_loss
```

This enables broader exploration of token space while optimizing for pixel fidelity.

────────────────────────────────────────────────────────────────────────────────

## 3. The ELBO Formulation

### The Pixel-Level Likelihood

We want to maximize:

```
max_θ E_{I~p_data} [log p(I; θ, φ)]

where p(I; θ, φ) = Σ_x p_φ(I|x) π_θ(x)
```

This marginalizes over all token sequences — intractable due to combinatorial space.

### Introducing the Variational Posterior

Define a variational posterior q_{ψ,θ}(x|I) using **teacher forcing**:

```
q_{ψ,θ}(x|I) = Π_{i=1}^N π_θ(x_i | x*_{1:i-1})

where x* = Q(E_ψ(I))  (ground-truth tokens from encoder)
```

Each token is predicted given the TRUE prefix, not the model's own outputs.
This concentrates on sequences that decode faithfully back to I.

### The ELBO

```
log p(I; θ, ψ, φ) ≥ E_{q(x|I)} [log p_φ(I|x)]     ← Reconstruction term
                    - KL(q_{φ,θ}(x|I) || π_θ(x))  ← Prior regularization
```

### Interpretation

**Reconstruction term**: "Given image I and its tokens, can the AR model generate
tokens that reconstruct I?" — pixel-level supervision

**Prior regularization**: "Keep the teacher-forced distribution close to the
free-running distribution" — prevents drift from learned token statistics

### Simplification: CE Instead of KL

In practice, the KL term is approximated with cross-entropy loss plus noise:

```
L_prior(π_θ, x*, x̃*) = -1/N Σ_{t=1}^N log π_θ(x*_t | x̃*_{<t})

where x̃* ~ K_ξ(·|x*) is x* corrupted with noise rate ξ
```

This addresses **exposure bias**: training on clean prefixes vs. testing on
model-generated (potentially noisy) prefixes.

────────────────────────────────────────────────────────────────────────────────

## 4. The VA-π Algorithm

### The Reconstruction Reward

Given reference image I, ground-truth tokens x*, sampled tokens x, decoded image Î:

```
R(x, x*) = -(L_MSE(Î, I) + λ_p L_p(Î, I))
```

Where:
- L_MSE = pixel-wise mean squared error
- L_p = perceptual loss (LPIPS)

### The Full Objective

Combining GRPO (Group Relative Policy Optimization) with our components:

```
J_{VA-π}(θ) = E[1/G Σ_i min(ρ_i A_i, clip(ρ_i, 1-ε, 1+ε) A_i) - β L_prior(π_θ, x*, x̃*)]
```

Where:
- G = number of samples per instance
- ρ_i = π_θ(x_i|x̃*) / π_{θ_old}(x_i|x̃*) (importance ratio)
- A_i = normalized advantage from reconstruction reward
- β = regularization weight
- ε = clipping parameter
- ξ = contextual noise level

### Training Procedure

```
For each batch of images:
  1. Encode: x* = Q(E(I))
  2. Add noise: x̃* ~ K_ξ(·|x*)
  3. Teacher-forcing: compute logits under AR model
  4. Sample: draw G token sequences per instance
  5. Decode: Î = D(x) for each sample
  6. Compute reward: R = -reconstruction_loss(Î, I)
  7. Normalize: A_i = (R_i - mean) / std  (group-relative)
  8. Update policy: GRPO objective
  9. Add regularization: CE loss on noisy context
```

### Advantages Over AR-GRPO

| Feature | AR-GRPO | VA-π |
|---------|---------|------|
| External reward model | Required | Not needed |
| Reference model storage | Required | Not needed |
| Free-running rollouts | Required (expensive) | Teacher-forcing only |
| Training time | 149 min | **20 min** |
| Pixel-level feedback | Indirect | **Direct** |

────────────────────────────────────────────────────────────────────────────────

## 5. Results

### Class-to-Image (ImageNet-1K)

| Model | FID↓ | IS↑ | Time |
|-------|------|-----|------|
| LlamaGen-XXL | 14.36 | 86.55 | - |
| + Post-train tokenizer | 14.26 | 86.70 | 18 min |
| + STE post-train | 11.46 | 102.21 | 381 min |
| + **VA-π** | **7.65** | **116.70** | **25 min** |

**47% FID improvement, 35% IS improvement, minimal compute.**

With classifier-free guidance (CFG):
- VA-π achieves FID 2.28, IS 273.53
- Best results with 15× less training than STE

### Text-to-Image (GenEval Benchmark)

| Model | Color | Counting | Two Obj. | Overall |
|-------|-------|----------|----------|---------|
| LlamaGen-XL | 0.550 | 0.197 | 0.263 | 0.306 |
| + AR-GRPO | 0.593 | 0.228 | 0.263 | 0.324 |
| + **VA-π** | **0.606** | **0.238** | **0.328** | **0.339** |

Without any text-alignment reward, VA-π improves compositional accuracy.

### Unified Multimodal (Janus-Pro 1B)

| Model | Attr. Binding | Two Obj. | Overall |
|-------|---------------|----------|---------|
| Janus-Pro 1B | 0.540 | 0.801 | 0.725 |
| + **VA-π** | **0.585** | **0.835** | **0.744** |

Generalizes to large multimodal systems.

### Ablation Findings

**Reward Composition**: Both MSE and perceptual loss needed; prior regularization essential
**Regularization Weight**: β=0.1 optimal; too high oversmooths, too low diverges
**Noise Ratio**: ξ=0.5 best; addresses exposure bias without excessive perturbation

────────────────────────────────────────────────────────────────────────────────

## 6. Implementable Algorithms

### Algorithm 1: VA-π Training Loop

```
Input: AR model π_θ, tokenizer (E, Q, D), dataset, hyperparams (β, ξ, ε, G)
Output: Aligned AR model π_θ

for each batch of images I:
  # 1. Encode to tokens
  z = E(I)
  x* = Q(z)  # ground-truth tokens
  
  # 2. Add contextual noise
  x̃* = corrupt(x*, noise_rate=ξ)  # random token replacement
  
  # 3. Compute logits under teacher forcing
  logits = π_θ(x̃*)  # shape: [batch, seq_len, vocab_size]
  
  # 4. Sample G sequences per instance
  samples = []
  for g in 1..G:
    x_g = sample_from_logits(logits)  # categorical sampling
    samples.append(x_g)
  
  # 5. Decode and compute rewards
  rewards = []
  for x_g in samples:
    Î = D(x_g)
    r = -MSE(Î, I) - λ_p * LPIPS(Î, I)
    rewards.append(r)
  
  # 6. Normalize rewards (group-relative)
  μ, σ = mean(rewards), std(rewards)
  advantages = [(r - μ) / σ for r in rewards]
  
  # 7. Compute GRPO loss
  policy_loss = 0
  for g, A_g in enumerate(advantages):
    ρ = π_θ(samples[g] | x̃*) / π_θ_old(samples[g] | x̃*)
    clipped = clip(ρ, 1-ε, 1+ε)
    policy_loss += min(ρ * A_g, clipped * A_g)
  policy_loss /= G
  
  # 8. Compute prior regularization
  prior_loss = CrossEntropy(logits, x*)
  
  # 9. Total loss
  loss = -policy_loss + β * prior_loss
  
  # 10. Update
  loss.backward()
  optimizer.step()

return π_θ
```

### Algorithm 2: Contextual Noise Corruption

```
Input: Token sequence x*, noise rate ξ, vocab size K
Output: Corrupted sequence x̃*

x̃* = x*.copy()
for i in 0..len(x*):
  if random() < ξ:
    x̃*[i] = random_int(0, K-1)  # replace with random token

return x̃*
```

### Algorithm 3: Reconstruction Reward

```
Input: Sampled tokens x, reference image I, decoder D, λ_p
Output: Reward scalar

# Decode tokens to image
Î = D(x)

# Pixel-level loss
L_MSE = mean((Î - I)^2)

# Perceptual loss (LPIPS)
L_p = LPIPS(Î, I)

# Reward is negative loss (higher is better)
R = -(L_MSE + λ_p * L_p)

return R
```

### Algorithm 4: Group-Relative Advantage

```
Input: Rewards [r_1, ..., r_G] for G samples
Output: Normalized advantages [A_1, ..., A_G]

μ = mean(rewards)
σ = std(rewards)

advantages = []
for r in rewards:
  A = (r - μ) / (σ + 1e-8)  # numerical stability
  advantages.append(A)

return advantages
```

### Algorithm 5: GRPO Policy Update

```
Input: Old policy π_old, current policy π_θ, samples, advantages, ε
Output: Policy loss

loss = 0
for (x, A) in zip(samples, advantages):
  # Importance ratio
  log_p_new = log π_θ(x | context)
  log_p_old = log π_old(x | context)
  ρ = exp(log_p_new - log_p_old)
  
  # Clipped objective
  unclipped = ρ * A
  clipped = clip(ρ, 1-ε, 1+ε) * A
  
  loss += min(unclipped, clipped)

return -loss / len(samples)  # negative for gradient ascent
```

────────────────────────────────────────────────────────────────────────────────

## 7. Hydrogen/PureScript Relevance

### Conceptual Parallels

**Token-Pixel Gap ↔ Element-Render Gap**

VA-π addresses the gap between token-level optimization and pixel-level quality.
Hydrogen addresses the gap between Element specification and actual rendering:

```
VA-π:     Token sequence (optimized) → Decoder → Pixels (what we care about)
Hydrogen: Element tree (specified)   → Target  → Pixels (what we care about)
```

In both cases, the intermediate representation may be "valid" but produce poor output.

### The "Off-Manifold" Problem in UI

Just as AR models can produce high-likelihood but visually garbage token sequences,
a compositional UI system could produce "valid" Element trees that render poorly:

- Colors that are technically valid SRGB but clash horribly
- Layouts that satisfy constraints but look unbalanced
- Typography that's schema-compliant but unreadable

### Potential Application: UI Quality as Reward

Following VA-π's approach, one could:

1. Define UI quality metrics (layout balance, color harmony, readability scores)
2. Treat UI generation as RL policy
3. Use quality metrics as intrinsic reward
4. Fine-tune UI generators with pixel-level feedback

```purescript
-- UI quality reward function
uiReward :: Element Msg -> RenderedPixels -> Number
uiReward element pixels = 
  - layoutBalanceScore pixels
  - colorHarmonyScore pixels  
  - readabilityScore pixels
```

### The ELBO Pattern

The ELBO decomposition (reconstruction + prior) is a useful pattern:

```
Reconstruction: Does the output match the intended input?
Prior:          Does the output stay within learned distribution?
```

For Hydrogen, this could translate to:

```purescript
-- "Reconstruction": Does the Element render correctly?
renderFidelity :: Element Msg -> TargetOutput -> Number

-- "Prior": Does the Element follow established patterns?
patternCompliance :: Element Msg -> DesignSystem -> Number

-- Combined objective
elementQuality :: Element Msg -> TargetOutput -> DesignSystem -> Number
elementQuality e t d = renderFidelity e t + λ * patternCompliance e d
```

### Exposure Bias in UI

VA-π addresses exposure bias: training on perfect prefixes vs. testing on
self-generated (potentially flawed) prefixes.

UI systems have analogous issues:
- Designing components in isolation vs. composing in real applications
- Testing with ideal content vs. user-generated content
- Training on curated examples vs. edge cases

The noisy context approach (ξ corruption rate) could apply:
train UI components with intentionally degraded context to improve robustness.

────────────────────────────────────────────────────────────────────────────────

## References

### Key Papers Cited

**AR Visual Generation**:
- Sun et al. (2024) — LlamaGen (AR image generation)
- Wu et al. (2024) — Janus-Pro (unified multimodal model)
- Esser et al. (2021) — VQGAN (visual tokenizer)

**Alignment Methods**:
- Li et al. (2024) — AR-GRPO (RL fine-tuning for AR models)
- Hou et al. (2024) — reAR (noisy context regularization)
- Shao et al. (2024) — GRPO (Group Relative Policy Optimization)

**Foundational**:
- Kingma & Welling (2014) — VAE (variational autoencoders)
- van den Oord et al. (2017) — VQVAE (vector quantized VAE)
- Schulman et al. (2017) — PPO (proximal policy optimization)

### Full Citation

Liao, X., He, Q., Xu, K., Qu, X., Li, Y., Wei, W., Yao, A. (2025).
"VA-π: Variational Policy Alignment for Pixel-Aware Autoregressive Generation."
arXiv:2512.19680v1.
https://arxiv.org/abs/2512.19680

Code: https://github.com/Lil-Shake/VA-Pi

────────────────────────────────────────────────────────────────────────────────
                                                                        — Opus
