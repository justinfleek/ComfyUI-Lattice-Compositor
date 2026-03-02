# VA-π: Variational Policy Alignment for Pixel-Aware Autoregressive Generation

**arXiv:** 2512.19680  
**Authors:** Xinyao Liao, Qiyuan He, Kai Xu, Xiaoye Qu, Yicong Li, Wei Wei, Angela Yao  
**Institution:** Huazhong University of Science & Technology, National University of Singapore  
**Date:** December 22, 2025  
**Domain:** Computer Vision / Generative Models / Reinforcement Learning

---

## Abstract

VA-π addresses the fundamental misalignment between autoregressive (AR) visual generators and pixel-space quality. The key insight is that tokenizers train to reconstruct clean images, while AR generators only optimize token likelihood—creating "off-manifold" token sequences that decode to low-quality images.

VA-π formulates generator-tokenizer alignment as a variational optimization, deriving an ELBO that unifies pixel reconstruction with autoregressive modeling. Uses RL-based alignment (REINFORCE/GRPO) with pixel-space reconstruction as intrinsic reward.

**Results:**
- FID: 14.36 → 7.65 on LlamaGen-XXL
- IS: 86.55 → 116.70
- Training: 1% data, 25 minutes on 8×A100

---

## 1. Problem: Token-Level vs Pixel-Level Mismatch

### 1.1 The AR Visual Generation Pipeline

```
Image → Tokenizer (encode) → Discrete Tokens → AR Model → Token Sequence → Tokenizer (decode) → Generated Image
```

Two-stage training creates a fundamental misalignment:

| Stage | Objective | Optimization |
|-------|-----------|--------------|
| Tokenizer | Pixel reconstruction | MSE |
| AR Generator | Token likelihood | Cross-entropy |

### 1.2 The Gap

- **Tokenizer:** Learns to reconstruct clean images from ground-truth tokens
- **AR Generator:** Only optimizes token probability, no pixel supervision
- **Result:** "Off-manifold" token sequences—high likelihood but poor pixel output

### 1.3 Visualization

```
Ground-truth manifold:  ●●●●●●●●●●●●●● (good images)
AR generated:          ○○○○○○○○○○○○○○ (off-manifold)
                        ↑
                   High token likelihood
                   Low pixel quality
```

---

## 2. Methodology: Variational Policy Alignment

### 2.1 ELBO Formulation

Treat AR token sequence as latent variable of pixel image:

```
log p(x) ≥ E[q(z|x)] [log p(x|z)] - KL[q(z|x) || p(z)]

Where:
  x = pixel image
  z = token sequence
  q(z|x) = tokenizer encoder
  p(x|z) = tokenizer decoder  
  p(z) = AR generator
```

**Interpretation:**
- **Reconstruction term:** Pixel-space quality
- **KL term:** Token-level likelihood preservation

### 2.2 VA-π Algorithm

```
Input: AR generator, tokenizer, reference image
1. Encode image to tokens: z = Encoder(x)
2. Add context noise: z_noisy = corrupt(z)
3. Teacher-forcing forward: logits = AR(z_noisy)
4. Sample tokens: z_sample ~ Categorical(logits)
5. Decode to image: x_recon = Decoder(z_sample)
6. Compute reward: r = similarity(x, x_recon)
7. RL update: maximize r with GRPO
8. Regularize: maintain token likelihood
```

### 2.3 Reward Design

**Intrinsic Reward:** Pixel reconstruction quality
```
r = ||x - x_recon||² (MSE-based)
```

Or perceptual:
```
r = CLIP similarity(x, x_recon)
r = LPIPS distance(x, x_recon)
```

### 2.4 RL Formulation

**Policy:** AR generator π(z_t | z_{<t})
**Action:** Sample next token
**Reward:** Pixel reconstruction quality

**Objective:**
```
maximize E_{z~π} [r(z)] + λ * H(π)

Where:
  r(z) = reconstruction reward
  H(π) = token likelihood entropy (regularization)
```

---

## 3. Technical Details

### 3.1 GRPO (Group Relative Policy Optimization)

Used for policy updates:

```python
def grpo_update(policy, old_logprobs, rewards, group_size=16):
    # Group rewards by context
    group_rewards = group_by_context(rewards, group_size)
    
    # Compute advantages
    advantages = group_rewards - mean(group_rewards)
    
    # Policy gradient update
    loss = -logprobs * advantages
    
    return policy_update(loss)
```

### 3.2 Context Noise

Add noise to input tokens during training:

```python
def corrupt_tokens(tokens, noise_ratio=0.1):
    mask = random_mask(tokens.shape, noise_ratio)
    corrupted = tokens.clone()
    corrupted[mask] = random_token()
    return corrupted
```

### 3.3 Teacher Forcing

During alignment, use ground-truth context:
- Input: partially corrupted ground-truth tokens
- Target: next token prediction
- This provides stable gradients vs. free-running

---

## 4. Experimental Results

### 4.1 ImageNet Class-Conditional Generation

| Method | FID ↓ | IS ↑ | Training Data | Time |
|--------|-------|------|--------------|------|
| LlamaGen-XXL (baseline) | 14.36 | 86.55 | — | — |
| + Noisy context | 12.11 | 92.34 | 10% | 4h |
| + Tokenizer tuning | 11.89 | 89.21 | 10% | 6h |
| **VA-π** | **7.65** | **116.70** | **1%** | **25min** |

### 4.2 Text-to-Image (GenEval)

| Method | Score ↑ |
|--------|---------|
| LlamaGen baseline | 0.306 |
| **+ VA-π** | **0.339** |
| Janus-Pro baseline | 0.725 |
| **+ VA-π** | **0.744** |

### 4.3 Efficiency

| Metric | Value |
|--------|-------|
| Training data | 1% of pretraining set |
| GPU time | 25 minutes (8×A100) |
| External rewards | None required |
| Free-running | Not needed |

---

## 5. Relation to Hydrogen

### 5.1 Schema-Element Alignment

VA-π addresses the tokenizer-generator alignment problem—directly relevant to Hydrogen's Element generation:

| VA-π Concept | Hydrogen Equivalent |
|--------------|-------------------|
| Tokenizer | Schema definition |
| AR Generator | Element builder |
| Pixel reconstruction | Rendered output |
| Off-manifold tokens | Invalid Elements |
| Alignment | Schema verification |

### 5.2 Schema Validation Pipeline

```purescript
-- VA-π style alignment for Hydrogen
alignSchema :: Schema -> Element -> ValidationResult
alignSchema schema element = do
  -- Encode to canonical form
  canonical = encode schema element
  
  -- Add noise/corruption
  corrupted = corrupt canonical
  
  -- Generate element
  generated = buildElement corrupted
  
  -- Decode to schema
  decoded = decode generated
  
  -- Compute reward (reconstruction quality)
  reward = schemaSimilarity schema decoded
  
  -- RL update if needed
  updateSchema reward
```

### 5.3 Element Quality Metrics

```purescript
-- Element quality rewards
data ElementReward
  = RenderQuality    -- Does it render correctly?
  | LayoutValid      -- Are bounds valid?
  | TypeSafe        -- Are types consistent?
  | CompositionValid -- Do compositions work?
  
-- VA-π style training
trainElementPolicy :: Policy ElementReward
trainElementPolicy = do
  elements <- sampleElements
  rendered <- render elements
  reward <- computeReward rendered
  updatePolicy reward
```

### 5.4 Off-Manifold Prevention

VA-π prevents off-manifold generation—Hydrogen needs similar guarantees:

```purescript
-- Prevent invalid Elements
validateElement :: Element -> Maybe Element
validateElement e = case e of
  Rectangle r | not (isValidBounds r) -> Nothing
  Text t | not (isValidFont t) -> Nothing  
  Image i | not (isValidURL i) -> Nothing
  _ -> Just e  -- Valid
```

---

## 6. Key Insights

### 6.1 Variational Framework

The ELBO formulation is general:

```
log p(desired_output) ≥ reconstruction_reward + prior_regularization

This applies to ANY generation pipeline where:
  - There's a "tokenizer" (schema)
  - There's a "generator" (builder)
  - There's a "reconstruction" (rendering)
```

### 6.2 RL for Discrete Alignment

RL effectively handles discrete token spaces:
- Gradient flows through sampled tokens
- Reward guides toward good sequences
- Regularization maintains distribution

### 6.3 Efficiency via Teacher Forcing

Avoids expensive free-running:
- Ground-truth context provides stable gradients
- Sampled tokens evaluated via reconstruction
- Direct pixel-level feedback

---

## 7. Technical Specifications

### 7.1 Algorithm Summary

```
VA-π(generator G, tokenizer T, data D):
  for batch in D:
    # 1. Encode
    z = T.encode(x)
    
    # 2. Corrupt
    z_noisy = corrupt(z)
    
    # 3. Forward (teacher forcing)
    logits = G(z_noisy)
    
    # 4. Sample
    z_sample = sample(logits)
    
    # 5. Decode
    x_recon = T.decode(z_sample)
    
    # 6. Reward
    r = reconstruction_reward(x, x_recon)
    
    # 7. Update (GRPO)
    G = G + α * ∇log G(z_sample) * r
    
    # 8. Regularize
    G = G + β * CE(logits, z)
```

### 7.2 Hyperparameters

| Parameter | Value |
|-----------|-------|
| Context noise ratio | 0.1-0.3 |
| GRPO group size | 16 |
| Learning rate | 1e-5 |
| Regularization λ | 0.1 |
| Training steps | 1000 |

---

## 8. Citation

```bibtex
@article{liao2025vapi,
  title={VA-π: Variational Policy Alignment for Pixel-Aware Autoregressive Generation},
  author={Liao, Xinyao and He, Qiyuan and Xu, Kai and Qu, Xiaoye and Li, Yicong and Wei, Wei and Yao, Angela},
  year={2025},
  eprint={2512.19680},
  archivePrefix={arXiv},
  primaryClass={cs.CV}
}
```

---

*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
