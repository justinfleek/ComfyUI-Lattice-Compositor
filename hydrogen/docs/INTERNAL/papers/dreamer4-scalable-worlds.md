# Dreamer 4: Training Agents Inside of Scalable World Models

**Source**: arXiv:2509.24527v1 (September 2025)
**Authors**: Danijar Hafner, Wilson Yan, Timothy Lillicrap (Google DeepMind)
**Domain**: World Models, Reinforcement Learning, Imagination Training

---

## Abstract

Dreamer 4 learns to solve complex control tasks by reinforcement learning inside
a fast and accurate world model. The world model achieves real-time interactive
inference on a single GPU through a **shortcut forcing objective** and an
efficient transformer architecture.

**Key results**:
- First agent to obtain diamonds in Minecraft purely from offline data (no
  environment interaction)
- Outperforms OpenAI's VPT offline agent using 100× less data
- World model achieves 21 FPS on single H100 with 9.6s context (6× longer than
  prior models)
- Learns accurate action conditioning from only 100 hours of paired data (4% of
  dataset)
- Action conditioning generalizes to unseen game dimensions (Nether/End)

## 1. Core Innovation: Shortcut Forcing

Standard diffusion models require 64+ sampling steps for quality generations —
far too slow for interactive inference or imagination training. Shortcut forcing
solves this by training the model to predict endpoints for variable step sizes:

**The insight**: Condition on both noise level τ AND step size d. Train the
model to produce correct outputs for any step size, from fine (d=1/64) to coarse
(d=1). At inference, use d=1/4 for 4-step generation with no quality loss.

```
Standard diffusion:     x₀ → x₁/₆₄ → x₂/₆₄ → ... → x₁    (64 steps)
Shortcut forcing:       x₀ → x₁/₄ → x₂/₄ → x₃/₄ → x₁     (4 steps)
```

**Why it works**: The bootstrap loss distills two smaller steps into one larger
step. The model learns to "jump ahead" by predicting where the flow would end
up after multiple fine steps.

## 2. Architecture

The agent consists of two components using the same efficient transformer:
1. **Causal Tokenizer**: Compresses video frames into continuous representations
2. **Interactive Dynamics**: Predicts representations given interleaved actions

### 2.1 Causal Tokenizer

Compresses raw video into continuous representations for dynamics to consume:

```
Input:  [patch tokens] + [learned latent tokens]
        ↓ Block-Causal Encoder
Bottleneck: Linear projection → tanh activation (low-dimensional)
        ↓ Block-Causal Decoder  
Output: Reconstructed patches
```

**Key design choices**:
- **Causal in time**: Enables frame-by-frame decoding for interactive inference
- **Masked autoencoding**: Drop input patches (p ~ U(0, 0.9)) during training
- **Loss**: MSE + 0.2 × LPIPS (perceptual)

**Attention pattern**:
- Latent tokens attend to all modalities
- Each modality only attends within itself
- Enables flexible multi-modal integration

### 2.2 Interactive Dynamics Model

Operates on interleaved sequence of:
- Actions (keyboard/mouse encoded as tokens)
- Shortcut signal level τ and step size d
- Tokenizer representations (from frozen tokenizer)

```
Input sequence per timestep:
  [S_z spatial tokens] + [S_r register tokens] + [τ,d embedding] + [action tokens]

Architecture:
  - τ and d: discrete embedding lookup, concatenated channels
  - Actions: each component → S_a tokens, summed with learned embedding
  - Unlabeled videos: only learned embedding (no action conditioning)
```

**Shortcut forcing for dynamics**: Train to denoise representations with
variable step sizes. At inference, generate each frame with K=4 steps.

**Context corruption**: Slightly corrupt past inputs to τ_ctx=0.1 to make model
robust to small imperfections in its own generations.

### 2.3 Efficient Transformer Design

Interactive inference requires both high capacity AND fast generation. The
architecture addresses both:

**Base architecture**:
- 2D transformer (time × space dimensions)
- Causal in time (all tokens within timestep attend to each other and past)
- Pre-layer RMSNorm, RoPE, SwiGLU
- QKNorm + attention logit soft capping (stability)

**Efficiency optimizations**:

| Technique | Benefit |
|-----------|---------|
| Factored attention (space-only + time-only layers) | Breaks dense attention cost |
| Temporal attention every 4 layers only | 4× fewer time layers needed |
| GQA (grouped query attention) | Smaller KV cache |
| Alternating batch lengths | Faster training convergence |

**Result**: 21 FPS on single H100 with 9.6s context (vs 0.8-1.6s for prior models)

## 3. Training Pipeline

Three-phase training separates world knowledge from task-specific behavior:

### 3.1 Phase 1: World Model Pretraining

```python
# Phase 1: Learn world dynamics from videos
def pretrain_world_model(videos, actions=None):
    # Train tokenizer on videos
    tokenizer = train_tokenizer(videos, loss=MSE + 0.2*LPIPS)
    
    # Freeze tokenizer, train dynamics
    representations = tokenizer.encode(videos)
    dynamics = train_dynamics(
        representations,
        actions,  # Optional - can be None for unlabeled videos
        objective=shortcut_forcing
    )
    
    return tokenizer, dynamics
```

**Key insight**: World model absorbs majority of knowledge from unlabeled videos.
Only small amount of action-paired data needed for grounding.

### 3.2 Phase 2: Agent Finetuning

Insert agent tokens into the transformer to learn task-conditioned policy and
reward model:

```python
def finetune_agent(world_model, dataset):
    """
    dataset contains: videos, actions, tasks, rewards
    """
    # Insert agent tokens as additional modality
    # Agent tokens receive task embeddings as input
    # Predict policy and reward from agent token outputs
    
    # CRITICAL: Agent tokens attend to everything,
    # but nothing attends BACK to agent tokens
    # This prevents causal confusion in world model
    
    for batch in dataset:
        z = world_model.tokenizer.encode(batch.videos)
        h = world_model.dynamics(z, batch.actions, task=batch.tasks)
        
        # Multi-token prediction (L=8 future steps)
        policy_loss = -sum(log p(a_{t+n} | h_t) for n in range(L))
        reward_loss = -sum(log p(r_{t+n} | h_t) for n in range(L))
        
        # Continue dynamics loss to preserve world model
        dynamics_loss = shortcut_forcing_loss(z)
        
        loss = policy_loss + reward_loss + dynamics_loss
```

**Reward parameterization**: Symexp twohot — handles stochastic rewards across
varying orders of magnitude robustly.

### 3.3 Phase 3: Imagination Training

Improve policy beyond dataset behaviors by RL on imagined rollouts:

```python
def imagination_training(world_model, policy, value, dataset):
    """
    No environment interaction — pure imagination.
    """
    # Freeze transformer, only train policy and value heads
    policy_prior = copy(policy)  # Behavioral prior (frozen)
    
    for context in dataset.sample_contexts():
        # Generate rollout inside world model
        trajectory = []
        z = context
        
        for t in range(horizon):
            # Sample action from policy
            a = policy.sample(z)
            # Predict next state from world model
            z_next = world_model.dynamics.step(z, a)
            # Get reward from learned reward model
            r = world_model.reward_head(z)
            trajectory.append((z, a, r))
            z = z_next
        
        # Compute λ-returns for value training
        returns = compute_lambda_returns(trajectory, value, gamma=0.997)
        
        # Update value head (TD-learning)
        value_loss = -sum(log p(R_λ_t | s_t))
        
        # Update policy head (PMPO)
        policy_loss = pmpo_loss(trajectory, returns, policy_prior)
```

## 4. Key Algorithms

### 4.1 Shortcut Forcing Objective

The core training objective combines flow matching with bootstrap distillation:

```python
def shortcut_forcing_loss(model, z_clean, actions, d_min=1/64):
    """
    Train model to predict clean data from corrupted input,
    for any step size d from d_min to 1.
    
    z_clean: clean representations from tokenizer
    d_min: finest step size (1/K_max)
    """
    # Sample noise
    z_noise = torch.randn_like(z_clean)
    
    # Sample step size (power of 2)
    K = random.choice([1, 2, 4, 8, ..., K_max])
    d = 1 / K
    
    # Sample signal level on grid reachable by step size
    tau = random.choice([0, d, 2*d, ..., 1-d])
    
    # Create corrupted input
    z_corrupted = (1 - tau) * z_noise + tau * z_clean
    
    # Model predicts clean data (x-prediction)
    z_pred = model(z_corrupted, tau, d, actions)
    
    if d == d_min:
        # Flow matching loss (finest step)
        loss = mse(z_pred, z_clean)
    else:
        # Bootstrap loss: distill two half-steps
        with torch.no_grad():
            # First half-step
            b1 = (model(z_corrupted, tau, d/2, actions) - z_corrupted) / (1 - tau)
            z_mid = z_corrupted + b1 * (d/2)
            # Second half-step
            b2 = (model(z_mid, tau + d/2, d/2, actions) - z_mid) / (1 - (tau + d/2))
            v_target = (b1 + b2) / 2
        
        # Loss in x-space (scaled from v-space)
        v_pred = (z_pred - z_corrupted) / (1 - tau)
        loss = (1 - tau)**2 * mse(v_pred, v_target)
    
    # Ramp weight: focus on higher signal levels
    weight = 0.9 * tau + 0.1
    
    return weight * loss
```

**Why x-prediction**: V-prediction produces high-frequency outputs that
accumulate errors over long rollouts. X-prediction targets are more structured.

### 4.2 Flow Matching Foundation

The underlying diffusion formulation uses flow matching for simplicity:

```python
def flow_matching_basics():
    """
    Flow matching: learn velocity field pointing from noise to data.
    
    x_tau = (1 - tau) * x_0 + tau * x_1
    
    where:
      x_0 ~ N(0, I)     # Pure noise
      x_1 ~ Data        # Clean data  
      tau in [0, 1]     # Signal level (0=noise, 1=clean)
    
    Network predicts velocity: v = x_1 - x_0
    """
    # Training
    x_0 = torch.randn_like(x_1)
    tau = sample_signal_level()  # Uniform or logit-normal
    x_tau = (1 - tau) * x_0 + tau * x_1
    
    v_pred = model(x_tau, tau)
    loss = mse(v_pred, x_1 - x_0)
    
    # Inference (Euler integration)
    x = torch.randn(...)  # Start from noise
    for k in range(K):
        d = 1 / K
        tau = k * d
        v = model(x, tau)
        x = x + v * d  # Step toward data
    
    return x  # Clean sample
```

**Signal level sampling**: Logit-normal focuses training on intermediate τ
where learning signal is highest.

### 4.3 PMPO Reinforcement Learning

Policy learning uses PMPO (Positive-Negative Maximum Probability Optimization):

```python
def pmpo_loss(states, actions, advantages, policy, policy_prior, alpha=0.5, beta=0.3):
    """
    PMPO: Use SIGN of advantages only (ignores magnitude).
    
    Benefits:
    - No return/advantage normalization needed
    - Equal focus on all tasks regardless of reward scale
    - Robust across varying return magnitudes
    """
    # Partition states by advantage sign
    positive_set = [(s, a) for s, a, A in zip(states, actions, advantages) if A >= 0]
    negative_set = [(s, a) for s, a, A in zip(states, actions, advantages) if A < 0]
    
    # Positive term: maximize probability of good actions
    pos_loss = -alpha / len(positive_set) * sum(
        log_prob(policy, a, s) for s, a in positive_set
    )
    
    # Negative term: minimize probability of bad actions  
    neg_loss = (1 - alpha) / len(negative_set) * sum(
        log_prob(policy, a, s) for s, a in negative_set
    )
    
    # KL to behavioral prior (reverse direction)
    prior_loss = beta / len(states) * sum(
        kl_divergence(policy(s), policy_prior(s)) for s in states
    )
    
    return pos_loss + neg_loss + prior_loss
```

**Why reverse KL**: KL[policy || prior] constrains policy to space of reasonable
behaviors better than KL[prior || policy].

### 4.4 Multi-Token Prediction

Both policy and reward heads use multi-token prediction (MTP) with L=8:

```python
def multi_token_prediction_loss(h_t, future_actions, future_rewards, L=8):
    """
    Predict multiple future steps from single hidden state.
    
    h_t: output embedding at timestep t
    L: prediction horizon (8 steps)
    """
    policy_loss = 0
    reward_loss = 0
    
    for n in range(L):
        # Each MTP distance has its own output layer
        action_logits = policy_head[n](h_t)
        reward_logits = reward_head[n](h_t)
        
        policy_loss -= log_prob(action_logits, future_actions[t + n])
        reward_loss -= log_prob(reward_logits, future_rewards[t + n])
    
    return policy_loss + reward_loss
```

**Reward head**: Symexp twohot parameterization handles rewards across orders of
magnitude:
```
symexp(x) = sign(x) * (exp(|x|) - 1)
twohot: discretize into bins, interpolate between adjacent bins
```

## 5. Results

### 5.1 Offline Diamond Challenge

Task: Obtain diamonds in Minecraft from empty inventory, random worlds, 60-min
episodes. Requires ~20,000 sequential actions.

| Agent | Wood | Stone Pick | Iron Pick | Diamond |
|-------|------|------------|-----------|---------|
| VPT (finetuned) | 65% | 4.7% | 0% | 0% |
| BC (behavioral cloning) | 96% | 84% | 4.3% | 0% |
| VLA (Gemma 3) | 84% | 26% | 11% | 0% |
| **Dreamer 4** | **99%** | **96%** | **29%** | **0.7%** |

Dreamer 4 is **first agent to obtain diamonds purely offline**.

### 5.2 World Model Accuracy

Human players attempting tasks inside world models:

| Model | Context | FPS | Tasks Completed |
|-------|---------|-----|-----------------|
| Lucid-v1 | 1.0s | 44 | 0/16 |
| Oasis (small) | 1.6s | 20 | 0/16 |
| Oasis (large) | 1.6s | ~5 | 5/16 |
| **Dreamer 4** | **9.6s** | **21** | **14/16** |

Dreamer 4 accurately simulates: block placement, tool switching, crafting
interfaces, boat riding, monster combat, portal entry.

### 5.3 Action Generalization

Learning from unlabeled videos + small amount of action-paired data:

| Action Data | PSNR | SSIM |
|-------------|------|------|
| 0 hours | 0% | 0% |
| 10 hours | 53% | 75% |
| 100 hours | 85% | 100% |
| 2500 hours (full) | 100% | 100% |

**Key finding**: 100 hours (4% of data) achieves 85%+ action-conditioned quality.

**Out-of-distribution generalization**: Action conditioning learned ONLY on
Overworld generalizes to Nether/End (unseen during action training):
- PSNR: 76% of full-action model
- SSIM: 80% of full-action model

## 6. Hydrogen Relevance

### 6.1 Temporal Pillar Integration

Dreamer 4's shortcut forcing maps directly to Hydrogen's temporal primitives:

```purescript
-- Signal level as bounded type
type SignalLevel = BoundedFloat 0.0 1.0

-- Step size as discrete bounded type  
type StepSize = OneOf [1/64, 1/32, 1/16, 1/8, 1/4, 1/2, 1]

-- Shortcut model query
type ShortcutQuery =
  { signalLevel :: SignalLevel
  , stepSize :: StepSize
  , corrupted :: Tensor  -- z_tau
  }
```

### 6.2 Key Patterns for Hydrogen

1. **Flow matching as pure function**: τ-parameterized interpolation between
   noise and data — deterministic given τ

2. **Bootstrap distillation**: Self-supervised objective that doesn't require
   ground truth for intermediate steps

3. **Ramp loss weight**: `w(τ) = 0.9τ + 0.1` — simple bounded schedule

4. **PMPO sign-based learning**: Advantage signs only — no magnitude scaling
   issues, robust across reward scales

### 6.3 Bounded Guarantees

| Property | Bound |
|----------|-------|
| Sampling steps | K ∈ {1, 2, 4, 8, ..., 64} |
| Signal level grid | τ ∈ {0, 1/K, 2/K, ..., 1-1/K} |
| Context corruption | τ_ctx = 0.1 (fixed) |
| MTP horizon | L = 8 (fixed) |
| Discount factor | γ = 0.997 (fixed) |

### 6.4 Implications for Autonomous Agents

Dreamer 4 demonstrates that world models can:
- Learn majority of knowledge from **unlabeled** data
- Generalize action conditioning to **unseen scenarios**
- Improve policies **purely in imagination** (no environment interaction)

This is the foundation for safe autonomous learning — agents that can be trained
without deploying partially-trained policies in real environments.

---

## 7. Model Design Ablations

Cascade of improvements from naive diffusion forcing transformer:

| Change | FPS | FVD |
|--------|-----|-----|
| Baseline (K=64 steps) | 0.8 | 306 |
| + K=4 steps (no shortcut) | 9.1 | 875 |
| + Shortcut model | 9.1 | 329 |
| + X-prediction | 9.1 | 326 |
| + X-loss | 9.1 | 151 |
| + Ramp weight | 9.1 | 102 |
| + Alternating batch lengths | 9.1 | 80 |
| + Time attention every 4 layers | 18.9 | 70 |
| + GQA | 23.2 | 71 |
| + Time-factorized long context | 30.1 | 91 |
| + Register tokens | 28.9 | 91 |
| + 256 spatial tokens | **21.4** | **57** |

**Final model**: 57 FVD (vs 306 baseline), 21 FPS on single H100.

---

*Synthesized for the Hydrogen project — world models as bounded simulation primitives*
