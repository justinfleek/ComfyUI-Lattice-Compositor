# Dreamer 4: Training Agents Inside of Scalable World Models

**Authors:** Danijar Hafner*, Wilson Yan*, Timothy Lillicrap

*Equal contribution. Google DeepMind, San Francisco, USA.

**arXiv:** 2509.24527v1 [cs.AI] 29 Sep 2025

**Website:** danijar.com/dreamer4

---

## Abstract

World models learn general knowledge from videos and simulate experience for training behaviors in imagination, offering a path towards intelligent agents. However, previous world models have been unable to accurately predict object interactions in complex environments.

We introduce **Dreamer 4**, a scalable agent that learns to solve control tasks by reinforcement learning inside of a fast and accurate world model. In the complex video game Minecraft, the world model accurately predicts object interactions and game mechanics, outperforming previous world models by a large margin.

The world model achieves real-time interactive inference on a single GPU through a **shortcut forcing objective** and an **efficient transformer architecture**. Moreover, the world model learns general action conditioning from only a small amount of data, allowing it to extract the majority of its knowledge from diverse unlabeled videos.

We propose the challenge of obtaining diamonds in Minecraft from only offline data, aligning with practical applications such as robotics where learning from environment interaction can be unsafe and slow. This task requires choosing sequences of over 20,000 mouse and keyboard actions from raw pixels.

By learning behaviors in imagination, **Dreamer 4 is the first agent to obtain diamonds in Minecraft purely from offline data, without environment interaction.**

---

## 1. Introduction

To solve complex tasks in embodied environments, intelligent agents need to deeply understand the world and choose successful actions. World models offer a promising approach towards this goal by learning to predict the future outcomes of potential actions from the perspective of an agent, such as a robot or a video game player.

World models equip agents with:
- A deep understanding of the world
- The ability to choose actions by planning or reinforcement learning in imagination
- The capacity to learn from fixed datasets (training purely in imagination without online interaction)

**Why offline training matters:** Optimizing behaviors offline is valuable for practical applications like robotics, where online interaction with a partially trained agent is often unsafe.

### Current Landscape

**World model agents (e.g., Dreamer 3):**
- Among the best-performing and most robust RL algorithms for games and robotics
- Fast and accurate for narrow environments
- Architecture lacks ability to fit complex real-world distributions

**Controllable video models (e.g., Genie 3):**
- Trained on diverse real video and games
- Accomplish diverse scene generation and simple interactions
- Based on scalable architectures (diffusion transformers)
- Still struggle to learn precise physics of object interactions and game mechanics
- Often require many GPUs to simulate a single scene in real time

### Contributions

1. **Training-free motion control using crude animations** — Scalable agent that learns to solve challenging control tasks by imagination training inside a world model

2. **First agent to obtain diamonds in Minecraft purely from offline data** — Substantially improves over OpenAI's VPT offline agent despite using 100× less data

3. **High-capacity world model with real-time inference** — Achieved through shortcut forcing objective and efficient transformer architecture

4. **Accurate prediction of object interactions and game mechanics** — Substantially outperforms previous world models in Minecraft

5. **Learning from unlabeled videos** — Requires only a small amount of aligned data to learn action conditioning with strong generalization

---

## 2. Background

### 2.1 Flow Matching

The world model is based on diffusion models, where the network f_θ is trained to restore a data point x₁ given a corrupted version x_τ. The signal level τ ∈ [0, 1] determines the mixture of noise and data:
- τ = 0: pure noise
- τ = 1: clean data

**Flow Matching Formulation:**

The network predicts the velocity vector v = x₁ − x₀ that points towards the clean data:

```
x_τ = (1 − τ) x₀ + τ x₁
x₀ ~ N(0, I)
x₁ ~ D (data distribution)
τ ~ p(τ)

Loss: L(θ) = ‖f_θ(x_τ, τ) − (x₁ − x₀)‖²
```

**Inference (Euler method):**

```python
def flow_matching_sample(model, K=64):
    """
    Standard flow matching sampling.
    K = number of sampling steps
    """
    d = 1/K  # step size
    x = torch.randn_like(data_shape)  # x₀ ~ N(0, I)
    
    for tau in range(0, 1, d):
        v = model(x, tau)  # predict velocity
        x = x + v * d       # Euler step
    
    return x  # x₁ (clean sample)
```

### 2.2 Shortcut Models

Shortcut models condition the neural network not only on signal level τ but also on the **requested step size d**. This allows choosing the step size at inference time and generating data using only a few forward passes.

**Training:**

For the finest step size d_min, use flow matching loss. For larger step sizes d_min < d ≤ 1, use a **bootstrap loss** that distills two smaller steps:

```python
def shortcut_model_loss(model, x0, x1, tau, d, d_min):
    """
    Shortcut model training objective.
    
    Args:
        x0: noise sample
        x1: clean data sample  
        tau: current signal level
        d: step size (sampled as power of 2)
        d_min: minimum step size = 1/K_max
    """
    x_tau = (1 - tau) * x0 + tau * x1
    
    if d == d_min:
        # Flow matching loss at finest resolution
        v_target = x1 - x0
    else:
        # Bootstrap loss: distill two half-steps
        with torch.no_grad():
            # First half-step
            b_prime = model(x_tau, tau, d/2)
            x_prime = x_tau + b_prime * (d/2)
            
            # Second half-step  
            b_double_prime = model(x_prime, tau + d/2, d/2)
            
            # Target is average of two velocities
            v_target = (b_prime + b_double_prime) / 2
    
    v_pred = model(x_tau, tau, d)
    loss = (v_pred - v_target).pow(2).mean()
    
    return loss
```

**Sampling step size and signal level:**

```python
def sample_shortcut_schedule(K_max):
    """
    Sample step size d uniformly as power of two.
    Sample signal level τ from grid reachable by current step size.
    """
    # d ∈ {1/1, 1/2, 1/4, 1/8, ..., 1/K_max}
    k = random.choice([1, 2, 4, 8, ..., K_max])
    d = 1 / k
    
    # τ from grid {0, d, 2d, ..., 1-d}
    tau = random.choice([i * d for i in range(k)])
    
    return tau, d
```

**Result:** Shortcut models generate high-quality samples with 2 or 4 sampling steps, compared to 64+ steps for typical diffusion models.

### 2.3 Diffusion Forcing

For sequential data, **diffusion forcing** assigns a different signal level to each time step of the data sequence, producing a corrupted sequence. This allows:

- Applying loss terms to all time steps in the sequence
- Each time step serves both as denoising task AND as history context for later time steps
- Flexible noise patterns at inference (e.g., generating next frame given clean or lightly noised history)

---

## 3. World Model Agent

Dreamer 4 consists of a **tokenizer** and a **dynamics model**, both using the same efficient transformer architecture.

### Algorithm 1: Dreamer 4 Training Pipeline

```
Phase 1: World Model Pretraining
  • Train tokenizer on videos using masked autoencoding (Eq. 5)
  • Train world model on tokenized videos and optionally actions using shortcut forcing (Eq. 7)

Phase 2: Agent Finetuning  
  • Finetune world model with task inputs for policy and reward heads (Eq. 7, 9)

Phase 3: Imagination Training
  • Optimize policy head using PMPO (Eq. 11)
  • Optimize value head using TD-learning (Eq. 10)
  • Train on trajectories generated by world model + policy head
```

### 3.1 Causal Tokenizer

The tokenizer compresses raw video into continuous representations for the dynamics model.

**Architecture:**
- Block-causal transformer (causal in time, full attention within each frame)
- Each time step: patch tokens of current image + learned latent tokens
- Encoder → bottleneck projection (linear + tanh) → Decoder
- Enables temporal compression while decoding frame-by-frame for interactive inference

**Attention Pattern:**
- Encoder: latent tokens attend to all modalities; each modality only attends within itself
- Decoder: each modality attends within itself and to latents; latents only attend within themselves

**Training Objective (Eq. 5):**

```python
def tokenizer_loss(encoder, decoder, video_frames):
    """
    Masked autoencoding with reconstruction loss.
    
    Args:
        video_frames: [B, T, C, H, W] input video
    """
    # Random patch dropout per image
    p = torch.rand(1).item() * 0.9  # p ~ U(0, 0.9)
    
    # Replace patches with learned embedding with probability p
    masked_input = apply_patch_dropout(video_frames, p, learned_mask_embedding)
    
    # Encode and decode
    latents = encoder(masked_input)
    reconstructed = decoder(latents)
    
    # Combined loss with loss normalization
    L_mse = F.mse_loss(reconstructed, video_frames)
    L_lpips = lpips_loss(reconstructed, video_frames)
    
    # Loss normalization: divide by running RMS estimates
    loss = normalize_by_rms(L_mse) + 0.2 * normalize_by_rms(L_lpips)
    
    return loss
```

**Why MAE training?** Improves spatial consistency of videos generated by the dynamics model.

### 3.2 Interactive Dynamics

The dynamics model operates on interleaved sequences of actions and tokenizer representations. Trained using **shortcut forcing** for fast interactive inference (K=4 forward passes per frame).

**Input Sequence Structure:**

```
[action_1, τ_1, d_1, z̃_1] → [action_2, τ_2, d_2, z̃_2] → ... → [action_T, τ_T, d_T, z̃_T]

Where:
- action_t: encoded action (mouse + keyboard components summed)
- τ_t: signal level at timestep t
- d_t: step size at timestep t  
- z̃_t: corrupted representation = (1-τ)z₀ + τz₁
```

**Action Encoding:**

```python
def encode_actions(actions, S_a=4):
    """
    Encode multi-component actions into tokens.
    
    Args:
        actions: dict with 'keyboard' (binary), 'mouse' (categorical)
        S_a: number of action tokens
    """
    # Encode each component separately
    keyboard_emb = linear_project(actions['keyboard'])  # continuous
    mouse_emb = embedding_lookup(actions['mouse'])       # categorical
    
    # Sum components with learned base embedding
    action_tokens = keyboard_emb + mouse_emb + learned_action_embedding
    
    return action_tokens  # [S_a, D]
```

**Shortcut Forcing Objective (Eq. 6-7):**

```python
def shortcut_forcing_loss(
    dynamics_model,
    z1,           # clean tokenized representations [T, N_z, D]
    actions,      # action sequence [T]
    K_max=64      # maximum sampling steps
):
    """
    Train dynamics model with shortcut forcing.
    Uses x-prediction (not v-prediction) to prevent error accumulation.
    
    Key insight: x-prediction produces structured targets that reduce
    high-frequency errors during long autoregressive rollouts.
    """
    B, T = z1.shape[:2]
    
    # Sample noise
    z0 = torch.randn_like(z1)
    
    # Sample signal levels and step sizes per timestep
    tau, d = sample_shortcut_schedule(K_max, T)  # [T], [T]
    
    # Corrupt representations (diffusion forcing: different τ per timestep)
    z_tilde = (1 - tau.unsqueeze(-1)) * z0 + tau.unsqueeze(-1) * z1
    
    # Forward pass: predict clean representations
    z1_hat = dynamics_model(z_tilde, tau, d, actions)
    
    # Compute loss per timestep
    loss = 0
    for t in range(T):
        if d[t] == 1/K_max:  # Finest step size
            # Flow loss in x-space
            L_t = (z1_hat[t] - z1[t]).pow(2).mean()
        else:
            # Bootstrap loss: distill two half-steps
            with torch.no_grad():
                # First half-step (convert x-pred to v-pred)
                b_prime = (dynamics_model.forward_single(
                    z_tilde[t], tau[t], d[t]/2, actions[t]
                ) - z_tilde[t]) / (1 - tau[t])
                
                z_prime = z_tilde[t] + b_prime * (d[t]/2)
                
                # Second half-step
                b_double_prime = (dynamics_model.forward_single(
                    z_prime, tau[t] + d[t]/2, d[t]/2, actions[t]
                ) - z_prime) / (1 - (tau[t] + d[t]/2))
                
                v_target = (b_prime + b_double_prime) / 2
            
            # Convert prediction to v-space and compute loss
            v_pred = (z1_hat[t] - z_tilde[t]) / (1 - tau[t])
            
            # Scale factor brings bootstrap loss to same range as x-space flow loss
            scale = (1 - tau[t]).pow(2)
            L_t = scale * (v_pred - v_target).pow(2).mean()
        
        # Ramp weight: focus on high signal levels (more learning signal)
        w_t = 0.9 * tau[t] + 0.1  # Eq. 8
        loss = loss + w_t * L_t
    
    return loss / T
```

**Inference (Autoregressive Generation):**

```python
def generate_video(
    dynamics_model,
    tokenizer,
    first_frame,
    actions,         # [T] action sequence
    K=4,             # sampling steps per frame
    tau_ctx=0.1      # context noise for robustness
):
    """
    Interactive video generation with shortcut model.
    Achieves real-time inference (20+ FPS) on single GPU.
    """
    d = 1/K  # step size
    
    # Encode first frame
    z_history = [tokenizer.encode(first_frame)]
    
    for t in range(1, len(actions)):
        # Initialize from noise
        z_t = torch.randn_like(z_history[0])
        
        # Slightly corrupt history for robustness
        z_ctx = [(1 - tau_ctx) * torch.randn_like(z) + tau_ctx * z 
                 for z in z_history]
        
        # K denoising steps
        for step in range(K):
            tau = step * d
            z_t = dynamics_model(
                z_ctx + [z_t],
                tau=[tau_ctx] * len(z_ctx) + [tau],
                d=[0] * len(z_ctx) + [d],
                actions=actions[:t+1]
            )[-1]  # get last timestep prediction
        
        z_history.append(z_t)
    
    # Decode to pixels
    video = tokenizer.decode(torch.stack(z_history))
    return video
```

### 3.3 Imagination Training

To solve control tasks:
1. Adapt pretrained world model to predict actions and rewards (conditioned on task)
2. Finetune policy through RL on imagined rollouts (no environment interaction)

**Agent Token Integration:**
- Insert agent tokens as additional modality into transformer
- Interleaved with image representations, actions, register tokens
- Agent tokens receive task embeddings as input
- Predict policy and reward from agent tokens via MLP heads
- **Critical:** Agent tokens attend to all modalities, but no other modalities attend back (prevents causal confusion)

**Behavior Cloning + Reward Model (Eq. 9):**

```python
def behavior_cloning_loss(
    world_model,
    z,              # encoded video representations
    actions,        # ground truth actions
    tasks,          # task embeddings (one-hot or text)
    rewards,        # sparse binary rewards
    L=8             # multi-token prediction length
):
    """
    Train policy and reward heads with multi-token prediction.
    Applied during Phase 2 (agent finetuning).
    """
    # Get task output embeddings from world model
    h = world_model.get_task_embeddings(z, tasks)  # [T, D]
    
    policy_loss = 0
    reward_loss = 0
    
    for t in range(len(h) - L):
        for n in range(L):
            # Policy: predict future actions
            action_logits = policy_head[n](h[t])
            policy_loss -= log_prob(actions[t+n], action_logits)
            
            # Reward: predict future rewards (symexp twohot for scale robustness)
            reward_logits = reward_head[n](h[t])
            reward_loss -= log_prob_twohot(rewards[t+n], reward_logits)
    
    return policy_loss + reward_loss
```

**Value Head Training - TD Learning (Eq. 10):**

```python
def value_loss(
    value_head,
    imagined_states,   # [T] states from world model rollout
    rewards,           # [T] predicted rewards
    values,            # [T] predicted values
    gamma=0.997,       # discount factor
    lambda_=0.95       # TD(λ) parameter
):
    """
    Train value head to predict λ-returns.
    Uses symexp twohot output for scale robustness.
    """
    T = len(rewards)
    
    # Compute λ-returns (backwards)
    R_lambda = [None] * T
    R_lambda[T-1] = values[T-1]  # bootstrap from final value
    
    for t in reversed(range(T-1)):
        c_t = 1.0  # continuation (1 if non-terminal, 0 if terminal)
        R_lambda[t] = rewards[t] + gamma * c_t * (
            (1 - lambda_) * values[t] + lambda_ * R_lambda[t+1]
        )
    
    # Loss: negative log probability of λ-returns under twohot distribution
    loss = 0
    for t in range(T):
        value_logits = value_head(imagined_states[t])
        loss -= log_prob_twohot(R_lambda[t], value_logits)
    
    return loss / T
```

**Policy Optimization - PMPO (Eq. 11):**

```python
def pmpo_policy_loss(
    policy_head,
    imagined_states,    # [N] all states across batch and time
    imagined_actions,   # [N] sampled actions
    advantages,         # [N] A_t = R^λ_t - v_t
    policy_prior,       # frozen behavioral cloning policy
    alpha=0.5,          # balance positive/negative
    beta=0.3            # prior regularization strength
):
    """
    PMPO: Probabilistic MPO - robust RL objective.
    
    Key insight: Uses SIGN of advantages, ignores magnitude.
    This eliminates need for return/advantage normalization and
    ensures equal focus on all tasks despite different reward scales.
    """
    N = len(advantages)
    
    # Split states by advantage sign
    D_plus = [i for i in range(N) if advantages[i] >= 0]
    D_minus = [i for i in range(N) if advantages[i] < 0]
    
    # Positive set: maximize likelihood (reinforce good actions)
    pos_loss = 0
    for i in D_plus:
        pos_loss -= log_prob(imagined_actions[i], policy_head(imagined_states[i]))
    pos_loss = pos_loss / max(len(D_plus), 1)
    
    # Negative set: minimize likelihood (discourage bad actions)
    neg_loss = 0
    for i in D_minus:
        neg_loss += log_prob(imagined_actions[i], policy_head(imagined_states[i]))
    neg_loss = neg_loss / max(len(D_minus), 1)
    
    # KL to behavioral prior (reverse direction: KL[π || π_prior])
    # Constrains policy to space of reasonable behaviors
    kl_loss = 0
    for i in range(N):
        pi = policy_head(imagined_states[i])
        pi_prior = policy_prior(imagined_states[i])
        kl_loss += kl_divergence(pi, pi_prior)
    kl_loss = kl_loss / N
    
    # Combined loss (all terms in nats, no normalization needed)
    loss = alpha * pos_loss + (1 - alpha) * neg_loss + beta * kl_loss
    
    return loss
```

**Full Imagination Training Loop:**

```python
def imagination_training(
    world_model,
    policy_head,
    value_head,
    policy_prior,      # frozen copy of BC policy
    dataset,
    num_iterations=10000,
    imagination_horizon=16
):
    """
    Phase 3: Improve policy beyond dataset behaviors.
    
    Key: Learn purely inside world model, no environment interaction.
    """
    # Freeze world model transformer, only train policy + value heads
    world_model.freeze_backbone()
    
    for iteration in range(num_iterations):
        # Sample context from dataset
        context = dataset.sample_context()
        z_ctx = world_model.tokenizer.encode(context.frames)
        
        # Imagine rollout (one per context for data diversity)
        z_trajectory = [z_ctx[-1]]
        a_trajectory = []
        
        for t in range(imagination_horizon):
            # Sample action from policy
            a_t = policy_head.sample(z_trajectory[-1])
            a_trajectory.append(a_t)
            
            # Predict next state from world model
            z_next = world_model.dynamics.generate_next(
                z_trajectory, a_trajectory, K=4
            )
            z_trajectory.append(z_next)
        
        # Annotate trajectory
        rewards = [world_model.reward_head(z) for z in z_trajectory]
        values = [value_head(z) for z in z_trajectory]
        
        # Compute advantages
        R_lambda = compute_lambda_returns(rewards, values, gamma=0.997)
        advantages = [R_lambda[t] - values[t] for t in range(len(values))]
        
        # Update value head
        value_loss = compute_value_loss(value_head, z_trajectory, R_lambda)
        value_loss.backward()
        
        # Update policy head
        policy_loss = pmpo_policy_loss(
            policy_head, z_trajectory, a_trajectory, 
            advantages, policy_prior
        )
        policy_loss.backward()
        
        optimizer.step()
```

### 3.4 Efficient Transformer

Block-causal transformer architecture used for both tokenizer and dynamics model.

**Base Architecture:**
- Pre-layer RMSNorm
- RoPE (Rotary Position Embeddings)
- SwiGLU activations
- QKNorm (stability)
- Attention logit soft capping (stability)

**Efficiency Optimizations:**

| Optimization | Training Speedup | Inference Speedup | Quality Impact |
|--------------|------------------|-------------------|----------------|
| Separate space/time attention | ✓ | ✓ | Neutral |
| Temporal attention every 4 layers | 2.5× | 2× | Improved (inductive bias) |
| GQA (grouped query attention) | Minor | 1.2× | Neutral |
| Time-factorized long context | Minor | 1.3× | Slight decrease |
| Register tokens | None | None | Temporal consistency |
| More spatial tokens (256) | -3× | -1.3× | Major improvement |

**Factorized Space-Time Attention:**

```python
class EfficientTransformerBlock(nn.Module):
    def __init__(self, dim, num_heads, is_temporal_layer=False):
        self.is_temporal = is_temporal_layer
        
        if is_temporal_layer:
            # Causal attention across time (every 4th layer)
            self.attn = CausalTimeAttention(dim, num_heads)
        else:
            # Full attention within each frame
            self.space_attn = SpaceAttention(dim, num_heads)
    
    def forward(self, x, T, S):
        """
        x: [B, T*S, D] flattened video tokens
        T: number of timesteps
        S: spatial tokens per timestep
        """
        if self.is_temporal:
            # Reshape to [B*S, T, D] for time attention
            x = rearrange(x, 'b (t s) d -> (b s) t d', t=T, s=S)
            x = self.attn(x)  # causal in time
            x = rearrange(x, '(b s) t d -> b (t s) d', s=S)
        else:
            # Reshape to [B*T, S, D] for space attention
            x = rearrange(x, 'b (t s) d -> (b t) s d', t=T, s=S)
            x = self.space_attn(x)  # full attention within frame
            x = rearrange(x, '(b t) s d -> b (t s) d', t=T)
        
        return x
```

**Alternating Batch Lengths (Training):**

```python
def train_with_alternating_lengths(model, dataset, T_short=64, T_long=256):
    """
    Train on many short batches, occasional long batches.
    
    Benefits:
    - Short batches: Fast iteration, frequent metrics
    - Long batches: Prevent overfitting to always seeing start frame
    - Finetune on long-only afterwards for length generalization
    """
    for step in range(num_steps):
        if step % 10 == 0:  # Every 10th batch is long
            batch = dataset.sample(seq_len=T_long)
        else:
            batch = dataset.sample(seq_len=T_short)
        
        loss = model(batch)
        loss.backward()
        optimizer.step()
```

**Model Specifications (Minecraft):**

| Component | Parameters | Spatial Tokens | Context Length |
|-----------|------------|----------------|----------------|
| Tokenizer | 400M | - | - |
| Dynamics | 1.6B | 256 | 192 frames |
| **Total** | **2B** | - | 9.6 seconds @ 20 FPS |

**Inference Speed Comparison:**

| Model | Parameters | Resolution | Context | FPS (1×H100) |
|-------|------------|------------|---------|--------------|
| MineWorld | 1.2B | 384×224 | 0.8s | 2 |
| Lucid-v1 | 1.1B | 640×360 | 1.0s | 44 |
| Oasis (small) | 500M | 640×360 | 1.6s | 20 |
| Oasis (large) | ~2B+ | 360×360 | 1.6s | ~5 |
| **Dreamer 4** | **2B** | **640×360** | **9.6s** | **21** |

Dreamer 4 achieves **6× longer context** than prior models while maintaining real-time inference.

---

## 4. Experiments

### 4.1 Offline Diamond Challenge

**Task:** Obtain diamonds in Minecraft from raw pixels and low-level mouse/keyboard actions.
- Human players: ~20 minutes average (24,000 actions)
- Episodes: 60 minutes, random worlds, empty inventory
- Data: VPT contractor dataset (2,541 hours)
- **No environment interaction** (purely offline)

**Results - Success Rates (%) over 1000 episodes:**

| Item | VPT (finetuned) | BC | VLA (Gemma 3) | Dreamer 4 |
|------|-----------------|-----|---------------|-----------|
| Log | 84 | 97 | 98 | **99** |
| Planks | 65 | 96 | 98 | **99** |
| Crafting table | 4.7 | 93 | 97 | **99** |
| Stick | 53 | 95 | 98 | **99** |
| Wooden pickaxe | 0 | 86 | 94 | **97** |
| Cobblestone | 6.9 | 84 | 92 | **96** |
| Stone pickaxe | 0 | 54 | 77 | **90** |
| Iron ore | 0.1 | 26 | 46 | **67** |
| Furnace | 0 | 16 | 42 | **58** |
| Iron ingot | 0.1 | 4.3 | 23 | **40** |
| Iron pickaxe | 0 | 0.6 | 11 | **29** |
| **Diamond** | 0 | 0 | 0 | **0.7** |

**Key findings:**
- Dreamer 4 is **first agent to obtain diamonds purely offline**
- Uses **100× less data** than VPT (2.5K vs 270K hours)
- Imagination training improves success rates AND efficiency (faster completion times)
- World model representations outperform Gemma 3 for behavioral cloning

### 4.2 Human Interaction (World Model Quality)

Human players attempt tasks inside the world model in real-time.

**Task Success Comparison:**

| Model | Tasks Completed (of 16) |
|-------|------------------------|
| Lucid-v1 | 0/16 |
| Oasis (large) | 5/16 |
| **Dreamer 4** | **14/16** |

**What Dreamer 4 accurately predicts:**
- Switching items
- Placing and breaking blocks
- Fighting monsters
- Placing and riding boats
- Entering portals
- Crafting table / furnace interfaces

**Failure modes of other models:**
- Lucid-v1: Generations diverge quickly, object interactions ignored
- Oasis: "Autocompletion" - hallucinates structures player never built

### 4.3 Action Generalization

**How much action data is needed?**

Training on 2,541 hours of video with varying amounts of paired actions:

| Action Data (hours) | PSNR (% of full) | SSIM (% of full) |
|---------------------|------------------|------------------|
| 0 | 0% | 0% |
| 10 | 53% | 75% |
| **100** | **85%** | **100%** |
| 1000 | 95% | 100% |
| 2541 (all) | 100% | 100% |

**Key insight:** World models absorb majority of knowledge from unlabeled videos, need only small amount of actions.

**Out-of-distribution generalization:**

Trained with Overworld actions only, tested on Nether/End (never seen actions for these):
- Achieves **76% PSNR** and **80% SSIM** of model trained with all actions
- Action conditioning generalizes to completely new visual environments

### 4.4 Model Design Ablations

**Cascade of improvements (measured by FVD on 20-second videos):**

| Configuration | Train (s/step) | Inference (FPS) | FVD ↓ |
|---------------|----------------|-----------------|-------|
| Baseline (DF + v-pred, K=64) | 9.8 | 0.8 | 306 |
| + Fewer steps (K=4) | 9.8 | 9.1 | 875 |
| + Shortcut model | 9.8 | 9.1 | 329 |
| + X-Prediction | 9.8 | 9.1 | 326 |
| + X-Loss | 9.8 | 9.1 | 151 |
| + Ramp weight | 9.8 | 9.1 | 102 |
| + Alternating batch lengths | 1.5 | 9.1 | 80 |
| + Long context every 4 layers | 0.6 | 18.9 | 70 |
| + GQA | 0.5 | 23.2 | 71 |
| + Time factorized long context | 0.4 | 30.1 | 91 |
| + Register tokens | 0.5 | 28.9 | 91 |
| + More spatial tokens (128) | 0.8 | 25.7 | 66 |
| + More spatial tokens (256) | 1.7 | 21.4 | **57** |

**Final vs baseline:** FVD 57 vs 306 (5.4× better quality)

---

## 5. Related Work

### Minecraft Agents

| Agent | Inputs | Actions | Offline Data | Online Data |
|-------|--------|---------|--------------|-------------|
| Dreamer 3 | 64×64 + inventory | keyboard, camera, abstract crafting | — | 1.4K hours |
| VPT (RL) | 128×128 | keyboard, mouse | 2.5K + 270K hours | 194K hours |
| VPT (BC) | 128×128 | keyboard, mouse | 2.5K + 270K hours | — |
| **Dreamer 4** | **360×640** | **keyboard, mouse** | **2.5K hours** | **—** |

Dreamer 4 uses **100× less data** than VPT with higher resolution inputs and no online interaction.

### World Model Agents

- **Visual Foresight, PlaNet** (2017-2018): First world models accurate enough for planning from pixels
- **Dreamer 1-3** (2019-2025): State-of-the-art for control with high-dimensional inputs
- **Transformer/Diffusion world models**: High data efficiency for discrete control but limited capacity

### Scalable World Models

| Model | Capabilities | Limitations |
|-------|--------------|-------------|
| Genie 3 | Diverse scene generation, simple interactions | Struggles with precise physics |
| Oasis | Simple game mechanics, real-time on special hardware | Hallucinates structures |
| Lucid | Real-time inference | Predictions diverge quickly |
| MineWorld | Open weights | Slower than real-time |
| GameNGen | Playable Doom simulator | Single level only |
| DIAMOND | CS:GO short-term predictions | Limited temporal consistency |

### Fast Generation Techniques

- **MaskGit**: Parallel discrete token generation
- **Distillation**: Two-phase training for fewer steps
- **Consistency models**: Straight paths but require careful schedules
- **Shortcut models**: Condition on step size, one-phase training

---

## 6. Discussion

**Achievements:**
- First agent to obtain diamonds in Minecraft purely from offline data
- Demonstrates learning successful long-horizon strategies in complex environments
- Enables applications where online interaction is impractical or unsafe

**Technical foundations:**
- Shortcut forcing objective for fast, accurate predictions
- Efficient transformer architecture for real-time inference
- X-prediction (not v-prediction) prevents error accumulation in long rollouts
- Ramp loss weight focuses capacity on high signal-level timesteps

**Current limitations:**
- Short memory (9.6 second context)
- Imprecise inventory predictions
- Not a full game clone

**Future directions:**
- Pretraining on general internet videos
- Long-term memory integration
- Language understanding
- Small amounts of corrective online data
- Automatic goal discovery for breaking up long tasks

---

## Key Hyperparameters Summary

| Parameter | Value | Purpose |
|-----------|-------|---------|
| K (sampling steps) | 4 | Real-time inference |
| K_max (training) | 64 | Shortcut model granularity |
| τ_ctx (context noise) | 0.1 | Robustness to imperfections |
| γ (discount) | 0.997 | Long-horizon credit assignment |
| λ (TD) | 0.95 | Bias-variance tradeoff |
| α (PMPO) | 0.5 | Balance positive/negative advantages |
| β (prior KL) | 0.3 | Behavioral constraint |
| L (MTP length) | 8 | Multi-token prediction horizon |
| Ramp weight | 0.9τ + 0.1 | Focus on informative signal levels |

---

## References

[1] Hafner et al. "Mastering diverse control tasks through world models." Nature, 2025. (Dreamer 3)

[2] Baker et al. "Video pretraining (VPT): Learning to act by watching unlabeled online videos." NeurIPS, 2022.

[3] Ball et al. "Genie 3: A new frontier for world models." DeepMind, 2025.

[4] Frans et al. "One step diffusion via shortcut models." arXiv:2410.12557, 2024.

[5] Chen et al. "Diffusion forcing: Next-token prediction meets full-sequence diffusion." NeurIPS, 2024.

[6] Lipman et al. "Flow matching for generative modeling." arXiv:2210.02747, 2022.

[7] Abdolmaleki et al. "Preference optimization as probabilistic inference." (PMPO) arXiv, 2024.

[8] Gloeckle et al. "Better & faster large language models via multi-token prediction." arXiv:2404.19737, 2024.

---

## Appendix A: Minecraft Task Set

**20 tasks for multi-task agent:**

| Index | Task |
|-------|------|
| 1 | mine_log |
| 2 | mine_cobblestone |
| 3 | mine_iron_ore |
| 4 | mine_coal |
| 5 | mine_diamond |
| 6 | craft_planks |
| 7 | craft_stick |
| 8 | craft_crafting_table |
| 9 | craft_furnace |
| 10 | craft_iron_ingot |
| 11 | craft_wooden_pickaxe |
| 12 | craft_stone_pickaxe |
| 13 | craft_iron_pickaxe |
| 14 | open_crafting_table |
| 15 | open_furnace |
| 16 | place_crafting_table |
| 17 | place_furnace |
| 18 | use_wooden_pickaxe |
| 19 | use_stone_pickaxe |
| 20 | use_iron_pickaxe |

---

## Appendix B: Dataset Details

**Minecraft VPT Dataset:**
- Source: OpenAI VPT contractor gameplay (subsets 6-10)
- Total: 2,541 hours
- Resolution: 360×640 at 20 FPS
- Split: 90% train, 10% eval (no shared 5-min chunks)
- Keyboard: 23 binary variables
- Mouse: μ-law encoded, 11×11=121 categorical

**Tokenizer Configuration:**
- Patch size: 16×16
- Spatial tokens: 960 (from 384×640 zero-padded frames)
- Bottleneck: 512×16 → reshaped to 256×32 for dynamics

**Dynamics Configuration:**
- Spatial tokens (N_z): 256
- Context length (C): 192 frames
- Batch lengths: 64 (short) / 256 (long)
- Training: 256-1024 TPU-v5p, batch size 1/device, FSDP

---

## Appendix C: Symexp Twohot Distribution

Used for reward and value predictions to handle varying scales robustly:

```python
def symexp_twohot(x, num_bins=255):
    """
    Symmetric exponential encoding with twohot distribution.
    
    Maps real values to a bounded discrete distribution that handles
    both small and large magnitudes gracefully.
    
    From Dreamer 3 (Hafner et al., 2025)
    """
    # Symmetric log transform
    def symlog(x):
        return torch.sign(x) * torch.log1p(torch.abs(x))
    
    def symexp(x):
        return torch.sign(x) * (torch.exp(torch.abs(x)) - 1)
    
    # Map to bin space
    x_log = symlog(x)
    bin_range = torch.linspace(-20, 20, num_bins)  # covers ~exp(20) = 485 million
    
    # Twohot: distribute probability between two adjacent bins
    idx = torch.searchsorted(bin_range, x_log)
    idx = idx.clamp(1, num_bins - 1)
    
    # Interpolation weights
    lower = bin_range[idx - 1]
    upper = bin_range[idx]
    weight_upper = (x_log - lower) / (upper - lower)
    weight_lower = 1 - weight_upper
    
    # Create distribution
    probs = torch.zeros(num_bins)
    probs[idx - 1] = weight_lower
    probs[idx] = weight_upper
    
    return probs
```

