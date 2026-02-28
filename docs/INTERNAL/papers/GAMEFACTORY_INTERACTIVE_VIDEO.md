# GameFactory: Creating New Games with Generative Interactive Videos

**Authors:** Jiwen Yu (HKU), Yiran Qin (HKU), Xintao Wang (Kuaishou), Pengfei Wan (Kuaishou), Di Zhang (Kuaishou), Xihui Liu (HKU)

**arXiv:** 2501.08325v4 [cs.CV] 30 Oct 2025

**Project:** https://yujiwen.github.io/gamefactory/

---

## Abstract

GameFactory is a framework for **action-controlled, scene-generalizable** game video generation. Key contributions:

1. **GF-Minecraft Dataset**: Action-annotated game videos with unbiased action distribution (no human gameplay bias)
2. **Action Control Module**: Precise control over keyboard (discrete) and mouse (continuous) inputs
3. **Autoregressive Generation**: Unlimited-length interactive video via multi-frame generation per step
4. **Scene Generalization**: Multi-phase training with domain adapter decouples style from action control

**Core Insight**: Pre-trained video diffusion models contain rich generative priors. By decoupling game-style learning (LoRA) from action control learning (separate module), action controllability transfers to arbitrary open-domain scenes

## 1. Introduction

**Problem**: Current game video generation methods overfit to specific games (DOOM, Atari, Minecraft). They lack scene generalization — cannot create content beyond training data.

**Challenge**: Directly fine-tuning pre-trained video models on game data causes style collapse (outputs inherit Minecraft visual style).

**Solution**: Disentangle style learning from action control learning using separate modules trained in separate phases

## 2. Related Work

- **DIAMOND**: Atari, CS:GO — frame-level control, no scene generalization
- **GameNGen**: DOOM — frame-level control, no scene generalization  
- **Oasis**: Minecraft — key + mouse, no scene generalization
- **GameGenX**: AAA games — video-level control only
- **Matrix**: Racing games — 4 keys only, limited action space
- **Genie 2**: Unknown source — requires massive action-labeled data

GameFactory: 7 keys + mouse, scene-generalizable, with technical paper and dataset

## 3. Preliminaries

**Backbone**: Transformer-based latent video diffusion model (1B parameters)

**Notation**:
- `X = [x₀, x₁, ..., x_rn]` — video frames (1 + rn frames)
- `Z = [z₀, z₁, ..., z_n]` — latent representation (1 + n latents)
- `r` — temporal compression ratio (r = 4)
- `A = [a₁, a₂, ..., a_rn]` — actions, where `aᵢ` transfers from `xᵢ₋₁` to `xᵢ`
- `p` — text prompt
- `ϕ` — model parameters

**Action-Conditioned Loss**:
```
L_a(ϕ) = E[||ε_ϕ(Z_t, p, A, t) - ε||²₂]
```
Where `ε` is the added noise and `t` is the diffusion timestep

## 4. Action-Controlled Video Generation

### 4.1 GF-Minecraft Dataset

**Requirements for training data**:
1. Accessible with customizable action inputs
2. Action sequences free from human bias (include rare actions like backward movement, jumping in place)
3. Diverse scenes with textual descriptions

**GF-Minecraft properties**:
- 70 hours of gameplay video
- Unbiased action distribution (atomic actions with balanced distribution)
- Randomized frame duration per atomic action (no temporal bias)
- Multiple scenes, weather conditions, times of day
- Text annotations via MiniCPM multimodal LLM

**Key insight**: Human gameplay datasets (like VPT) have skewed distributions:
- W (forward): 50.11% vs S (backward): 0.32%
- Models trained on biased data fail on rare actions

**GF-Minecraft distribution**: ~13-15% per key (uniform)

### 4.2 Action Control Module

**Architecture**: Injected into transformer blocks after spatial-temporal self-attention

**Input types**:
- Mouse movement: `M ∈ R^(rn×d₁)` — continuous
- Keyboard actions: `K ∈ R^(rn×d₂)` — discrete (one-hot encoded)

**Intermediate feature**: `F ∈ R^((n+1)×l×c)` where `l` = token sequence length, `c` = channels

---

#### Algorithm 1: Action Grouping with Sliding Window

**Problem**: Temporal compression causes granularity mismatch — `rn` actions vs `n+1` features

**Solution**: Group actions using sliding window of size `w`

```python
def group_actions(actions, feature_idx, window_size, compression_ratio):
    """
    For i-th feature, consider actions in range:
    [a_{r×(i-w+1)}, ..., a_{r×i}]
    
    This captures delayed action effects (e.g., jump affects multiple frames)
    """
    start_idx = compression_ratio * (feature_idx - window_size + 1)
    end_idx = compression_ratio * feature_idx
    
    # Boundary padding for out-of-range indices
    grouped = []
    for j in range(start_idx, end_idx + 1):
        if j < 0:
            grouped.append(actions[0])  # Pad with first action
        elif j >= len(actions):
            grouped.append(actions[-1])  # Pad with last action
        else:
            grouped.append(actions[j])
    
    return grouped

# Result shapes:
# M_group ∈ R^((n+1) × rw × d₁)  for mouse
# K_group ∈ R^((n+1) × rw × c)   for keyboard (after embedding + positional encoding)
```

---

#### Algorithm 2: Mouse Movement Control (Concatenation)

**Key finding**: Continuous signals work better with concatenation (preserves magnitude)

```python
def mouse_control(M_group, F):
    """
    M_group: (n+1, rw, d₁) — grouped mouse movements
    F: (n+1, l, c) — intermediate features
    
    Returns: F_fused with mouse information
    """
    # Reshape: (n+1, rw, d₁) → (n+1, 1, rw*d₁)
    M_reshaped = M_group.reshape(n+1, 1, rw * d1)
    
    # Repeat along token sequence dimension: (n+1, 1, rw*d₁) → (n+1, l, rw*d₁)
    M_repeat = M_reshaped.repeat(1, l, 1)
    
    # Concatenate with features: (n+1, l, c+rw*d₁)
    F_fused = torch.cat([F, M_repeat], dim=-1)
    
    # Further processing through MLP and temporal self-attention
    F_out = temporal_self_attention(mlp(F_fused))
    
    return F_out
```

---

#### Algorithm 3: Keyboard Action Control (Cross-Attention)

**Key finding**: Discrete/categorical signals work better with cross-attention (similarity-based)

```python
def keyboard_control(K_group, F):
    """
    K_group: (n+1, rw, c) — grouped keyboard embeddings
    F: (n+1, l, c) — intermediate features
    
    Returns: F with keyboard control applied
    """
    # Cross-attention: K_group as Key and Value, F as Query
    # Similar to prompt cross-attention between text and features
    
    Q = F                    # Query from features
    K = K_group              # Key from keyboard actions
    V = K_group              # Value from keyboard actions
    
    # Standard cross-attention
    attention_weights = softmax(Q @ K.transpose(-2, -1) / sqrt(c))
    F_out = attention_weights @ V
    
    return F_out
```

**Why this matters**:
- Cross-attention for discrete: similarity computation matches categorical nature
- Concatenation for continuous: preserves magnitude (cross-attention reduces magnitude influence)

### 4.3 Autoregressive Long Video Generation

**Problem**: Standard video diffusion generates fixed-length outputs. Games need unlimited-length streams.

**Solution**: Allow different noise levels across frames — earlier frames generated first, later frames conditioned on them.

---

#### Algorithm 4: Autoregressive Training

```python
def autoregressive_training(latents, k, N):
    """
    latents: N+1 frame latents [z₀, z₁, ..., z_N]
    k: randomly selected — first k+1 frames are conditions
    N-k: frames to predict
    
    Key insight: Only compute loss on frames that need prediction
    """
    # Split into condition and prediction
    condition_frames = latents[:k+1]      # Clean, no noise added
    predict_frames = latents[k+1:N+1]     # Add noise for training
    
    # Add noise only to prediction frames
    noisy_predict = add_noise(predict_frames, timestep=t)
    
    # Concatenate for model input
    model_input = concat(condition_frames, noisy_predict)
    
    # Forward pass
    predicted_noise = model(model_input, prompt, actions, t)
    
    # CRITICAL: Loss only on predicted frames (not condition frames)
    # This eliminates noise interference from already-generated frames
    loss = mse_loss(
        predicted_noise[k+1:],  # Only prediction portion
        actual_noise[k+1:]
    )
    
    return loss
```

---

#### Algorithm 5: Autoregressive Inference

```python
def autoregressive_inference(initial_latents, actions, prompt, k, N):
    """
    Generates unlimited-length video by iterative multi-frame generation
    
    initial_latents: First N+1 frames (full-sequence generation)
    k: Number of condition frames per iteration
    N-k: New frames generated per iteration
    """
    history = initial_latents  # Start with full-sequence generation
    
    while generating:
        # Select most recent k+1 frames as conditions
        condition = history[-k-1:]
        
        # Get actions for next N-k frames
        next_actions = get_next_actions()
        
        # Generate N-k new frames conditioned on k+1 history frames
        new_frames = diffusion_sample(
            condition_frames=condition,
            actions=next_actions,
            prompt=prompt,
            num_steps=50  # DDIM sampling steps
        )
        
        # Merge into history
        history = concat(history, new_frames)
    
    return history
```

**Advantage over prior work**: Multi-frame generation per step (N-k frames) instead of next-frame prediction. Greatly reduces generation time for long videos

## 5. Open-Domain Game Scene Generalization

### 5.1 Style-Action Decoupling with Domain Adapter

**Problem**: Fine-tuning on Minecraft data embeds Minecraft visual style, compromising open-domain generalization.

**Key Insight**: Disentangle style and action control into different modules/parameters, then remove style module at inference.

**Implementation**:
- **Domain Adapter**: LoRA (Low-Rank Adaptation) for game-specific visual style
- **Action Control Module**: Separate module for action controllability

**Why LoRA for style**:
- Efficiently learns specific styles
- Can be "plugged out" without affecting base model's open-domain priors
- Keeps most original parameters frozen

### 5.2 Multi-Phase Training Strategy

---

#### Algorithm 6: Multi-Phase Training

```python
# Phase #0: Pretraining (already done)
# Large video diffusion model trained on open-domain data
pretrained_model = load_pretrained()  # 1B params, rich generative priors

# ═══════════════════════════════════════════════════════════════════════════
# Phase #1: Tune LoRA to Fit Game Videos
# ═══════════════════════════════════════════════════════════════════════════
def phase_1_style_adaptation(pretrained_model, game_data):
    """
    Fine-tune with LoRA to adapt to Minecraft style
    while preserving most original parameters.
    
    Better style adaptation here → Phase 2 focuses purely on action control
    """
    lora = LoRA(rank=128)
    
    # Freeze base model, only train LoRA
    pretrained_model.requires_grad_(False)
    lora.requires_grad_(True)
    
    optimizer = Adam(lora.parameters(), lr=1e-4)
    
    for batch in game_data:
        loss = diffusion_loss(pretrained_model + lora, batch)
        loss.backward()
        optimizer.step()
    
    return lora

# ═══════════════════════════════════════════════════════════════════════════
# Phase #2: Tune Action Control Module
# ═══════════════════════════════════════════════════════════════════════════
def phase_2_action_control(pretrained_model, lora, game_data_with_actions):
    """
    FREEZE: pretrained_model + lora
    TRAIN: only action_control_module
    
    Since Phase 1 handled style → loss focuses on action control
    This achieves style-independent control that generalizes
    """
    action_module = ActionControlModule()
    
    # Freeze everything except action module
    pretrained_model.requires_grad_(False)
    lora.requires_grad_(False)
    action_module.requires_grad_(True)
    
    optimizer = Adam(action_module.parameters(), lr=1e-5)
    
    for batch in game_data_with_actions:
        frames, actions, prompts = batch
        loss = action_conditioned_loss(
            pretrained_model + lora + action_module,
            frames, actions, prompts
        )
        loss.backward()
        optimizer.step()
    
    return action_module

# ═══════════════════════════════════════════════════════════════════════════
# Phase #3: Inference on Open Domain
# ═══════════════════════════════════════════════════════════════════════════
def phase_3_inference(pretrained_model, action_module, prompt, actions):
    """
    REMOVE: LoRA (game style)
    KEEP: action_control_module
    
    Action control works independently of game style
    → Open-domain generation with action controllability
    """
    # Note: NO lora — only pretrained + action_module
    model = pretrained_model + action_module
    
    video = generate(model, prompt, actions)
    return video
```

**Training details**:
- Each phase: 2-4 days on 8× A100, batch size 64
- LoRA: rank=128, lr=1e-4
- Action module: lr=1e-5
- Inference: CFG on text only, DDIM 50 steps

## 6. Experiments

**Model**: 1B transformer-based text-to-video diffusion (distilled from larger model)
**Resolution**: 360×640
**Temporal compression**: r = 4

### Ablation: Control Mechanisms

| Control Type | Best Method | Why |
|--------------|-------------|-----|
| Keyboard (discrete) | Cross-Attention | Similarity-based matching suits categorical signals |
| Mouse (continuous) | Concatenation | Preserves magnitude (cross-attn reduces magnitude influence) |

### Scene Generalization Results

| Strategy | Cam↓ | Flow↓ | Dom↑ | CLIP↑ | FID↓ | FVD↓ |
|----------|------|-------|------|-------|------|------|
| Multi-Phase (open-domain) | 0.0997 | 54.13 | 0.7565 | 0.3181 | 121.18 | 1256.94 |
| One-Phase (open-domain) | 0.1134 | 76.02 | 0.7345 | 0.3111 | 167.79 | 1323.58 |

Multi-phase maintains closer domain to original model (higher Dom), better action following (lower Cam/Flow), and better generation quality (lower FID/FVD).

### Dataset Comparison (GF-Minecraft vs VPT)

| Metric | VPT (human bias) | GF-Minecraft (uniform) |
|--------|------------------|------------------------|
| Cam↓ | 0.1324 | 0.0839 |
| Flow↓ | 107.67 | 43.48 |

Models trained on uniform distribution follow rare actions (backward, jump-in-place) correctly. VPT-trained models fail on these.

### Loss Scope for Autoregressive

| Loss Scope | Cam↓ | Flow↓ |
|------------|------|-------|
| All frames | 0.1547 | 148.73 |
| Only predicted frames | 0.0924 | 85.45 |

Computing loss only on frames requiring prediction eliminates noise interference from already-generated frames

## 7. Conclusion

**GameFactory enables**:
1. Action-controlled video generation (keyboard + mouse)
2. Scene-generalizable game creation (not bound to training game style)
3. Unlimited-length interactive video via autoregressive multi-frame generation

**Key technical insights**:
- Cross-attention for discrete actions, concatenation for continuous
- Multi-phase training decouples style (LoRA) from action control
- Loss only on predicted frames for autoregressive training
- Unbiased action datasets critical for handling rare actions

## Appendix: Algorithm Details

### Hydrogen Integration Notes

**Relevance to Temporal Pillar**:
- Autoregressive generation with varying noise levels maps to temporal composition
- Action sequences as discrete timestep transitions

**Relevance to Reactive Pillar**:
- Keyboard action encoding as discrete categorical (one-hot → embedding → cross-attention)
- Mouse movement as continuous signal (concatenation preserves magnitude)

**Relevance to Gestural Pillar**:
- Action grouping with sliding window captures delayed effects
- Window size `w` controls temporal receptive field for gesture interpretation

### Complete Action Control Integration

```python
class ActionControlModule:
    """
    Complete action control module for video diffusion transformer
    """
    def __init__(self, config):
        self.window_size = config.window_size  # w
        self.compression_ratio = config.compression_ratio  # r
        self.keyboard_embedding = nn.Embedding(config.num_keys, config.channels)
        self.positional_encoding = PositionalEncoding(config.channels)
        self.mouse_mlp = nn.Linear(config.mouse_dim * config.window_size * config.compression_ratio, config.channels)
        self.keyboard_cross_attn = CrossAttention(config.channels)
        self.temporal_self_attn = TemporalSelfAttention(config.channels)
    
    def forward(self, features, mouse_actions, keyboard_actions):
        """
        features: (batch, n+1, seq_len, channels)
        mouse_actions: (batch, r*n, mouse_dim) — continuous
        keyboard_actions: (batch, r*n, num_keys) — one-hot discrete
        """
        n_plus_1 = features.shape[1]
        
        # Group actions with sliding window
        mouse_grouped = self.group_with_window(mouse_actions, n_plus_1)
        keyboard_grouped = self.group_with_window(keyboard_actions, n_plus_1)
        
        # Keyboard: embed → positional → cross-attention
        keyboard_embedded = self.keyboard_embedding(keyboard_grouped.argmax(-1))
        keyboard_embedded = self.positional_encoding(keyboard_embedded)
        features = self.keyboard_cross_attn(
            query=features,
            key=keyboard_embedded,
            value=keyboard_embedded
        )
        
        # Mouse: reshape → repeat → concatenate → MLP → temporal attention
        mouse_flat = mouse_grouped.reshape(mouse_grouped.shape[0], n_plus_1, -1)
        mouse_repeated = mouse_flat.unsqueeze(2).expand(-1, -1, features.shape[2], -1)
        features_fused = torch.cat([features, mouse_repeated], dim=-1)
        features = self.mouse_mlp(features_fused)
        features = self.temporal_self_attn(features)
        
        return features
    
    def group_with_window(self, actions, n_features):
        """Group actions for each feature using sliding window"""
        r, w = self.compression_ratio, self.window_size
        grouped = []
        for i in range(n_features):
            start = r * (i - w + 1)
            end = r * i + 1
            window = []
            for j in range(start, end):
                if j < 0:
                    window.append(actions[:, 0])
                elif j >= actions.shape[1]:
                    window.append(actions[:, -1])
                else:
                    window.append(actions[:, j])
            grouped.append(torch.stack(window, dim=1))
        return torch.stack(grouped, dim=1)
```

---

**Document Status**: COMPLETE
**Synthesis Date**: 2026-02-26
**Synthesized By**: Opus 4.5

