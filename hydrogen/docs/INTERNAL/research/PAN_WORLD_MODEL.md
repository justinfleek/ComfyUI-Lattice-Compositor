# PAN: A World Model for General, Interactable, and Long-Horizon World Simulation

**arXiv:** 2511.09057  
**Authors:** PAN Team, Institute of Foundation Models (MBZUAI)  
**Venue:** Technical Report, 2025  
**Status:** IN_PROGRESS

---

## 1. Abstract

PAN is a general, interactable, and long-horizon world model that predicts future world states through high-quality video simulation conditioned on history and natural language actions. It employs the **Generative Latent Prediction (GLP)** architecture combining:
- Autoregressive LLM-based latent dynamics backbone
- Video diffusion decoder for perceptual realization
- Unification of latent space reasoning and world dynamics

---

## 2. GLP Architecture

### 2.1 Core Components

**Definition 1 (GLP - Generative Latent Prediction):** A world model framework that unifies latent dynamics with perceptual grounding through three components:

1. **Encoder h:** Maps observation to latent representation
   ```
   ŝ_t ~ p_h(· | o_t)
   ```

2. **Predictive Module f:** Models latent world dynamics
   ```
   ŝ_{t+1} ~ p_f(· | ŝ_t, a_t)
   ```

3. **Decoder g:** Reconstructs observable outcomes
   ```
   ô_{t+1} ~ p_g(· | ŝ_{t+1})
   ```

### 2.2 Generative Process

**Equation 4 (Joint Distribution):**
```
p_PAN(o_{t+1} | o_t, a_t) = Σ_{ŝ_t, ŝ_{t+1}} p_h(ŝ_t | o_t) · p_f(ŝ_{t+1} | ŝ_t, a_t) · p_g(o_{t+1} | ŝ_{t+1})
```

### 2.3 Learning Objective

**Equation 5 (Training Loss):**
```
L_PAN = E_{(o_t, a_t, o_{t+1})~D} [ disc(ô_{t+1}, o_{t+1}) ]
```

Where disc is a discrepancy measure between predicted and ground-truth observations.

---

## 3. PAN Architecture

### 3.1 Three-Component System

```
┌─────────────┐     ┌─────────────────┐     ┌─────────────────┐
│   Vision    │     │   LLM Backbone  │     │   Video Diff   │
│  Encoder    │────▶│  (Qwen2.5-VL)  │────▶│    Decoder     │
└─────────────┘     └─────────────────┘     └─────────────────┘
     │                      │                       │
   o_t                   a_t                    ô_{t+1}
```

### 3.2 Components

| Component | Model | Purpose |
|-----------|-------|---------|
| Vision Encoder | Qwen2.5-VL-7B | Encode observations to latents |
| World Model | Autoregressive LLM | Predict latent dynamics |
| Video Decoder | Wan2.1-T2V-14B | Reconstruct video from latents |

---

## 4. Causal Swin-DPM

### 4.1 Problem: Error Accumulation

Long-horizon video generation suffers from:
- Error accumulation across frames
- Temporal drift in latent space
- Compound artifacts in diffusion process

### 4.2 Solution: Chunk-wise Causal Attention

**Definition 2 (Causal Swin-DPM):** Diffusion process with chunk-wise causal attention masks ensuring smooth transitions between consecutive chunks.

**Key features:**
- Sliding window denoising
- Conditioning on slightly noised last frame
- Chunk-wise causal attention masks

### 4.3 Long-Horizon Strategy

1. Generate chunk i conditioned on chunk i-1
2. Add small noise to chunk i-1 output
3. Use as conditioning for chunk i+1
4. Reduces drift and maintains consistency

---

## 5. Key Definitions

1. **GLP:** Generative Latent Prediction - unified latent dynamics + perceptual grounding
2. **Causal Swin-DPM:** Causal Shift-Window Denoising Process Model
3. **Latent Dynamics:** Evolution of world state in compact representation
4. **Action Conditioning:** Natural language actions controlling world evolution

---

## 6. Relation to Hydrogen

### 6.1 World Model Integration

```purescript
-- World model state
data WorldState
  = WorldState
      { latent :: Tensor          -- Current latent representation
      , history :: [Tensor]      -- Past observations
      }

-- Action types
data WorldAction
  = NaturalLanguage Text
  | AgentAction Action
  | NoAction

-- Step world forward
stepWorld ::
  WorldState ->
  WorldAction ->
  WorldState
```

### 6.2 Simulation Loop

```purescript
simulate ::
  forall msg.
  Int ->                    -- Horizon
  WorldState ->            -- Initial state
  Stream WorldAction ->    -- Action stream
  Stream (Element msg)     -- Visual output
```

---

## 7. Bibliography

1. PAN Team "PAN: A World Model for General, Interactable, and Long-Horizon World Simulation" MBZUAI 2025

---

*Document generated: 2026-02-26*
