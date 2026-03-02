# AI Mother Tongue: Self-Emergent Communication in MARL via Endogenous Symbol Systems

**arXiv:** 2507.10566  
**Author:** Liu Hung Ming (PARRAWA AI)  
**Date:** July 16, 2025  
**Domain:** Multi-Agent Reinforcement Learning / Emergent Communication / Neurosymbolic AI

---

## Abstract

This paper challenges the fundamental assumption that artificial inductive biases are necessary for emergent communication in Decentralized Multi-Agent Reinforcement Learning (MARL). Through the "AI Mother Tongue" (AIM) framework based on Vector Quantized Variational Autoencoders (VQ-VAE), the authors demonstrate that when agents possess an endogenous symbol system, neural representations naturally exhibit spontaneous semantic compression and Nash equilibrium-driven semantic convergence—achieving effective symbolic communication WITHOUT external inductive biases.

**Key Insight:** This aligns with neuroscience findings that human brains don't directly use human language for internal thought, and resonates with "soft thinking" research in LLMs.

---

## 1. Problem: The Joint Exploration Dilemma

### 1.1 Background

Multi-agent reinforcement learning (MARL) enables complex collaborative tasks by modeling agent interactions in dynamic environments. However, establishing effective communication remains a significant challenge:

| Problem | Description |
|---------|-------------|
| **Joint Exploration Dilemma** | Agents fail to explore cooperative strategies |
| **Communication Vacuum Equilibrium** | Communication collapses due to insufficient incentives |
| **Centralization Limitations** | RIAL/DIAL rely on centralized training mechanisms that limit scalability |

### 1.2 Traditional Fix: Inductive Biases

Previous approaches introduce artificial biases:
- **Positive Signaling Bias**: Compel senders to produce state-discriminative messages
- **Positive Listening Bias**: Require receivers to generate differentiated actions for distinct messages
- **Opponent-Learning Awareness (OLA)**: Model other agents' policies

### 1.3 The Question

> Is this artificial inductive bias truly "over-engineering"?

The authors argue: **No external inductive biases needed** when agents possess an endogenous symbol system.

---

## 2. Methodology: AIM Framework

### 2.1 Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    AIM Framework Architecture                   │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Task Signal (Stask) ──► Encoder ──► Continuous Latent (ze)   │
│                                      │                          │
│                                      ▼                          │
│                           Vector Quantizer                       │
│                                      │                          │
│                                      ▼                          │
│                           Discrete Symbols (AIM) ──► Communication
│                                      │                          │
│                                      ▼                          │
│                                  Decoder                        │
│                                      │                          │
│                                      ▼                          │
│                           Reconstructed Input                   │
│                                                                 │
│  REINFORCE + Reflection Strategies ──► Policy Learning         │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### 2.2 VQ-VAE Core Components

#### Encoding Stage
```
ze = Encoder(x)
```
Transforms input (e.g., image x ∈ R^(C×H×W)) into continuous latent representation ze ∈ R^D.

#### Quantization Stage (Core Innovation)
```
zq = arg min_{ek ∈ C} ||ze - ek||²
```
- Codebook C = {ek}^K_{k=1} contains K discrete vectors
- Quantization forces continuous representations to align with discrete symbols
- This creates the "shared language" between agents

#### Decoding Stage
```
x̂ = Decoder(zq)
```
Reconstructs input from quantized discrete representation.

### 2.3 Agent Architecture

#### Agent A: Active Communicator (Actor-Critic)
- **Policy Network (πA)**: Outputs AIM sequence based on image encoding and environment label
  ```
  aA = πA(ze, l; θA),  aA ∈ {0, 1, ..., K-1}
  ```
- **Centralized Value Network (V)**: Evaluates joint state value
  ```
  V(sA, aB; ϕA) = ValueNet(ze, l, Embed(aB))
  ```
- **Opponent AIM Predictor**: Predicts Agent B's AIM sequence
- **Intent Predictor**: Predicts action intention (Cooperate/Defect)

#### Agent B: Responsive Communicator
- **Policy Network (πB)**: Generates response based on Agent A's AIM sequence, label, and image encoding
  ```
  aB = πB(aA, l, ze; θB),  aB ∈ {0, 1, ..., K-1}
  ```
- **Opponent AIM Predictor**: Predicts Agent A's AIM sequence
- **Intent Decoder**: Decodes Agent A's action intention

### 2.4 Policy Learning: REINFORCE with Reflection Strategies

#### Standard REINFORCE
```
∇J(θ) ≈ Σ ∇log π(at|st; θ) · Gt
```

#### Multi-Level Loss Function
```
L_A = L_policy + L_value + λ_ε·L_entropy + λ_r·L_intent + λ_r·L_predictive
L_B = L_policy + λ_ε·L_entropy + λ_r·L_intent + λ_r·L_predictive
```

**Loss Components:**
| Loss | Purpose |
|------|---------|
| L_policy | REINFORCE policy gradient |
| L_value | Value prediction in context (MSE) |
| L_entropy | Encourage exploration |
| L_intent | Ensure communication semantic consistency |
| L_predictive | Theory of Mind - predict opponent behavior |

### 2.5 Reflection Strategies

#### Method 1: Contextual Value Learning
```
L_A,value = ||VA(Embed(aA)|Stask,A) - Rjoint||²
L_B,value = ||VB(Embed(aA)|Stask,B) - Rjoint||²
```
Agents learn the expected reward of their generated AIM sequence.

#### Method 2: Predictive Bias
```
L_A,predictive = ||R̂B|A(Embed(aA)|Stask,A) - RB,indiv||²
L_B,predictive = ||R̂A|B(Embed(aA)|Stask,B) - RA,indiv||²
```
Agents predict opponent's individual rewards—developing Theory of Mind.

### 2.6 Reward Function (Prisoner's Dilemma)

```
(rA, rB) = 
  (4 + I[II mod 2 = 0], 4 + I[II mod 2 = 0])   if aA=C, aB=C  (mutual cooperation)
  (-1 - I[II mod 2 = 1], 5)                      if aA=C, aB=D  (exploitation)
  (5, -1 - I[II mod 2 = 1])                      if aA=D, aB=C  (reverse exploitation)
  (0, 0)                                          if aA=D, aB=D  (mutual defection)
```

### 2.7 AIM Sequence to Action Mapping

```
Action(a) = 
  C  if a1 < K/2
  D  otherwise
```

---

## 3. Key Theoretical Contributions

### 3.1 Neural Communication Hypothesis
> Neural networks inherently encode the potential for efficient communication.

### 3.2 Tool-First Principle
> Research should shift towards providing symbolic tools rather than inductive mechanisms.

### 3.3 Semantic Interpretability Paradigm
> Establish observational methodologies for mapping symbols to policies.

### 3.4 Power-Law Distribution of Symbols

Experimental results confirm: **Symbol usage exhibits significant power-law distribution**, confirming the hypothesis of "dominance of few effective codes."

---

## 4. Relation to Hydrogen

### 4.1 Agent Swarm Communication (Critical)

For **billion-agent scale** swarms, this paper provides:

| Hydrogen Need | AIM Solution |
|---------------|-------------|
| **Hierarchical group messaging** | VQ-VAE codebook as shared vocabulary |
| **Decentralized communication** | No centralized training required |
| **Scalable coordination** | Emergent protocols without predefined structures |
| **Interpretability** | AIM Dictionary for real-time symbol tracking |

### 4.2 Implementation Considerations

**For Hydrogen's agent runtime:**

1. **Codebook Design**
   - K symbols for base vocabulary
   - Hierarchical VQ-VAE (HQ-VAE) for complex semantics
   - Dynamic codebook sizing based on task complexity

2. **Communication Protocol**
   ```
   Agent State → Encoder → Quantizer → AIM Symbol → Channel → Agent B
   ```

3. **Reflection Strategy Integration**
   - Value prediction for communication quality
   - Theory of Mind for opponent modeling
   - Intent prediction for coordination

### 4.3 NOT Directly Applicable

- UI rendering
- DOM diffing/patching
- WebGPU compute shaders

---

## 5. References

1. Foerster et al. "Learning to Communicate with Deep Multi-Agent Reinforcement Learning" (RIAL/DIAL)
2. Eccles et al. "Learning to Communicate with Deep Multi-Agent RL"
3. Tan "Multi-Agent Reinforcement Learning"
4. Littman "Markov Games"
5. Tucker et al. "Commutative Matrix"
6. Yang et al. "Learning to Incentivize Communication"
7. Razavi et al. "VQ-VAE-2"
8. Takida et al. "SQ-VAE"
9. Takida et al. "HQ-VAE"
10. Zhang et al. "Soft Thinking"
11. Axelrod "The Evolution of Cooperation"
12. Axelrod & Hamilton "The Evolution of Cooperation in Biological Systems"
13. Perolat et al. "Multi-Agent Reinforcement Learning in Sequential Social Dilemmas"
14. Phan et al. "MATE: Mutual Acknowledgment Token Exchange"
15. Lupu & Precup "Gifting"
16. Yoshida & Taniguchi "MARL-CPC"

---

## 6. Citation

```bibtex
@misc{liu2025aim,
  title={AI Mother Tongue: Self-Emergent Communication in MARL via Endogenous Symbol Systems},
  author={Liu Hung Ming},
  year={2025},
  eprint={2507.10566},
  archivePrefix={arXiv},
  primaryClass={cs.AI}
}
```

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
