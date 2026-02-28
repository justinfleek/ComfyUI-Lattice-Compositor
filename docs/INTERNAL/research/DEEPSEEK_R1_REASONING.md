# DeepSeek-R1: Incentivizing Reasoning Capability in LLMs via Reinforcement Learning

**arXiv:** 2501.12948  
**Authors:** DeepSeek-AI  
**Date:** January 4, 2026  
**Domain:** Large Language Models / Reinforcement Learning / Reasoning

---

## Abstract

DeepSeek-R1 achieves reasoning capabilities through **pure reinforcement learning** — no human-annotated reasoning trajectories required.

**Key Breakthrough:** Through GRPO (Group Relative Policy Optimization), the model:
- Emerges self-reflection
- Develops verification behaviors
- Creates dynamic strategy adaptation
- Achieves SOTA on math, coding, STEM

---

## 1. The Problem: Reasoning Limitations

### 1.1 Previous Approaches

| Method | Limitation |
|--------|------------|
| Chain-of-thought prompting | Requires careful few-shot examples |
| Supervised fine-tuning | Constrained by human reasoning patterns |
| Extensive human annotations | Not scalable, introduces biases |

### 1.2 Core Issue

> Human-defined reasoning patterns may limit model exploration

---

## 2. DeepSeek-R1-Zero

### 2.1 Approach

- **Base model:** DeepSeek-V3-Base
- **Algorithm:** GRPO (Group Relative Policy Optimization)
- **Reward:** Only correctness of final answers
- **No SFT phase** — pure RL from base model

### 2.2 GRPO Algorithm

For each question q, sample G outputs, optimize:

```
J_GRPO(θ) = E[ Σ_i min( clip(πθ/πold, 1-ε, 1+ε) * A_i, A_i ) ]
```

Where A_i is advantage relative to group mean.

### 2.3 Emergent Behaviors

Without explicit teaching, DeepSeek-R1-Zero developed:
- **Longer reasoning chains**
- **Self-reflection**
- **Verification steps**
- **Alternative approach exploration**

---

## 3. DeepSeek-R1

### 3.1 Addressing R1-Zero Limitations

| Issue | Solution |
|-------|----------|
| Poor readability | Multi-stage training |
| Language mixing | Rejection sampling + SFT |
| Limited scope | Additional non-reasoning data |

### 3.2 Training Pipeline

1. **Cold start:** Minimal SFT data
2. **GRPO:** Pure RL on reasoning tasks
3. **Rejection sampling:** Generate high-quality reasoning
4. **SFT:** Supervised fine-tuning on reasoning + general data
5. **GRPO:** Final RL alignment

---

## 4. Distilled Models

Released smaller models (1.5B - 70B) that:
- Outperform instruction-tuned baselines
- Enable broader access
- Provide research value

---

## 5. Relation to Hydrogen

### 5.1 Agent Reasoning

For **billion-agent swarms**:

| Need | R1 Insight |
|------|------------|
| **Emergent reasoning** | Pure RL can develop reasoning without SFT |
| **Self-verification** | Models learn to check their own work |
| **Scalable training** | GRPO reduces compute vs PPO |

### 5.2 Hybrid Integration

Could integrate with Hydrogen for:
- Dynamic strategy selection
- Self-correcting agent loops
- Emergent planning behaviors

---

## 6. References

1. GRPO (Group Relative Policy Optimization)
2. PPO (Proximal Policy Optimization)
3. DeepSeek-V3-Base
4. Chain-of-thought prompting

---

## 7. Citation

```bibtex
@misc{deepseek2025r1,
  title={DeepSeek-R1: Incentivizing Reasoning Capability in LLMs via Reinforcement Learning},
  author={DeepSeek-AI},
  year={2026},
  eprint={2501.12948},
  archivePrefix={arXiv},
  primaryClass={cs.CL}
}
```

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
