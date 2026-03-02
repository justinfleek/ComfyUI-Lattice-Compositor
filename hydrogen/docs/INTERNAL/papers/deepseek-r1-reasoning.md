# DeepSeek-R1: Incentivizing Reasoning Capability in LLMs via Reinforcement Learning

**Source**: arXiv:2501.12948v2 (January 2026)
**Authors**: DeepSeek-AI (research@deepseek.com)
**Domain**: LLM Reasoning, Reinforcement Learning, Chain-of-Thought

---

## Abstract

LLM reasoning abilities can be **incentivized through pure reinforcement
learning**, without human-labeled reasoning trajectories. Key findings:

1. RL facilitates **emergent development** of advanced reasoning patterns:
   self-reflection, verification, dynamic strategy adaptation
2. Model spontaneously increases "thinking time" during training
3. "Aha moments" emerge where model learns to rethink mid-solution
4. Emergent patterns can be **distilled** to smaller models

**Results**:
- DeepSeek-R1-Zero: 77.9% on AIME 2024 (surpasses human average)
- With self-consistency: 86.7% on AIME 2024
- Outperforms SFT-trained models on math, coding, STEM

## 1. Core Innovation: Pure RL for Reasoning

**Hypothesis**: Human-defined reasoning patterns limit model exploration.
Unrestricted RL can incentivize novel reasoning capabilities.

**Method**:
- Start from DeepSeek-V3-Base
- Apply GRPO (Group Relative Policy Optimization)
- Reward: correctness of final answer only
- **No SFT phase** — skip conventional supervised fine-tuning
- No constraints on reasoning process

**Why skip SFT?** Human reasoning traces:
1. Hinder scalability
2. Introduce cognitive biases
3. Cap performance at human-provided exemplar level
4. Prevent exploration of superior non-human reasoning pathways

**Template** (minimal constraint):
```
<think> reasoning process here </think>
<answer> answer here </answer>
```

## 2. DeepSeek-R1-Zero

Pure RL model trained without any supervised fine-tuning.

### 2.1 GRPO Algorithm

Group Relative Policy Optimization — simplifies PPO, reduces resource
consumption:

```python
def grpo_objective(policy, policy_old, policy_ref, question, G=16):
    """
    GRPO: Sample group of outputs, compute relative advantage.
    
    G: group size (16 outputs per question)
    """
    # Sample G outputs from old policy
    outputs = [policy_old.sample(question) for _ in range(G)]
    
    # Get rewards for each output
    rewards = [get_reward(o) for o in outputs]
    
    # Compute group-relative advantage (normalized within group)
    mean_r = mean(rewards)
    std_r = std(rewards)
    advantages = [(r - mean_r) / std_r for r in rewards]
    
    # PPO-style clipped objective with KL penalty
    loss = 0
    for o, A in zip(outputs, advantages):
        ratio = policy(o|question) / policy_old(o|question)
        clipped = clip(ratio, 1-epsilon, 1+epsilon)
        policy_loss = -min(ratio * A, clipped * A)
        
        # KL divergence to reference policy
        kl_loss = beta * kl_divergence(policy, policy_ref, o, question)
        
        loss += policy_loss + kl_loss
    
    return loss / G
```

**Key insight**: Advantage computed relative to group (Eq. 3), not global
baseline. Enables meaningful learning signal even when all outputs are good/bad.

### 2.2 Reward Design

Rule-based rewards only — no neural reward models (susceptible to reward hacking):

```
Reward_rule = Reward_acc + Reward_format

Reward_acc:    Correctness of final answer
  - Math: answer matches ground truth (in specified format)
  - Code: passes test cases via compiler
  
Reward_format: Structural compliance
  - Reasoning within <think>...</think>
  - Answer within <answer>...</answer>
```

**Why no neural reward models?**
1. Susceptible to reward hacking at scale
2. Require substantial compute to retrain
3. Complicate training pipeline

### 2.3 Emergent Behaviors

Sophisticated reasoning patterns emerge **without explicit teaching**:

**1. Increasing thinking time**:
- Response length grows steadily throughout training
- Model learns to allocate more tokens to harder problems
- Driven by intrinsic adaptation, not external modification

**2. Self-reflection ("aha moments")**:
```
"Wait, wait. Wait. That's an aha moment I can flag here.
Let's reevaluate this step-by-step to identify if the correct sum can be..."
```
Sudden increase in use of "wait" during reflections marks distinct reasoning
pattern change.

**3. Verification and backtracking**:
- Model checks intermediate results
- Explores alternative approaches within single response
- Abandons failing strategies mid-solution

**4. Dynamic strategy adaptation**:
- Tries simpler methods first
- Escalates to complex approaches when needed
- Learns problem-type specific heuristics

## 3. DeepSeek-R1 Training Pipeline

DeepSeek-R1-Zero has challenges: poor readability, language mixing (EN/CN),
limited non-reasoning performance. DeepSeek-R1 addresses these.

### 3.1 Multi-Stage Framework

```
DeepSeek-V3-Base
       ↓
[Cold Start: Long CoT SFT]  ← High-quality reasoning traces
       ↓
[RL: Rule-based + Language Consistency]  ← Reasoning prompts
       ↓
DeepSeek-R1-Dev-2
       ↓
[Rejection Sampling]  ← Generate diverse solutions
       ↓
[SFT: Reasoning + Non-Reasoning]  ← Combine with general data
       ↓
[RL: Rule-based + Preference Reward]  ← Diverse prompts
       ↓
DeepSeek-R1
```

### 3.2 Cold Start with Long CoT

Initial SFT on small set of high-quality long chain-of-thought examples:
- Establishes reasoning structure
- Sets response format expectations
- Provides starting point for RL exploration

### 3.3 Rejection Sampling

Generate multiple solutions, filter by correctness:
- Produces diverse successful reasoning traces
- High-quality SFT data from model's own generations
- Enables human preference alignment on non-reasoning tasks

## 4. Key Algorithms

### 4.1 Group Relative Policy Optimization

Full GRPO objective (Equation 1):

```
J_GRPO(θ) = E[q~P(Q), {o_i}~π_θ_old(O|q)]
            (1/G) Σ_i min(ratio_i × A_i, clip(ratio_i, 1-ε, 1+ε) × A_i)
            - β × D_KL(π_θ || π_ref)

where:
  ratio_i = π_θ(o_i|q) / π_θ_old(o_i|q)
  A_i = (r_i - mean(r)) / std(r)        # Group-relative advantage
  D_KL = π_ref/π_θ - log(π_ref/π_θ) - 1 # KL divergence
```

**Training hyperparameters**:
| Parameter | Value |
|-----------|-------|
| Learning rate | 3e-6 |
| KL coefficient β | 0.001 |
| Sampling temperature | 1.0 |
| Group size G | 16 |
| Max length (early) | 32,768 tokens |
| Max length (late) | 65,536 tokens |
| Total steps | 10,400 |
| Batch size | 512 (32 questions × 16 outputs) |

### 4.2 Rule-Based Rewards

```python
def compute_reward(response, ground_truth, task_type):
    """
    Pure rule-based reward — no neural models.
    """
    reward = 0.0
    
    # Format reward: correct structure
    if has_think_tags(response) and has_answer_tags(response):
        reward += 1.0
    
    # Accuracy reward: correct answer
    if task_type == "math":
        answer = extract_boxed_answer(response)
        if answer == ground_truth:
            reward += 1.0
    elif task_type == "code":
        passed = run_test_cases(response, ground_truth)
        reward += passed / total_tests
    elif task_type == "logic":
        answer = extract_answer(response)
        if answer == ground_truth:
            reward += 1.0
    
    return reward
```

### 4.3 Distillation to Smaller Models

Emergent reasoning patterns transferable to smaller models:

```python
def distill_reasoning(teacher_model, student_model, prompts):
    """
    Transfer reasoning capabilities via response distillation.
    """
    for prompt in prompts:
        # Generate teacher response with full reasoning
        teacher_response = teacher_model.generate(
            prompt,
            max_length=65536,
            temperature=0.7
        )
        
        # Train student to match teacher's reasoning trace
        student_loss = cross_entropy(
            student_model(prompt),
            teacher_response
        )
        
        student_model.backward(student_loss)
```

**Released distilled models**: Smaller models with strong reasoning capabilities
that surpass their original instruction-tuned counterparts.

## 5. Results

### 5.1 AIME 2024 (Mathematical Reasoning)

| Model | Pass@1 | Cons@16 |
|-------|--------|---------|
| DeepSeek-R1-Zero (start) | 15.6% | - |
| DeepSeek-R1-Zero (end) | 77.9% | 86.7% |
| Human participants (avg) | ~50% | - |

Training progression shows steady improvement from 15.6% → 77.9% over 10k steps.

### 5.2 Response Length Evolution

| Training Stage | Avg Response Length |
|----------------|---------------------|
| Step 0 | ~2,000 tokens |
| Step 5,000 | ~10,000 tokens |
| Step 10,000 | ~18,000 tokens |

Model learns to "think longer" on hard problems without explicit instruction.

### 5.3 Cross-Domain Performance

Strong results on:
- Coding competitions
- Graduate-level biology, physics, chemistry
- Logical reasoning benchmarks

## 6. Hydrogen Relevance

### 6.1 Implications for AI Agent Design

DeepSeek-R1 demonstrates that complex behaviors emerge from simple incentives:

**The insight**: Don't teach HOW to reason — provide correct incentives and let
reasoning emerge. This aligns with Hydrogen's philosophy of minimal, lawful
abstractions.

### 6.2 Bounded Reasoning Primitives

```purescript
-- Response structure as bounded type
type ReasoningResponse =
  { think :: NonEmptyString   -- Reasoning trace
  , answer :: Answer          -- Final answer
  }

-- Reward signal as bounded type
type Reward = BoundedFloat 0.0 2.0  -- acc + format

-- Group-relative advantage
type Advantage = Float  -- Normalized within group
```

### 6.3 Key Patterns

1. **Group-relative reward**: Compare within batch, not against global baseline
   — robust to varying problem difficulty

2. **Rule-based verification**: Deterministic rewards avoid neural model
   pitfalls — aligns with Hydrogen's bounded types philosophy

3. **Emergent thinking time**: Model allocates compute based on problem
   complexity — adaptive resource usage

4. **Self-correction emergence**: "Wait" patterns appear spontaneously —
   verification as emergent behavior, not trained feature

### 6.4 Training Configuration

| Parameter | Value |
|-----------|-------|
| Base model | DeepSeek-V3-Base |
| Algorithm | GRPO |
| Steps | 10,400 |
| Group size | 16 |
| Max tokens | 32k → 65k |
| Reference update | Every 400 steps |
| Inner epochs | 1 (single pass per mini-batch) |

---

*Synthesized for the Hydrogen project — RL for emergent reasoning as bounded behavior*
