# Deciding not to Decide: Sound and Complete Effect Inference in the Presence of Higher-Rank Polymorphism

**arXiv:** 2510.20532  
**Authors:** Patrycja Balik, Szymon Jędras, Piotr Polesiuk (University of Wrocław)  
**Date:** October 23, 2025  
**Domain:** Programming Languages / Type Systems / Effect Inference

---

## Abstract

Presents a **sound and complete effect inference algorithm** for type-and-effect systems with:
- Subtyping
- Expressive higher-rank polymorphism
- Set-like semantics of effects

**Key Innovation:** Transforms effect constraints into propositional logic formulae to handle scoping issues of higher-rank polymorphism.

---

## 1. Problem: Effect Inference Challenges

### 1.1 Type-and-Effect Systems

Track both:
- **Data** (types)
- **Computational effects** (IO, state, exceptions, etc.)

### 1.2 Challenges

| Issue | Description |
|-------|-------------|
| **Expressiveness** | Need higher-rank polymorphism for effect scoping |
| **Intuitiveness** | Set-like semantics preferred by programmers |
| **Decidability** | Effect rows stop being unitary with rank-N |
| **Scoping** | Effect variables don't compose nicely |

---

## 2. Methodology

### 2.1 Key Insight

**Delay solving effect constraints** by transforming them into formulae of propositional logic.

### 2.2 Higher-Rank Polymorphism

Example: File handle with restricted scope
```haskell
-- Naive (too permissive):
∀β. Filepath → (File → IO·β Unit) → IO·β Unit

-- Rank-2 polymorphism (restricted):
∀β. Filepath → (∀α. File α →α·β Unit) → IO·β Unit
```

The second version ensures the file handle can't escape its scope.

### 2.3 Effect Rows vs Set-Like Effects

| Approach | Pros | Cons |
|----------|------|------|
| **Effect Rows** | Decidable unification | Can't handle two row variables |
| **Set-Like Effects** | More expressive | Requires boolean unification |

**This paper:** Combines set-like expressiveness with delayed constraint solving.

---

## 3. Algorithm

### 3.1 Two-Stage Approach

1. **Type reconstruction** (standard Hindley-Milner)
2. **Effect constraint solving** (propositional logic)

### 3.2 Constraint Transformation

```
Effect constraints → Propositional formulae → Solve → Substitute
```

### 3.3 Formalization

All results formalized in **Coq** proof assistant.

---

## 4. Results

- **Soundness:** Every inferred effect is valid
- **Completeness:** Every valid effect is inferred
- **Minimal annotations** required from programmer

---

## 5. Relation to Hydrogen

### 5.1 Graded Monads

This work directly informs Hydrogen's effect/co-effect tracking:

| Hydrogen Need | This Paper's Solution |
|--------------|----------------------|
| **Effect tracking** | Type-and-effect system |
| **Higher-rank grades** | Rank-N polymorphism support |
| **Composable effects** | Set-like semantics with union/intersection |
| **Inference** | Sound + complete algorithm |

### 5.2 Schema Relevance

For **billion-agent swarms**, effect tracking ensures:
- Agents can reason about what operations are allowed
- Compositional guarantees about side effects
- Formal verification of effect boundaries

---

## 6. References

1. Hindley-Minler type inference
2. Effect rows (FX)
3. Flix programming language (set-like effects)
4. GRPO / PPO for RL
5. Algebraic effect handlers
6. Coq proof assistant

---

## 7. Citation

```bibtex
@misc{balik2025deciding,
  title={Deciding not to Decide: Sound and Complete Effect Inference in the Presence of Higher-Rank Polymorphism},
  author={Patrycja Balik and Szymon Jędras and Piotr Polesiuk},
  year={2025},
  eprint={2510.20532},
  archivePrefix={arXiv},
  primaryClass={cs.PL}
}
```

---
*Research Document: Hydrogen Research Collection*
*Completed: 2026-02-26*
*Attestation: clarity*
