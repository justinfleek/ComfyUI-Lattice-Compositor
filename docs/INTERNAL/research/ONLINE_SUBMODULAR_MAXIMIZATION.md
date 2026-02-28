━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                    // online // submodular // maximization
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Improved Algorithms for Online Submodular Maximization via First-order Regret Bounds

## Citation

```bibtex
@inproceedings{harvey2020improved,
  title={Improved Algorithms for Online Submodular Maximization via First-order Regret Bounds},
  author={Harvey, Nicholas J. A. and Liaw, Christopher and Soma, Tasuku},
  booktitle={Advances in Neural Information Processing Systems (NeurIPS)},
  volume={33},
  year={2020},
  address={Vancouver, Canada}
}
```

## Authors

- **Nicholas J. A. Harvey** — University of British Columbia (nickhar@cs.ubc.ca)
- **Christopher Liaw** — University of Toronto (cvliaw@cs.toronto.edu)
- **Tasuku Soma** — The University of Tokyo (tasuku_soma@mist.i.u-tokyo.ac.jp)

## Publication

34th Conference on Neural Information Processing Systems (NeurIPS 2020), Vancouver, Canada.

────────────────────────────────────────────────────────────────────────────────
                                                                    // abstract
────────────────────────────────────────────────────────────────────────────────

The paper addresses nonnegative submodular maximization in the online setting:

- At time step t, an algorithm selects a set S_t ∈ C ⊆ 2^V where C is a feasible
  family of sets
- An adversary then reveals a submodular function f_t
- Goal: design an efficient algorithm for minimizing expected approximate regret

The key innovation is exploiting "first-order" regret bounds for online linear
optimization to improve regret bounds in online submodular maximization.

────────────────────────────────────────────────────────────────────────────────
                                                              // key results
────────────────────────────────────────────────────────────────────────────────

## Monotone Submodular Maximization (Matroid Constraint)

**Result**: (1 − c/e − ε)-regret of O(√(kT ln(n/k)))

Where:
- n = size of ground set
- k = rank of the matroid
- ε > 0 is a constant
- c = average curvature

This improves on previous results of Streeter et al. (2009) and Golovin et al. (2014).

## Nonmonotone Unconstrained Submodular Functions

**Result**: 1/2-regret of O(√(nT))

This improves on Roughgarden and Wang (2018) by a factor of √n.

## Summary Table

| Setting                          | Known Results              | New Results              |
|----------------------------------|----------------------------|--------------------------|
| monotone+matroid (α=1−1/e−ε)     | O(k√(nT)) [Golovin 2014]   | O(√(kT ln(n/k)))        |
| monotone+matroid+bounded curv.   | —                          | O(√(kT ln(n/k)))        |
| nonmonotone (α=1/2)              | O(n√T) [R&W 2018]          | O(√(nT))                |
| monotone+cardinality (α=1−1/e)   | O(√(kT ln n)) [S&G 2009]   | O(√(kT ln(n/k)))        |

────────────────────────────────────────────────────────────────────────────────
                                                         // technical overview
────────────────────────────────────────────────────────────────────────────────

## Core Innovation: First-Order Regret Bounds

The common ingredient is exploiting "first-order" regret bounds for online linear
optimization (OLO), which bound regret in terms of the total gain or loss of the
best single action rather than the time horizon T.

This data-dependent nature enables exploiting structures of OLO subproblems
appearing in online submodular maximization.

## Monotone Case: Online Continuous Greedy

- Based on online continuous greedy [Golovin et al. 2014]
- Reduces problem to series of OLO problems on a matroid polytope
- Previous work used follow-the-perturbed-leader (FPL) → O(k√(nT))
- Key observation: OLO subproblems are structured — sum of rewards cannot be too large
- Using OLO algorithms with first-order regret bounds yields O(√(kT ln(n/k)))

## Nonmonotone Case: Online Double Greedy

- Similar to online double greedy of Roughgarden and Wang (2018)
- Reduces to auxiliary online learning problems (USM balance subproblems)
- Novel algorithm for USM balance with "first-order" regret bound
- Exploits Blackwell approachability theorem and online dual averaging
- Yields improved O(√(nT)) bound

────────────────────────────────────────────────────────────────────────────────
                                                    // mathematical background
────────────────────────────────────────────────────────────────────────────────

## Submodular Functions

A set function f : 2^V → ℝ is **submodular** if it satisfies the diminishing
returns property:

```
f(X ∪ {i}) − f(X) ≥ f(Y ∪ {i}) − f(Y)  for X ⊆ Y and i ∈ V \ Y
```

## Curvature

The curvature c of a nonnegative monotone submodular function f:

```
c = 1 − min_{i∈V} f(V\{i}) / f({i})
```

- c ∈ [0, 1] for all monotone submodular functions
- c = 0 for linear functions
- Lower curvature → better approximation guarantees

## Multilinear Extension

For a set function f : 2^V → ℝ, its multilinear extension F : [0,1]^V → ℝ:

```
F(x) = E[f(R(x))] = Σ_{S⊆V} f(S) ∏_{i∈S} x_i ∏_{i∉S} (1 − x_i)
```

Where R(x) is a random set containing each element i with probability x_i.

## α-Regret

```
Reg_α(T) := α max_{S*} Σ_{t=1}^T f_t(S*) − Σ_{t=1}^T f_t(S_t)
```

Where α ∈ (0,1] corresponds to the offline approximation ratio.

────────────────────────────────────────────────────────────────────────────────
                                                   // blackwell approachability
────────────────────────────────────────────────────────────────────────────────

## Definition

A Blackwell instance is a tuple (X, Y, u, S) where:
- X ⊆ ℝ^n, Y ⊆ ℝ^m, S ⊆ ℝ^d are closed convex sets
- u : X × Y → ℝ^d is a biaffine function

## Blackwell Approachability Theorem

A Blackwell instance B is **approachable** if and only if it is:
- response-satisfiable
- halfspace-satisfiable

## Application to USM Balance

The USM-balance subproblem can be cast as a Blackwell instance:
- X = {p = (p⁺, p⁻) ∈ [0,1]² : p⁺ + p⁻ = 1}
- Y = {Δ = (Δ⁺, Δ⁻) ∈ [−1,1]² : Δ⁺ + Δ⁻ ≥ 0}
- S = ℝ²_{≤0}

────────────────────────────────────────────────────────────────────────────────
                                               // relevance to hydrogen / nvfp4
────────────────────────────────────────────────────────────────────────────────

## Why This Matters for Tensor Rendering

Online submodular maximization is directly applicable to:

1. **Resource Allocation**: Allocating GPU compute budget across viewport regions
2. **Feature Selection**: Selecting which latent features to compute per frame
3. **Attention Mechanisms**: Online selection of attention heads in transformer models
4. **Cache Eviction**: Submodular coverage for latent cache management

## NVFP4 Backend Considerations

With NVFP4 (4-bit floating point with FP8 block scales) on Blackwell:

1. **Quantized Gradients**: First-order regret bounds are more robust to
   quantization noise than second-order bounds

2. **Block-Scaled Operations**: The matroid polytope constraints map naturally
   to block-scaled tensor operations (16 elements per block)

3. **Memory Efficiency**: O(√(kT ln(n/k))) regret enables aggressive memory
   reduction while maintaining approximation guarantees

4. **Streaming Computation**: Online algorithms don't require knowing T in advance,
   enabling true streaming tensor computation

## Implementation Considerations

For implementing in Hydrogen's tensor rendering pipeline:

```purescript
-- Submodular function for viewport region selection
type RegionValue = ViewportTensor -> Number

-- Online algorithm state
type OnlineState =
  { cumulativeGradient :: Tensor
  , dualVariable :: Tensor
  , iteration :: Int
  }

-- First-order regret bound: O(√(kT ln(n/k)))
-- k = number of selected regions
-- n = total regions
-- T = frames rendered
```

────────────────────────────────────────────────────────────────────────────────
                                                                 // references
────────────────────────────────────────────────────────────────────────────────

## Primary References

1. Harvey, N.J.A., Liaw, C., Soma, T. (2020). Improved Algorithms for Online
   Submodular Maximization via First-order Regret Bounds. NeurIPS 2020.

2. Streeter, M., Golovin, D. (2008). An Online Algorithm for Maximizing
   Submodular Functions. NIPS 2008.

3. Golovin, D., Krause, A., Streeter, M. (2014). Online Submodular Maximization
   under a Matroid Constraint with Application to Learning Assignments. arXiv.

4. Roughgarden, T., Wang, J.R. (2018). An Optimal Learning Algorithm for Online
   Unconstrained Submodular Maximization. COLT 2018.

5. Blackwell, D. (1956). An Analog of the Minimax Theorem for Vector Payoffs.
   Pacific Journal of Mathematics, 6(1):1–8.

6. Abernethy, J., Bartlett, P.L., Hazan, E. (2011). Blackwell Approachability
   and No-Regret Learning are Equivalent. COLT 2011.

## Additional References

7. Feldman, M. (2019). Guess Free Maximization of Submodular and Linear Sums.
   WADS 2019.

8. Buchbinder, N., Feldman, M., Seffi, J., Schwartz, R. (2015). A Tight Linear
   Time (1/2)-Approximation for Unconstrained Submodular Maximization.
   SIAM Journal on Computing.

9. Calinescu, G., Chekuri, C., Pál, M., Vondrák, J. (2011). Maximizing a
   Monotone Submodular Function Subject to a Matroid Constraint.
   SIAM Journal on Computing.

10. Sviridenko, M., Vondrák, J., Ward, J. (2015). Optimal Approximation for
    Submodular and Supermodular Optimization with Bounded Curvature. SODA 2015.

────────────────────────────────────────────────────────────────────────────────

## Acknowledgments (from original paper)

The authors thank the anonymous referees for their useful comments.

**Funding**:
- N.H. was supported by Canada Research Chairs Program and an NSERC Discovery Grant
- C.L. was supported by an NSERC graduate scholarship
- T.S. was supported by the Operations Research Society of Japan and JST, ERATO,
  Grant Number JPMJER1903, Japan

────────────────────────────────────────────────────────────────────────────────

                                                        — documented 2026-02-25

