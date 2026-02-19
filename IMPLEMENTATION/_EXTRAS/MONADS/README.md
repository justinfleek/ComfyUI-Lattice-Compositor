# COMPASS — Full Architecture

## Module Map

```
src/Compass/
├── Core/
│   └── Types.hs                  ← Foundational types: CAS, lattice, graded monad
│
├── CAS/
│   └── Store.hs                  ← Three-tier CAS backend (HAMT + Postgres + DuckDB)
│                                    UUID5 content addressing, Bloom filter, epoch snapshots
│
├── Serialization/
│   └── Binary.hs                 ← Deterministic binary encoding for CAS values
│                                    Wire protocol, cache key derivation
│
├── Inference/
│   └── TieredRouter.hs           ← Five-tier inference routing (Tier 0-4)
│                                    Selective prefetch, streaming, agent cache
│
├── Models/
│   └── Backends.hs               ← Model server wiring
│                                    Tier 2: llama.cpp (local 1-3B quantized)
│                                    Tier 3: vLLM (medium 7-13B)
│                                    Tier 4: DeepSeek API + Weyl polyhedral optimization
│                                    Prompt construction, SSE streaming
│
└── Warming/
    └── Speculative.hs            ← Speculative CAS warming engine
                                     Session/anticipatory/cascade warming strategies
                                     Query prediction (frequency + Markov + role + time-of-day)
                                     Budget management, worker pool

lean/Compass/
├── lakefile.lean                 ← Build configuration (depends on Mathlib)
├── Lattice/
│   └── Basic.lean                ← Semilattice laws, VersionVec proofs,
│                                    ascending chain condition, CALM convergence,
│                                    CAS retry termination bound
│
├── Merkle/
│   └── Integrity.lean            ← Merkle DAG well-formedness, tamper detection,
│                                    provenance path verification, append-only consistency,
│                                    epoch snapshot isolation
│
├── Inference/
│   └── TierProofs.lean           ← Tier classification determinism + monotonicity,
│                                    MAESTRO state machine totality (no stuck states),
│                                    budget allocation soundness, warming idempotency
│
└── CAS/
    └── Correctness.lean          ← CAS dedup, write-order independence,
                                     widget consistency, Bloom filter soundness,
                                     FULL SYSTEM COMPOSITION THEOREM
```

## Proof Coverage

| Property | Lean4 File | Status | What It Guarantees |
|---|---|---|---|
| Semilattice laws (4 laws) | Lattice/Basic | ✅ Proved | CALM applicability |
| VersionVec join comm/assoc/idem | Lattice/Basic | ✅ Proved | Concurrent writes converge |
| VersionVec bot identity | Lattice/Basic | ✅ Proved | Initial state is valid |
| Bump monotonicity | Lattice/Basic | ✅ Proved | Version only increases |
| Join monotonicity (both args) | Lattice/Basic | ✅ Proved | Merges preserve ordering |
| Ascending chain termination | Lattice/Basic | ✅ Proved | CAS retry loop terminates |
| CALM convergence | Lattice/Basic | ✅ Proved | Permutation independence |
| Content addr determinism | Lattice/Basic | ✅ Proved | Same content → same UUID5 |
| Scraper deduplication | Lattice/Basic | ✅ Proved | Two scrapers, one address |
| Merkle integrity | Merkle/Integrity | ✅ Proved | Structural consistency |
| Leaf modification detection | Merkle/Integrity | ✅ Proved | Tamper detection |
| Epoch read determinism | Merkle/Integrity | ✅ Proved | Snapshot isolation |
| Epoch consistency | Merkle/Integrity | ✅ Proved | Repeatable reads |
| Tier determinism | Inference/TierProofs | ✅ Proved | Same input → same tier |
| Tier monotonicity | Inference/TierProofs | ✅ Proved | More data → same/lower tier |
| MAESTRO no stuck states | Inference/TierProofs | ✅ Proved | Agents always progress |
| Ready is terminal | Inference/TierProofs | ✅ Proved | Clean termination |
| Warming idempotency | Inference/TierProofs | ✅ Proved | No wasted computation |
| Warming invalidation | Inference/TierProofs | ✅ Proved | Data change → re-warm |
| Budget bounded | Inference/TierProofs | ✅ Proved | Never exceeds time budget |
| Widget determinism | CAS/Correctness | ✅ Proved | Reproducible queries |
| Write order independence | CAS/Correctness | ✅ Proved | CALM for CAS writes |
| No partial reads | CAS/Correctness | ✅ Proved | Snapshot atomicity |
| Bloom filter soundness | CAS/Correctness | ✅ Proved | No false negatives |
| **System composition** | CAS/Correctness | ✅ Proved | **All 4 properties hold** |

**ZERO SORRY. ZERO AXIOMS.**

## Build

```bash
cd lean && lake build
```
