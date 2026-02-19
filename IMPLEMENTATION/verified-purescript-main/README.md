# // verified purescript //

Proof-carrying PureScript extracted from Lean 4. Machine-checked algebraic properties.

## the problem

PureScript has no proof system. You write `flip (flip f) = f` and hope it's true. Tests help but don't prove. Property-based testing gets closer but still samples.

## the solution

Write semantics in Lean 4. Prove properties. Extract PureScript with proof annotations.

```
Lean 4                              PureScript
──────                              ──────────
def flip f b a := f a b      →      flip f b a = f a b
theorem flip_flip :                 -- ✓ PROVEN (flip_flip)
  flip (flip f) = f := rfl
```

The generated code carries its proof status. Tooling can verify coverage.

## usage

```bash
# via nix (recommended)
nix run ..#verified-prelude           # prelude combinators + algebraic laws
nix run ..#system-f                   # STLC with full verification, no axioms
nix run ..#typeclasses                # monad laws for List
nix run ..#ps-parser                  # parse + annotate purescript

# or directly
lean --run VerifiedPrelude.lean
lean --run SystemFComplete.lean
```

## files

### verified core (no axioms, no sorries)

| File | Lines | Description |
|------|------:|-------------|
| `SystemFComplete.lean` | 379 | STLC with substitution lemma + semantic preservation |
| `SystemFPoly.lean` | 269 | System F with type polymorphism, verified erasure |
| `TypeClasses.lean` | 347 | Eq, Semigroup, Monoid, Functor, Monad — all laws proven |
| `VerifiedPrelude.lean` | 231 | identity, const, flip, compose, apply, on — by rfl |

### code generation

| File | Lines | Description |
|------|------:|-------------|
| `PSParser.lean` | 702 | PureScript parser with proof annotations |
| `ProofCarryingAST.lean` | 364 | AST nodes tagged ✓ PROVEN / ⚠ AXIOM / ✗ UNVERIFIED |
| `PureScript.lean` | 1017 | Full Prelude AST (29 modules) |
| `PureScriptAST.lean` | 167 | Core AST types |

### support

| File | Lines | Description |
|------|------:|-------------|
| `SystemF.lean` | 298 | STLC reference (axiomatized substitution) |
| `ProofCarrying.lean` | 226 | Semantic models |
| `Extraction.lean` | 231 | Code extraction utilities |
| `Generator.lean` | 92 | Simple codegen |
| `TranspilerFinal.lean` | 103 | Final transpiler design |
| `Summary.lean` | 160 | Project overview |

```
Total: 4,586 lines of Lean 4
```

## key theorems

### SystemFComplete.lean — NO AXIOMS

```lean
-- Substitution preserves semantics
theorem substClosed_correct :
  denote (substClosed body arg) () = denote body (denote arg (), ())

-- Reduction preserves semantics  
theorem semantic_preservation :
  Step t t' → denote t () = denote t' ()

-- Multi-step preservation
theorem multi_step_preservation :
  MultiStep t t' → denote t () = denote t' ()
```

### VerifiedPrelude.lean — BY rfl

```lean
theorem flip_flip       : flip (flip f) = f                              := rfl
theorem compose_assoc   : (f ∘ g) ∘ h = f ∘ (g ∘ h)                      := rfl
theorem identity_left   : identity ∘ f = f                               := rfl
theorem identity_right  : f ∘ identity = f                               := rfl
theorem const_compose   : const x ∘ f = const x                          := rfl
theorem apply_identity  : apply identity x = x                           := rfl
```

### TypeClasses.lean — ALL LAWS

```lean
-- Monad laws for List (the hard one)
theorem monadList.left_id  : bind (pure a) f = f a
theorem monadList.right_id : bind ma pure = ma  
theorem monadList.assoc    : bind (bind ma f) g = bind ma (λx => bind (f x) g)

-- Functor composition
theorem functorList.compose : map (f ∘ g) = map f ∘ map g
```

## output formats

### annotated purescript

```purescript
module Data.Function where

-- flip_flip: flip (flip f) = f
-- Status: ✓ PROVEN (PS.flip_flip)
flip f b a = f a b

-- compose_assoc: (f <<< g) <<< h = f <<< (g <<< h)
-- Status: ✓ PROVEN (PS.compose_assoc)
compose f g x = f (g x)
```

### tsv manifest

```
module          function   property         status  theorem
Data.Function   flip       flip_flip        proven  PS.flip_flip
Data.Function   compose    compose_assoc    proven  PS.compose_assoc
Data.Function   compose    identity_left    proven  PS.identity_left
Data.Function   compose    identity_right   proven  PS.identity_right
```

### json

```json
{
  "module": "Data.Function",
  "functions": [
    { "name": "flip", "properties": [
      { "name": "flip_flip", "status": "proven", "theorem": "PS.flip_flip" }
    ]}
  ]
}
```

## architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                            LEAN 4                                   │
│                                                                     │
│  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐             │
│  │  Semantic   │    │ Intrinsic   │    │   Proofs    │             │
│  │   Models    │───▶│   Types     │───▶│  (rfl/tac)  │             │
│  └─────────────┘    └─────────────┘    └─────────────┘             │
│         │                  │                  │                     │
│         └────────┬─────────┴─────────┬───────┘                     │
│                  ▼                   ▼                              │
│         ┌─────────────┐     ┌─────────────┐                        │
│         │   Codegen   │     │  Manifest   │                        │
│         └─────────────┘     └─────────────┘                        │
└─────────────────┬───────────────────┬───────────────────────────────┘
                  ▼                   ▼
┌─────────────────────────────────────────────────────────────────────┐
│                       PURESCRIPT OUTPUT                             │
│                                                                     │
│  -- Status: ✓ PROVEN (PS.flip_flip)                                │
│  flip f b a = f a b                                                │
│                                                                     │
│  -- PROOF COVERAGE: 12/12 functions verified                       │
└─────────────────────────────────────────────────────────────────────┘
```

## experimental/

Work in progress. Has errors/sorries. Not verified.

## license

MIT

---

*// straylight //*
