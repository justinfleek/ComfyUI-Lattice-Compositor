/-
  Verified PureScript Extraction from Lean 4
  
  A framework for generating proof-carrying PureScript code.
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- PROJECT STRUCTURE
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  CORE FILES (all compile with no errors or sorries):
  
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │ VERIFIED COMPUTATION                                                        │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ SystemFComplete.lean  │ STLC with full verification, NO AXIOMS              │
  │                       │ - Substitution lemma proven                         │
  │                       │ - Semantic preservation proven                      │
  │                       │ - Multi-step preservation proven                    │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ SystemF.lean          │ STLC with axiomatized substitution                  │
  │                       │ - Simpler version for reference                     │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ SystemFPoly.lean      │ System F with type polymorphism                     │
  │                       │ - Type abstraction (Λ) and application              │
  │                       │ - Type erasure verified                             │
  │                       │ - Church encodings                                  │
  └─────────────────────────────────────────────────────────────────────────────┘
  
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │ TYPECLASS VERIFICATION                                                      │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ TypeClasses.lean      │ Verified typeclass instances                        │
  │                       │ - Eq, Semigroup, Monoid, Functor, Monad             │
  │                       │ - All laws proven (including List Monad assoc)      │
  │                       │ - Dictionary-passing code generation                │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ VerifiedPrelude.lean  │ Prelude combinators with proofs                     │
  │                       │ - identity, const, flip, compose, apply, on         │
  │                       │ - All algebraic laws proven by rfl                  │
  └─────────────────────────────────────────────────────────────────────────────┘
  
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │ PROOF-CARRYING CODE                                                         │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ ProofCarryingAST.lean │ AST with proof status annotations                   │
  │                       │ - ✓ PROVEN / ⚠ AXIOM / ✗ UNVERIFIED                 │
  │                       │ - Generates annotated PureScript                    │
  │                       │ - TSV manifest for tooling                          │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ PSParser.lean         │ PureScript parser                                   │
  │                       │ - Type signatures with :: and forall                │
  │                       │ - Constraint parsing (Semigroupoid a =>)            │
  │                       │ - Pattern wildcards (_)                             │
  │                       │ - Infix operators (<<<, >>>, $, #, `backticks`)     │
  │                       │ - JSON and TSV manifest output                      │
  └─────────────────────────────────────────────────────────────────────────────┘
  
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │ CODE GENERATION                                                             │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ PureScript.lean       │ Full PureScript Prelude AST                         │
  │                       │ - 29 modules                                        │
  │                       │ - Pretty printer                                    │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ PureScriptAST.lean    │ Core AST types                                      │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ ProofCarrying.lean    │ Semantic models (Lean = spec)                       │
  ├─────────────────────────────────────────────────────────────────────────────┤
  │ Generator.lean        │ Simple code generator                               │
  │ Extraction.lean       │ Code extraction utilities                           │
  │ TranspilerFinal.lean  │ Final transpiler design                             │
  └─────────────────────────────────────────────────────────────────────────────┘
  
  experimental/           │ Work in progress, has errors                        │
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUICK START
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  # Verify all files compile:
  for f in *.lean; do lean "$f"; done
  
  # Run the parser:
  lean PSParser.lean
  
  # See verified prelude:
  lean VerifiedPrelude.lean
  
  # See full verification (no axioms):
  lean SystemFComplete.lean
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- KEY THEOREMS
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  FROM SystemFComplete.lean (ALL PROVEN, NO AXIOMS):
  
  theorem semantic_preservation :
    Step t t' → denote t () = denote t' ()
    
  theorem substClosed_correct :
    denote (substClosed body arg) () = denote body (denote arg (), ())
  
  FROM VerifiedPrelude.lean (BY rfl):
  
  theorem flip_flip : flip (flip f) = f
  theorem compose_assoc : compose f (compose g h) = compose (compose f g) h
  theorem identity_left : compose identity f = f
  theorem identity_right : compose f identity = f
  
  FROM TypeClasses.lean (ALL LAWS PROVEN):
  
  monadList.assoc : bind (bind ma f) g = bind ma (fun x => bind (f x) g)
  optionMonad.left_id : bind (pure a) f = f a
  optionMonad.right_id : bind ma pure = ma
-/

-- ═══════════════════════════════════════════════════════════════════════════════
-- ARCHITECTURE
-- ═══════════════════════════════════════════════════════════════════════════════

/-
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │                              LEAN 4                                         │
  │                                                                             │
  │   ┌───────────────┐     ┌───────────────┐     ┌───────────────┐            │
  │   │ Semantic      │     │ Intrinsically │     │ Proofs        │            │
  │   │ Models        │────▶│ Typed Terms   │────▶│ (rfl/tactic)  │            │
  │   └───────────────┘     └───────────────┘     └───────────────┘            │
  │          │                     │                     │                      │
  │          │                     │                     │                      │
  │          ▼                     ▼                     ▼                      │
  │   ┌─────────────────────────────────────────────────────────────┐          │
  │   │                     CODE GENERATION                         │          │
  │   │                                                             │          │
  │   │  codegen : Term → String                                    │          │
  │   │  pretty : PSModule → String                                 │          │
  │   └─────────────────────────────────────────────────────────────┘          │
  │                              │                                              │
  └──────────────────────────────┼──────────────────────────────────────────────┘
                                 │
                                 ▼
  ┌─────────────────────────────────────────────────────────────────────────────┐
  │                         PURESCRIPT OUTPUT                                   │
  │                                                                             │
  │   -- flip_flip: flip (flip f) = f                                          │
  │   -- Status: ✓ PROVEN (PS.flip_flip)                                        │
  │   flip f b a = f a b                                                        │
  │                                                                             │
  │   -- PROOF SUMMARY: 12 properties proven, 0 functions unverified            │
  └─────────────────────────────────────────────────────────────────────────────┘
-/

#check "Verified PureScript Extraction - All core files compile cleanly"
