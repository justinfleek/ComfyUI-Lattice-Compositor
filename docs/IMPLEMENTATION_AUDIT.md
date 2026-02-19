# IMPLEMENTATION Folder Audit - What Standalone MUST Have

**Date:** February 2026
**Status:** Critical Gap Analysis

---

## Executive Summary

After auditing all 23 IMPLEMENTATION folders, standalone is **missing critical infrastructure** for production. The backend logic is complete, but we're missing:

1. **Armitage Build System** (DICE, CAS, Witness Proxy)
2. **Dhall Lint Rules** (17 rules for Nix compliance)
3. **PureScript UI Components** (Dialog, Tabs from Radix)
4. **GPU Inference Kernels** (s4 NVFP4, SageAttention)
5. **Tokenizer Bindings** (HuggingFace tokenizers)
6. **Verified Extraction Pipeline** (Lean4 → PureScript)

---

## CRITICAL MISSING: Armitage Build System

Location: `IMPLEMENTATION/aleph-baileylu-linter-round-2/src/armitage/`

| File | Lines | Purpose | Status |
|------|-------|---------|--------|
| DICE.hs | 848 | Dynamic Incremental Computation Engine | **MISSING** |
| CAS.hs | 283 | Content-Addressed Storage client | **MISSING** |
| Builder.hs | 590 | Daemon-free build executor | **MISSING** |
| Store.hs | 354 | Daemon-free Nix store ops | **MISSING** |
| Dhall.hs | 784 | Build target configuration | **MISSING** |
| Trace.hs | 564 | CMake/build system tracing | **MISSING** |
| Proxy.hs | 886 | Witness Proxy (TLS MITM) | **MISSING** |
| RE.hs | 432 | Remote Execution API client | **MISSING** |
| Main.hs | 632 | CLI entry point | **MISSING** |

**Why Critical:** DICE is the incremental build engine. Without it, no production builds.


---

## CRITICAL MISSING: Dhall Lint Rules

Location: `IMPLEMENTATION/aleph-baileylu-linter-round-2/linter/lints/nix/`

| Rule | Code | Level | What It Catches |
|------|------|-------|-----------------|
| with-lib.dhall | ALEPH-E001 | ERROR | `with lib;` statements |
| rec-in-derivation.dhall | ALEPH-E002 | ERROR | `rec` in mkDerivation |
| non-lisp-case.dhall | ALEPH-E003 | ERROR | camelCase in aleph.* |
| missing-class.dhall | ALEPH-E004 | ERROR | Modules without `_class` |
| default-nix-in-packages.dhall | ALEPH-E005 | ERROR | `default.nix` in packages/ |
| no-heredoc-in-inline-bash.dhall | ALEPH-E006 | ERROR | Heredocs in Nix strings |
| no-substitute-all.dhall | ALEPH-E007 | ERROR | substituteAll usage |
| no-raw-mkderivation.dhall | ALEPH-E010 | ERROR | Direct mkDerivation |
| no-raw-runcommand.dhall | ALEPH-E011 | ERROR | Direct runCommand |
| no-raw-writeshellapplication.dhall | ALEPH-E012 | ERROR | Direct writeShellApplication |
| no-translate-attrs-outside-prelude.dhall | ALEPH-E013 | ERROR | translate-attrs misuse |
| rec-anywhere.dhall | ALEPH-W001 | WARNING | All `rec` attrsets |
| long-inline-string.dhall | ALEPH-W003 | WARNING | Multi-line strings >10 lines |
| or-null-fallback.dhall | ALEPH-W004 | WARNING | `x or null` patterns |
| missing-description.dhall | ALEPH-W005 | WARNING | mkOption without description |
| prefer-write-shell-application.dhall | ALEPH-W006 | ERROR | writeShellScript (deprecated) |
| missing-meta.dhall | ALEPH-W007 | WARNING | Derivations without meta |

**Why Critical:** Without lint rules, Nix code will violate Aleph RFCs.


---

## CRITICAL MISSING: PureScript UI Components

Location: `IMPLEMENTATION/purescript-radix-main/src/Radix/Pure/`

| Component | Lines | Features |
|-----------|-------|----------|
| Dialog.purs | 407 | Modal dialog, focus trap, scroll lock, ARIA |
| Tabs.purs | 329 | Keyboard nav, roving tabindex, orientation |
| FocusTrap.purs | 195 | Tab loop management |
| AriaHider.purs | 31 | Screen reader isolation |
| Id.purs | 41 | Unique ID generation |

Location: `IMPLEMENTATION/straylight-web-main/purescript/src/Straylight/`

| Module | Purpose |
|--------|---------|
| UI.purs | Core primitives (flex, row, column, heading, text) |
| Router.purs | Client-side routing with pushState |
| Layout/Header.purs | Site header component |
| Layout/Footer.purs | Site footer component |
| Components/*.purs | NavBar, Callout, Tag, StatusBlock |

**Why Critical:** standalone has 0 UI components. Need these as foundation.


---

## CRITICAL MISSING: GPU Inference (s4)

Location: `IMPLEMENTATION/s4-main/`

| Kernel | File | Purpose |
|--------|------|---------|
| quantize_row_major_kernel | nvfp4.cu | Q/K tensor FP4 quantization |
| quantize_transpose_kernel | nvfp4.cu | V tensor FP4 quantization |
| score_correction | score_correction.cu | cuBLAS GEMM for attention |
| sage_attention_plugin | sage_attention_plugin.h | TensorRT plugin |

**Why Critical:** FP4 quantized inference for production GPU workloads.

---

## CRITICAL MISSING: Verified Extraction

Location: `IMPLEMENTATION/verified-purescript-main/`

| File | What It Proves |
|------|----------------|
| SystemFComplete.lean | STLC + substitution lemma (NO AXIOMS) |
| TypeClasses.lean | Functor, Monad laws (ALL PROVEN) |
| VerifiedPrelude.lean | flip, compose, identity (by rfl) |
| Extraction.lean | F-omega subset extraction |

Location: `IMPLEMENTATION/continuity/`

| File | Purpose |
|------|---------|
| dice.lean | DICE build engine formalization |
| store.lean | Git attestation store |
| identity.lean | Ed25519 cryptographic identity |
| coset.lean | Build equivalence / cache correctness |

**Why Critical:** Lean proofs verify the PureScript code is correct.


---

## ALL 23 IMPLEMENTATION FOLDERS - Status

| # | Folder | Purpose | Integrated? | Priority |
|---|--------|---------|-------------|----------|
| 1 | aleph-main | Core Aleph infrastructure | PARTIAL | CRITICAL |
| 2 | aleph-baileylu-linter-round-2 | Aleph + linter rules | PARTIAL | CRITICAL |
| 3 | continuity | Lean proofs (DICE, store) | NO | CRITICAL |
| 4 | haskemathesis | Property-based API testing | YES | - |
| 5 | haskemathesis-main | (duplicate) | YES | - |
| 6 | hs-io-uring-main | io_uring bindings | NO | LOW |
| 7 | isospin-microvm-main | GPU VM passthrough | NO | MEDIUM |
| 8 | isospin-vm-main | Firecracker VMM | NO | LOW |
| 9 | mdspan-cute-main | CUDA tensor layouts | NO | MEDIUM |
| 10 | MONADS | Monad patterns | NO | LOW |
| 11 | nix-compile-main | Nix compilation | NO | LOW |
| 12 | nvidia-sdk-main | CUDA 13.1 SDK | YES | - |
| 13 | purescript-radix-main | Halogen UI components | NO | CRITICAL |
| 14 | Qwen3-TTS-main | TTS model | NO | LOW |
| 15 | s4-main | GPU inference runtime | NO | HIGH |
| 16 | sensenet-main | ML infra + hasktorch | PARTIAL | HIGH |
| 17 | slide-main | LLM inference client | NO | MEDIUM |
| 18 | straylight-web-main | Web skeleton + patterns | NO | HIGH |
| 19 | tokenizers-cpp-main | HuggingFace tokenizers | NO | MEDIUM |
| 20 | trinity-engine-hs-dev | io_uring bindings | NO | LOW |
| 21 | trtllm-serve-main | TensorRT LLM serving | NO | LOW |
| 22 | verified-purescript-main | Verified extraction | NO | CRITICAL |
| 23 | _EXTRAS | Miscellaneous | N/A | - |


---

## ALREADY INTEGRATED (Good)

These are in standalone and working:

- [x] `nix/prelude/` - All 22 files synced with aleph
- [x] `nix/templates/` - All 7 templates synced
- [x] `src/haskell/Aleph/Script/Tools/` - 25 typed tool wrappers
- [x] `src/haskell/Aleph/Nix/` - Typed package DSL
- [x] `nvidia-sdk` integration via overlays
- [x] `haskemathesis` for property testing
- [x] `lattice-core/lean/` - 246 Lean4 proof files
- [x] `lattice-core/purescript/` - 341 service files
- [x] `lattice-core/haskell/` - 190 type files

---

## INTEGRATION PLAN

### Phase 1: Build Infrastructure (Week 1-2)
1. Copy Armitage modules to `standalone/src/armitage/`
2. Copy Dhall lint rules to `standalone/linter/`
3. Copy all RFCs to `standalone/docs/rfc/`
4. Wire up `armitage` CLI in flake.nix

### Phase 2: UI Foundation (Week 3-4)
1. Copy purescript-radix components
2. Copy straylight-web patterns
3. Set up Halogen app skeleton
4. Implement routing

### Phase 3: Verified Pipeline (Week 5-6)
1. Set up verified-purescript extraction
2. Bridge continuity/dice.lean to Armitage/DICE.hs
3. Generate verified prelude

### Phase 4: GPU Runtime (Week 7-8)
1. Integrate s4 CUDA kernels
2. Set up hasktorch from sensenet
3. Wire tokenizers-cpp FFI

### Phase 5: Full UI (Week 9-40)
1. Port all 167 Vue components to PureScript/Halogen
2. Match comfyui/ui functionality exactly

---

## Files to Copy

```
FROM                                    TO
----                                    --
IMPLEMENTATION/aleph-baileylu-linter-round-2/
  src/armitage/                         standalone/src/armitage/
  linter/                               standalone/linter/
  docs/rfc/                             standalone/docs/rfc/

IMPLEMENTATION/purescript-radix-main/
  src/Radix/Pure/                       standalone/ui/src/Radix/Pure/

IMPLEMENTATION/straylight-web-main/
  purescript/src/Straylight/            standalone/ui/src/Straylight/

IMPLEMENTATION/verified-purescript-main/
  *.lean                                standalone/verified/

IMPLEMENTATION/continuity/
  *.lean                                standalone/proofs/continuity/
  schemas/*.sql                         standalone/db/schemas/

IMPLEMENTATION/s4-main/
  s4/                                   standalone/gpu/s4/
```


---

## HASKTORCH Location

**Found in:** `IMPLEMENTATION/sensenet-main/src/examples/hasktorch/`

| File | Purpose |
|------|---------|
| Main.hs | Tensor operations demo |
| LinearRegression.hs | Gradient descent example |
| BUCK | Buck2 build config |

**Integration:** sensenet flake provides hasktorch overlay with nvidia-sdk CUDA.

---

## DICE Location

**Lean Spec:** `IMPLEMENTATION/continuity/dice.lean` (340 lines)
**Haskell Impl:** `IMPLEMENTATION/aleph-baileylu-linter-round-2/src/armitage/Armitage/DICE.hs` (848 lines)
**Database:** `IMPLEMENTATION/continuity/schemas/04_dice.sql`

Key theorems in dice.lean:
- `dice_correctness`: Same key = same execution result
- `cache_correctness`: Cache hit = correct output
- `hermeticity`: Namespace isolation guarantees

---

## Summary: What You Asked About

| Item | Location | Status |
|------|----------|--------|
| **Hasktorch** | sensenet-main/src/examples/hasktorch/ | Available, not wired |
| **DICE** | continuity/dice.lean + armitage/DICE.hs | NOT INTEGRATED |
| **Linter Rules** | aleph-baileylu-linter-round-2/linter/ | NOT INTEGRATED |
| **UI Components** | purescript-radix-main/ | NOT INTEGRATED |
| **All 23 folders** | See status table above | 3 integrated, 20 not |

**Bottom Line:** standalone has the types and proofs but is missing:
1. The build system (Armitage/DICE)
2. The lint enforcement
3. The entire UI layer
4. GPU inference kernels
5. Verified extraction pipeline
