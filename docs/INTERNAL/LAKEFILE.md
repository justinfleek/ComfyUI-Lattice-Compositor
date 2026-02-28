━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      // lakefile // configuration
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# LEAN 4 BUILD CONFIGURATION

Hydrogen's `lakefile.lean` configures the Lean 4 proof infrastructure.

## CURRENT STRUCTURE

```lean
import Lake
open Lake DSL

package hydrogen where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,         -- Pretty-print λ as fun a ↦ b
    ⟨`pp.proofs.withType, false⟩,    -- Hide proof types in output
    ⟨`autoImplicit, false⟩           -- Require explicit type arguments
  ]

@[default_target]
lean_lib Hydrogen where
  srcDir := "proofs"

lean_exe hue where
  root := `Hydrogen.Schema.Color.Hue

lean_exe conversions where
  root := `Hydrogen.Schema.Color.Conversions
```

## LEAN OPTIONS EXPLAINED

### `pp.unicode.fun = true`

Pretty-prints lambda abstractions with arrow notation:

```lean
-- With option enabled:
fun a ↦ a + 1

-- Without option:
λ a, a + 1
```

Both are equivalent, but `↦` is more readable in proof output.

### `pp.proofs.withType = false`

Hides type annotations in proof goals:

```lean
-- With option disabled (less clutter):
⊢ rotate h 0 = h

-- With option enabled (verbose):
⊢ (rotate h 0 : Hue) = (h : Hue)
```

Reduces noise when working with proofs interactively.

### `autoImplicit = false`

**CRITICAL FOR CORRECTNESS:**

```lean
-- With autoImplicit = true (DANGEROUS):
def identity x := x  -- Lean infers: {α : Type} → α → α

-- With autoImplicit = false (SAFE):
def identity x := x  -- ERROR: unknown identifier 'x'
def identity (x : α) := x  -- ERROR: unknown type 'α'
def identity {α : Type} (x : α) := x  -- CORRECT
```

Prevents silent bugs from implicit type variables. Forces explicit quantification.

## SOURCE DIRECTORY STRUCTURE

```
proofs/
├── Hydrogen.lean                    # Root module (imports all submodules)
└── Hydrogen/
    └── Schema/
        └── Color/
            ├── Hue.lean
            └── Conversions.lean
```

The `srcDir := "proofs"` setting tells Lake to look for source files in `proofs/`.

Module paths follow directory structure:
- `proofs/Hydrogen.lean` → `import Hydrogen`
- `proofs/Hydrogen/Schema/Color/Hue.lean` → `import Hydrogen.Schema.Color.Hue`

## LIBRARY VS EXECUTABLE TARGETS

### lean_lib (Library)

```lean
lean_lib Hydrogen where
  srcDir := "proofs"
```

Compiles proof modules to `.olean` files (Lean object files). Used by:
- `lake build` - Builds all modules
- Other Lean files importing these modules
- IDE support (LSP)

### lean_exe (Executable)

```lean
lean_exe hue where
  root := `Hydrogen.Schema.Color.Hue
```

Generates executable that can:
- Print proof status
- Generate PureScript code
- Export proof manifest (TSV)

Run with `lake exe hue`.

## INTEGRATION WITH NIX/ALEPH

### Current (Standalone)

Hydrogen uses a standalone `lakefile.lean` with `lean-toolchain` specifying
Lean 4.7.0. This works but doesn't integrate with Nix derivations.

### Future (CA Derivations)

Following aleph's pattern, Hydrogen proofs could be Nix packages:

```nix
# In flake.nix or overlay
hydrogen-proofs = pkgs.leanPackages.buildLeanPackage {
  name = "hydrogen-proofs";
  src = ./proofs;
  
  # Content-addressed - identical proofs reuse cached builds
  __contentAddressed = true;
  
  # Dependencies (if we add mathlib, etc.)
  deps = [ ];
};
```

Benefits:
- **CA derivations** - Proof builds are cached by content hash
- **Reproducible** - Same proof always builds the same `.olean`
- **Cacheable** - Binary cache for proof artifacts
- **Isolated** - Pure builds, no network access

### Typed Package DSL (Future)

Aleph's WASM-based package system could compile Hydrogen schemas:

```haskell
-- nix/packages/hydrogen-schema.hs
import Aleph.Nix.Syntax

hydrogenSchema :: Drv
hydrogenSchema = mkDerivation
    [ pname "hydrogen-schema-color"
    , version "0.1.0"
    , src $ github "straylight-software/hydrogen" "main"
    , buildInputs ["purescript", "spago"]
    , prover ["lean4"]  -- Run proofs before building PureScript
    , buildPhase
        [ run "lake" ["build"]  -- Build proofs first
        , run "spago" ["build"] -- Then build PureScript
        ]
    , installPhase
        [ install [lib "output"]
        , install [doc "proofs/.lake/build/lib"]
        ]
    ]
```

The `prover` field would:
1. Build Lean proofs
2. Verify no `sorry`
3. Generate proof manifest
4. Fail build if proofs incomplete

## ADDING NEW PROOF MODULES

### 1. Create the Lean file

```bash
touch proofs/Hydrogen/Schema/Color/NewModule.lean
```

### 2. Add module structure

```lean
-- proofs/Hydrogen/Schema/Color/NewModule.lean
namespace NewModule

-- Definitions
def myFunction (x : Nat) : Nat := x + 1

-- Theorems
theorem myFunction_correct (x : Nat) : myFunction x = x + 1 := rfl

end NewModule
```

### 3. Import in root module

```lean
-- proofs/Hydrogen.lean
import Hydrogen.Schema.Color.Hue
import Hydrogen.Schema.Color.Conversions
import Hydrogen.Schema.Color.NewModule  -- Add this
```

### 4. (Optional) Add executable

```lean
-- lakefile.lean
lean_exe newmodule where
  root := `Hydrogen.Schema.Color.NewModule
```

### 5. Build and verify

```bash
lake build Hydrogen.Schema.Color.NewModule
lake exe newmodule  # If you added an executable
```

## COMMON LAKE COMMANDS

```bash
# Build everything
lake build

# Build specific module
lake build Hydrogen.Schema.Color.Hue

# Clean build artifacts
lake clean

# Update dependencies (if we add any)
lake update

# Run executable
lake exe hue
lake exe conversions

# Get help
lake help
```

## LEAN TOOLCHAIN VERSION

The `lean-toolchain` file specifies:

```
leanprover/lean4:v4.7.0
```

This is managed by `elan` (Lean version manager). To update:

```bash
# List available versions
elan toolchain list

# Update to latest stable
echo "leanprover/lean4:stable" > lean-toolchain
lake build  # Will download new version

# Pin to specific version
echo "leanprover/lean4:v4.10.0" > lean-toolchain
```

**Convention:** Use stable releases for production, not nightly builds.

## DEPENDENCIES (FUTURE)

If we add dependencies like `mathlib4`, add to `lakefile.lean`:

```lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib Hydrogen where
  srcDir := "proofs"
```

Then run `lake update` to fetch.

**Current status:** Zero dependencies. All proofs use only Lean 4 core library.

## PROOF VERIFICATION IN CI

Future CI integration:

```yaml
# .github/workflows/proofs.yml
name: Verify Proofs

on: [push, pull_request]

jobs:
  lean4:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: leanprover/lean4-action@v1
        with:
          version: v4.7.0
      
      - name: Build proofs
        run: lake build
      
      - name: Check for sorry
        run: |
          if grep -r "sorry" proofs/; then
            echo "ERROR: Found sorry in proofs"
            exit 1
          fi
      
      - name: Generate manifests
        run: |
          lake exe hue > proofs/hue-manifest.tsv
          lake exe conversions > proofs/conversions-manifest.tsv
      
      - name: Upload artifacts
        uses: actions/upload-artifact@v3
        with:
          name: proof-manifests
          path: proofs/*-manifest.tsv
```

## TROUBLESHOOTING

### "unknown constant" errors

**Cause:** Missing import or typo in name.

**Fix:** Add `import` at top of file:

```lean
import Hydrogen.Schema.Color.OtherModule
```

### "declaration uses 'sorry'"

**Cause:** Incomplete proof.

**Fix:** Replace `sorry` with actual proof or convert to axiom:

```lean
-- Bad (causes warning):
theorem foo : x = y := by sorry

-- Good (explicit axiom):
axiom foo : x = y
```

### "failed to compile definition, mark as 'noncomputable'"

**Cause:** Definition depends on axiom without executable code.

**Fix:** Add `noncomputable`:

```lean
noncomputable def myFunction := ...
```

### Lake hangs / doesn't update

**Cause:** Stale build cache.

**Fix:**

```bash
lake clean
rm -rf .lake
lake build
```

## RESOURCES

- **Lake Manual**: https://github.com/leanprover/lake#readme
- **Lean 4 Setup**: https://lean-lang.org/lean4/doc/setup.html
- **elan (version manager)**: https://github.com/leanprover/elan

────────────────────────────────────────────────────────────────────────────────

Build configurations are proof infrastructure.

Configure correctly. Build correctly. Verify correctly.

                                                                  — b7r6 // 2026
