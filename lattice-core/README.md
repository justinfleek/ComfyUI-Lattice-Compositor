# typed-comfy

**Bulletproof types for ComfyUI**

Everything flows from Lean proofs. No external schema. Just theorems.

## Architecture

```
lean/TensorCore/Extract.lean     ← THE SOURCE OF TRUTH
         │
         │  Extractable typeclass
         │  + roundtrip PROOFS
         │
         ├──▶ extracted/elm/TensorCore/Types.elm
         │      (type aliases, decoders, encoders)
         │
         ├──▶ extracted/python/types.py
         │      (frozen dataclasses, __post_init__ validation)
         │
         └──▶ extracted/c/tensor_core_types.h
                (structs, inline validators)
```

No Dhall. No JSON Schema. No codegen scripts. **Just proofs.**

## The Key Idea

Every extractable type has a **theorem**:

```lean
instance : Extractable Point3 where
  encode p := .obj [("x", .num p.x), ("y", .num p.y), ("z", .num p.z)]
  decode j := do
    let x ← j.lookup "x" >>= Json.asFloat
    let y ← j.lookup "y" >>= Json.asFloat
    let z ← j.lookup "z" >>= Json.asFloat
    pure ⟨x, y, z⟩
  proof p := by simp [Json.lookup, Json.asFloat]; rfl  -- ← THE LOCK
```

That `rfl` at the end means "reflexivity" - the terms are **definitionally equal**. 
The proof guarantees that `decode (encode x) = x` for all `x`.

The extracted Elm/Python/C does the same encoding. Therefore it's correct **by construction**.

## Building

```bash
nix develop

# Extract everything from proofs
make extract

# Build all targets
make all

# Run the scene editor
make serve
# Open http://localhost:8000

# Verify all proofs
make check

# See the type flow
make deps
```

## What Gets Extracted

### Elm (with proven codecs)
```elm
type alias Point3 =
    { x : Float, y : Float, z : Float }

decodePoint3 : Decoder Point3
decodePoint3 =
    D.succeed Point3
        |> required "x" D.float
        |> required "y" D.float
        |> required "z" D.float
```

### Python (with runtime validation)
```python
@dataclass(frozen=True)
class ColorRGB:
    r: float
    g: float
    b: float
    
    def __post_init__(self):
        assert 0 <= self.r <= 1, f"r must be in [0,1]"
        # ...
```

### C (with inline validators)
```c
typedef struct {
    float r;  /* must be in [0,1] */
    float g;
    float b;
} ColorRGB;

static inline bool ColorRGB_valid(ColorRGB c) {
    return c.r >= 0 && c.r <= 1 && ...;
}
```

## Why This Works

The droids can't cheat because:

1. **Types require proofs** - No `Extractable` instance without a `proof` field
2. **Proofs must typecheck** - Lean's kernel verifies, not vibes
3. **`rfl` demands equality** - Terms must compute to the same thing
4. **Extraction mirrors the proof** - The Elm/Python/C does exactly what was proven

Change a type → proof breaks → extraction fails → types stay in sync.

## Files

```
lean/
├── TensorCore/
│   ├── Basic.lean      # DType, Shape
│   ├── Tensor.lean     # Dependent tensor types
│   ├── Ops.lean        # Type-safe operations  
│   ├── Geometry.lean   # 3D primitives
│   └── Extract.lean    # THE PROOFS + emission
├── ExtractMain.lean    # CLI: lake exe extract
└── lakefile.lean

elm/
└── src/
    ├── Main.elm        # Scene editor
    └── Scene/
        ├── Types.elm   # (or use extracted)
        └── Renderer.elm

python/
└── tensor_core_py.cpp  # nanobind
```

## The Bottom Line

This is not code generation. This is **extraction from proofs**.

The Elm types are theorems. The Python types are theorems. The C types are theorems.

The only way to break them is to break Lean's kernel - ~2000 lines of auditable code.

Everything else is derived. Bulletproof.

## Why This Exists

When using LLMs for "vibe coding", they optimize for:
- "Code that compiles"
- "Code that looks right"


## License

MIT
