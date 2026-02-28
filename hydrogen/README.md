# HYDROGEN

```
    ██╗  ██╗██╗   ██╗██████╗ ██████╗  ██████╗  ██████╗ ███████╗███╗   ██╗
    ██║  ██║╚██╗ ██╔╝██╔══██╗██╔══██╗██╔═══██╗██╔════╝ ██╔════╝████╗  ██║
    ███████║ ╚████╔╝ ██║  ██║██████╔╝██║   ██║██║  ███╗█████╗  ██╔██╗ ██║
    ██╔══██║  ╚██╔╝  ██║  ██║██╔══██╗██║   ██║██║   ██║██╔══╝  ██║╚██╗██║
    ██║  ██║   ██║   ██████╔╝██║  ██║╚██████╔╝╚██████╔╝███████╗██║ ╚████║
    ╚═╝  ╚═╝   ╚═╝   ╚═════╝ ╚═╝  ╚═╝ ╚═════╝  ╚═════╝ ╚══════╝╚═╝  ╚═══╝
```

**The purest web design language ever created.**

UI as data, not framework-specific code. Pure PureScript describing interfaces that render targets interpret to reality. Zero external framework dependencies. Formally verified with Lean4 proofs.

| | |
|---|---|
| **Build** | 0 errors, 0 warnings |
| **Schema** | 516 files across 17 pillars |
| **Proofs** | 80 Lean files, ~1100 theorems, **0 sorry** |

---

## Why Hydrogen?

Web frameworks optimize for developer ergonomics. Hydrogen optimizes for **correctness at scale**.

When AI agents compose UI — not one agent, but millions operating in parallel — the framework must guarantee:

- **Determinism**: Same input → same pixels. Always.
- **Bounded types**: No `undefined`, no `NaN`, no invalid states.
- **Algebraic composition**: UI primitives that compose lawfully.
- **Formal verification**: Properties proven in Lean4, not just tested.

Hydrogen is infrastructure for autonomous systems that need to reason about UI algebraically.

---

## Architecture

```
State × Msg → State × [Effect]
view :: State → Element Msg
```

Elements are pure PureScript data structures. Targets interpret them:

| Target | Description |
|--------|-------------|
| `Hydrogen.Target.DOM` | Browser DOM with diff/patch |
| `Hydrogen.Target.Static` | HTML strings for SSG |
| `Hydrogen.Target.Canvas` | 2D canvas rendering |
| `Hydrogen.Target.WebGL` | 3D/WebGPU rendering |

Same Element, multiple outputs. **Separate what from how.**

---

## Design System Ontology

17 pillars of bounded, type-safe design primitives:

| Pillar | Atoms |
|--------|-------|
| **Color** | sRGB, P3, LAB, OKLCH, camera log curves, LUTs, CDL |
| **Dimension** | SI units (yocto→quetta), device units, typography units |
| **Geometry** | Shapes, curves (Bezier, NURBS, B-spline), transforms |
| **Typography** | OpenType features, metrics, type scales, font stacks |
| **Material** | Gradients, noise (Perlin, Worley), blur, surfaces |
| **Elevation** | Shadows, z-index, depth of field, parallax |
| **Temporal** | Easing (30 functions), spring physics, keyframes |
| **Reactive** | States (loading, error, success), validation, focus |
| **Gestural** | Touch, pointer, multi-touch, drag/drop, vim keys |
| **Haptic** | Vibration patterns, iOS system feedback |
| **Audio** | Synthesis, effects, analysis, spatial audio |
| **Spatial** | 3D primitives, PBR materials, XR, scene graphs |
| **Accessibility** | WAI-ARIA 1.2 roles, states, live regions |
| **Sensation** | Proprioceptive, environmental, social awareness |
| **Scheduling** | Time-based primitives |
| **Epistemic** | Model-level phenomenology |
| **Brand** | Token composition, theme configuration |

Atoms compose into molecules. Molecules compose into compounds. Compounds compose into brands.

---

## Formal Verification

Hydrogen properties are proven in Lean4, not just tested:

```lean
-- Hue rotation is associative
theorem rotate_assoc (h : Hue) (a b : Float) :
  rotate (rotate h a) b = rotate h (a + b)

-- Color conversion roundtrips
theorem srgb_to_linear_to_srgb (c : SRGB) :
  linearToSRGB (srgbToLinear c) = c

-- Submodular optimization guarantees
theorem continuous_greedy_guarantee (F : Set V → ℝ) (k : ℕ) :
  F(solution) ≥ (1 - 1/e) * F(optimal)
```

**80 proof files. ~1100 theorems. 0 sorry.**

The type system encodes invariants. The proofs verify properties. Invalid states don't compile.

---

## Quick Start

```purescript
import Hydrogen.Render.Element as E
import Hydrogen.Data.RemoteData as RD
import Hydrogen.Query as Q

-- UI as pure data
button :: forall msg. msg -> String -> E.Element msg
button onClick label =
  E.button_
    [ E.onClick onClick
    , E.class_ "btn"
    ]
    [ E.text label ]

-- Data fetching with caching
client <- Q.newClient
state <- Q.query client
  { key: ["user", userId]
  , fetch: Api.getUser userId
  }

-- RemoteData is a lawful Monad
let dashboard = ado
      user <- userState.data
      posts <- postsState.data
      in { user, posts }
```

---

## Core Modules

| Module | Purpose |
|--------|---------|
| `Hydrogen.Render.Element` | Pure data UI elements |
| `Hydrogen.Schema.*` | 516 design system atoms |
| `Hydrogen.Query` | Data fetching, caching, deduplication |
| `Hydrogen.Data.RemoteData` | Lawful Monad for async state |
| `Hydrogen.Router` | Type-safe ADT routing |
| `Hydrogen.API.Client` | HTTP client with auth |
| `Hydrogen.SSG` | Static site generation |

---

## Development

```bash
# Enter dev environment (Nix)
nix develop

# Build PureScript
spago build

# Build Lean proofs
lake build

# Run tests
spago test
```

### Requirements

- Nix (with flakes enabled)
- Or manually: PureScript 0.15.15, Node 22, Lean 4.7.0

---

## Documentation

| Document | Description |
|----------|-------------|
| [Schema Reference](docs/SCHEMA.md) | Complete pillar enumeration |
| [Design Ontology](docs/design-ontology.md) | Type-safe primitives |
| [Component Architecture](docs/COMPOUND_ARCHITECTURE.md) | Schema-native components |
| [Query Guide](docs/query.md) | Caching, pagination |
| [Router Guide](docs/router.md) | Route ADTs, navigation |
| [Proofs Guide](docs/PROOFS.md) | Lean4 verification |
| [Roadmap](docs/roadmap.md) | Project status and estimates |

---

## Project Status

Hydrogen is in **alpha**. The Schema is complete. Runtime targets are in progress.

See [roadmap.md](docs/roadmap.md) for detailed status and completion estimates.

---

## License

MIT

---

<sub>Built for the Continuity Project. Infrastructure for AI autonomy done correctly.</sub>
