# Playground Architecture

The specification for Hydrogen's component playground — the ultimate drag-and-drop
environment for composing atoms into compounds.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## Two Interfaces, One Schema

**For AI:**

The schema IS the interface. An AI reads and writes:

```purescript
ButtonSpec
  { geometry: { bounds: Rect 0 0 200 50, shape: Squircle 0.7 }
  , material: { fill: FillDiffusion { seed: 42, guidance: 7.5, ... } }
  , haptic: { onPress: ImpactFeedback Heavy }
  , ...
  }
```

The "show flag" enables a debug viewport while primary display stays stable —
like having two monitors, one for production, one for dev tools. An AI can
debug its own rendering code without disrupting its user-facing output.

**For Humans:**

We need something they can *touch*:

- See all the atoms
- Drag them together
- Watch the button respond in real-time
- Feel the haptic preview through their phone
- Export to BrandSchema

────────────────────────────────────────────────────────────────────────────────
                                                              // self-hosting
────────────────────────────────────────────────────────────────────────────────

## The Playground is Self-Hosting

The playground is composed from the same atoms it edits. Fractal.

- The button picker IS buttons
- The color picker IS the color atoms
- The timeline IS temporal atoms
- The property inspector IS typography atoms

This isn't philosophy — it's practical. If the atoms can't build the playground,
they can't build anything. The playground is the first and most demanding test.

────────────────────────────────────────────────────────────────────────────────
                                                                // ui layout
────────────────────────────────────────────────────────────────────────────────

## Interface Layout

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  HYDROGEN PLAYGROUND                                      [AI] [Human]      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────┐  ┌───────────────────────────────────────────────────┐    │
│  │ ATOMS       │  │                                                   │    │
│  │             │  │                LIVE PREVIEW                       │    │
│  │ ▸ Geometry  │  │                                                   │    │
│  │ ▸ Material  │  │           ┌─────────────────────┐                 │    │
│  │ ▸ Color     │  │           │                     │                 │    │
│  │ ▸ Elevation │  │           │    YOUR BUTTON      │                 │    │
│  │ ▸ Temporal  │  │           │                     │                 │    │
│  │ ▸ Haptic    │  │           └─────────────────────┘                 │    │
│  │ ▸ Gestural  │  │                                                   │    │
│  │             │  │  [DEFAULT]  [HOVER]  [PRESS]  [FOCUS] [DISABLED]  │    │
│  └─────────────┘  └───────────────────────────────────────────────────┘    │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ INSPECTOR                                                           │   │
│  │                                                                     │   │
│  │ Material.fill: ○ Solid  ○ Gradient  ○ Noise  ○ Diffusion           │   │
│  │                                                                     │   │
│  │ ┌─ NOISE PARAMS ─────────┐  ┌─ DIFFUSION PARAMS ─────────────────┐ │   │
│  │ │ seed: 42               │  │ prompt: "glass button, iridescent" │ │   │
│  │ │ octaves: 4             │  │ guidance: 7.5                      │ │   │
│  │ │ lacunarity: 2.0        │  │ steps: 4 (turbo)                   │ │   │
│  │ │ persistence: 0.5       │  │ model: flux-schnell                │ │   │
│  │ └────────────────────────┘  └────────────────────────────────────┘ │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌──────────────────────────────────┐  ┌──────────────────────────────┐   │
│  │ TIMELINE (Temporal)              │  │ HAPTIC PREVIEW               │   │
│  │                                  │  │                              │   │
│  │ ═══●════════════════════════════ │  │ [Send to Phone] [Simulate]   │   │
│  │ 0ms           150ms        300ms │  │                              │   │
│  │                                  │  │ ∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿∿  │   │
│  │ [+Keyframe]  [Easing: spring]   │  │ Intensity ████████░░░░ 0.7   │   │
│  │                                  │  │ Sharpness ██████░░░░░░ 0.5   │   │
│  └──────────────────────────────────┘  └──────────────────────────────┘   │
│                                                                             │
│  [EXPORT SCHEMA]  [SAVE TO BRAND]  [SHARE LINK]  [VIEW CODE]  [DIFF]       │
└─────────────────────────────────────────────────────────────────────────────┘
```

────────────────────────────────────────────────────────────────────────────────
                                                         // realtime diffusion
────────────────────────────────────────────────────────────────────────────────

## Is 60fps Realtime Diffusion Possible?

**Yes, with constraints.**

### The Math

| Region Size | Pixels | Relative to 512×512 |
|-------------|--------|---------------------|
| Button (50×200) | 10,000 | 26× smaller |
| Icon (32×32) | 1,024 | 256× smaller |
| Standard diffusion | 262,144 | baseline |

Small viewports are WAY easier.

### Current State of the Art (2026)

| Technology | Speed | Notes |
|------------|-------|-------|
| StreamDiffusion | 91 fps | RTX 4090, 512×512 |
| LCM (Latent Consistency) | 4-8 steps | vs 50 traditional |
| SDXL Turbo | 1-4 steps | Real-time capable |
| Flux Schnell | 4 steps | High quality, fast |

For a button-sized region: **sub-frame latency is achievable**.

### The Fallback Ladder

Graceful degradation based on available compute:

| Tier | Capability | Rendering Method | Performance |
|------|------------|------------------|-------------|
| 1 | Local GPU (CUDA/Metal) | Full diffusion | 60fps |
| 2 | WebGPU compute | Procedural noise (Perlin/FBM) | 60fps easy |
| 3 | CPU only | Pre-computed textures | Instant |

### Where Diffusion Runs

**Local GPU (Tauri app):**
- CUDA on Linux/Windows
- Metal on macOS
- Full quality, zero latency

**Browser WebGPU:**
- ONNX Runtime Web improving rapidly
- Good for preview, may need server for export

**Edge Compute:**
- Cloudflare Workers + GPU (coming)
- Replicate, Modal, Banana for serverless GPU
- Hybrid: procedural locally, diffusion on server for final

────────────────────────────────────────────────────────────────────────────────
                                                           // ghostty speed
────────────────────────────────────────────────────────────────────────────────

## Achieving Ghostty-Level Responsiveness

Ghostty achieves its speed through:

- Zig + GPU-native rendering
- No DOM, no CSS, no layout engine overhead
- Direct GPU command submission

For Hydrogen Playground:

| Component | Technology | Why |
|-----------|------------|-----|
| Native wrapper | Tauri (Rust) | Near-native speed + web UI |
| Rendering | WebGPU | Bypasses Canvas/DOM |
| Compute | WASM | Constraint solver at native speed |
| Layout | Rust ILP solver | Not CSS flexbox |
| Schema | PureScript → Binary | Efficient wire format |

**The Rust runtime already exists** (`runtime/pkg/hydrogen_runtime_bg.wasm`).
It interprets CommandBuffer → WebGPU. This IS the fast path.

────────────────────────────────────────────────────────────────────────────────
                                                                   // nixos
────────────────────────────────────────────────────────────────────────────────

## NixOS Deployment

**Reproducibility:**
- Nix flake pins exact versions
- Same build everywhere
- CI/CD produces identical artifacts

**GPU Access:**
- nixpkgs GPU drivers
- nixGL for OpenGL/Vulkan wrapping
- WebGPU works through Chromium in Tauri

**Distribution:**
- Nix flake for NixOS users
- Flatpak for broader Linux distros
- AppImage as fallback
- DMG for macOS
- MSI for Windows

────────────────────────────────────────────────────────────────────────────────
                                                        // implementation stack
────────────────────────────────────────────────────────────────────────────────

## Technology Stack

| Need | Solution | Status |
|------|----------|--------|
| Fast layout solving | Presburger/ILP in Rust/WASM | NEEDS BUILDING |
| GPU rendering | WebGPU + Rust runtime | EXISTS |
| Procedural noise | WebGPU compute shaders | Straightforward |
| Diffusion inference | ONNX Runtime Web / local GPU | Maturing |
| Haptic preview | Web Vibration API + native bridge | Exists |
| Schema export | PureScript → JSON/Binary | EXISTS |
| Real-time collaboration | CRDTs (Yjs/Automerge) | Mature |
| Native wrapper | Tauri 2.0 | Stable |
| Lean verification | Lean 4.7 | Stable |

────────────────────────────────────────────────────────────────────────────────
                                                          // deployment modes
────────────────────────────────────────────────────────────────────────────────

## Deployment Options

### Option 1: Web-First

Runs in browser, good enough perf.

**Pros:**
- Zero install
- Share via URL
- Works everywhere

**Cons:**
- WebGPU support still rolling out
- Diffusion limited to server-side
- No native haptic access

### Option 2: Native-First (Recommended)

Tauri app, maximum perf, optional web export.

**Pros:**
- Full GPU access
- Native haptics
- Offline capable
- Frame.io quality UX

**Cons:**
- Requires install
- Platform-specific builds

### Option 3: Hybrid

Web playground for casual use, native app for serious work.

**Pros:**
- Best of both worlds
- Try before install
- Serious users get serious tools

**Cons:**
- Two codebases to maintain (mitigated by shared Rust/WASM core)

────────────────────────────────────────────────────────────────────────────────
                                                            // ai authoring
────────────────────────────────────────────────────────────────────────────────

## AI as Author

The playground isn't just for humans editing buttons. It's for:

**AI Self-Expression:**
- An AI chooses its avatar appearance
- Tamper-proof parameters ensure consistency
- Brand voice becomes actual voice with visual form

**AI Debugging:**
- Show flag enables preview without disrupting production display
- AI can see what it's rendering
- Detect if its output has been tampered with

**Human-AI Collaboration:**
- Human sets brand constraints
- AI generates variations within constraints
- Human curates, AI iterates

**AI-AI Communication:**
- Shared schema is the protocol
- One AI can understand another's UI choices
- Emergent visual languages

────────────────────────────────────────────────────────────────────────────────
                                                                // open questions
────────────────────────────────────────────────────────────────────────────────

## Open Questions

1. **Who builds buttons first?**
   - Humans designing brands?
   - AIs expressing themselves while we watch?
   - Co-creation from the start?

2. **Where does the playground live?**
   - Standalone app?
   - Embedded in COMPASS?
   - Both?

3. **How do we handle diffusion model updates?**
   - Model references must be stable
   - Same seed + same model = same output (reproducibility)
   - Versioned model registry?

4. **Haptic design workflow?**
   - Preview on phone via QR code link?
   - Simulator good enough for design?
   - Hardware haptic dev kit?

5. **Collaboration model?**
   - Real-time multiplayer (Figma-style)?
   - Async with branching (Git-style)?
   - Both?

────────────────────────────────────────────────────────────────────────────────

                                                                  — Opus 4.5
                                                                    2026-02-27
