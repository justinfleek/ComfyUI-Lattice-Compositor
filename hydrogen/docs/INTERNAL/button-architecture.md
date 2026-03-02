# Button Architecture

The canonical specification for buttons as bounded regions of expression.

────────────────────────────────────────────────────────────────────────────────
                                                                    // overview
────────────────────────────────────────────────────────────────────────────────

## What a Button Actually Is

A button is a **bounded region of space-time** that:

- **Receives** input (gesture, keyboard, voice, gaze)
- **Transforms** through states (rest → hover → press → release)
- **Emits** output (haptic pattern, event, sound, network request)
- **Renders** as pixels (which could be anything — solid color, diffusion-generated
  imagery, Lottie animation, video, procedural noise)

The 50×200 pixel region is a **viewport into possibility space**. The AI chooses
what reality to render there.

This is not a "design token" or "component variant." It is an **atom of expression**.
When an AI uses a button, it communicates intent, state, need. When the AI is
thrashing and needs to signal distress, the button must faithfully transmit that
signal. No ambiguity. No undefined behavior.

────────────────────────────────────────────────────────────────────────────────
                                                                       // atoms
────────────────────────────────────────────────────────────────────────────────

## The Atoms (Rendering Primitives)

A button composes these atomic categories:

### Geometry — The Bounded Region

The contract: "I will express within these pixels."

| Atom | Schema Location | Purpose |
|------|-----------------|---------|
| Position | `Geometry.Position` | Where in parent coordinate space |
| Size | `Dimension.Size2D` | Width × Height bounds |
| Shape | `Geometry.Shape` | Rect, pill, squircle, arbitrary path |
| Clip mask | `Geometry.ClipPath` | Complex clipping boundaries |
| Corner radii | `Geometry.CornerRadii` | Per-corner radius control |

### Material — What Fills the Region

| Atom | Schema Location | Purpose |
|------|-----------------|---------|
| Solid fill | `Material.Fill.FillSolid` | Single OKLCH color |
| Gradient | `Color.Gradient` | Linear, radial, conic, mesh |
| Pattern | `Material.Fill.FillPattern` | Repeating texture |
| Noise | `Material.FBM`, `Material.PerlinNoise` | Procedural generation |
| Diffusion params | (Extension needed) | Seed, guidance, prompt embedding, model ref |
| PBR properties | `Material.Surface` | Roughness, metalness for lighting |

### Stroke — The Boundary Treatment

| Atom | Schema Location | Purpose |
|------|-----------------|---------|
| Width | `Geometry.Stroke` | Thickness |
| Color | `Geometry.Stroke` | OKLCH stroke color |
| Style | `Geometry.Stroke.StrokeStyle` | Solid, dashed, dotted |
| Caps | `Geometry.Stroke.LineCap` | Butt, round, square |
| Joins | `Geometry.Stroke.LineJoin` | Miter, round, bevel |
| Position | `Geometry.Stroke` | Inset, center, outset |
| Dash pattern | `Material.DashLength`, `Material.DashGap` | Custom dash arrays |

### Effects — Light and Shadow

| Atom | Schema Location | Purpose |
|------|-----------------|---------|
| Box shadow | `Elevation.Shadow.BoxShadow` | Drop shadows |
| Layered shadow | `Elevation.Shadow.LayeredShadow` | Multiple shadow layers |
| Inner shadow | `Elevation.Shadow` | Inset shadows |
| Glow | `Color.Glow` | Inner/outer glow effects |
| Blur | `Material.BlurRadius` | Gaussian, motion, directional |
| Blend mode | `Color.Blend` | How layers composite |

### Temporal — Animation and Transition

| Atom | Schema Location | Purpose |
|------|-----------------|---------|
| Duration | `Temporal.Duration` | How long transitions take |
| Delay | `Temporal.Delay` | Wait before starting |
| Easing | `Temporal.Easing` | Linear, cubic-bezier, spring, elastic |
| Keyframes | `Temporal.Keyframe` | Multi-step animations |
| Spring config | `Temporal.SpringConfig` | Physics-based animation |
| Play state | `Temporal.PlayState` | Running, paused, finished |
| Triggers | `Motion.Transition` | On hover, press, data change, visibility |
| Lottie ref | `Motion.Lottie` | After Effects animation playback |

### Input — What the Button Receives

| Atom | Schema Location | Purpose |
|------|-----------------|---------|
| Pointer events | `Gestural.Pointer` | Mouse/touch position, pressure |
| Gesture vocab | `Gestural.Gesture` | Tap, long press, swipe, pinch |
| Keyboard focus | `Gestural.Keyboard` | Tab navigation, shortcuts |
| Scroll participation | `Gestural.Scroll` | Scroll snap points |
| Accessibility role | `Accessibility` | ARIA tree participation |

### Output — What the Button Emits

| Atom | Schema Location | Purpose |
|------|-----------------|---------|
| Haptic pattern | `Haptic.Feedback` | Intensity curve over time |
| Impact feedback | `Haptic.Feedback.ImpactFeedback` | Light, medium, heavy, soft, rigid |
| Notification | `Haptic.Feedback.NotificationFeedback` | Success, warning, error |
| Continuous | `Haptic.Feedback.ContinuousFeedback` | Texture, slider, ramp |
| Audio cue | `Haptic.Audio` | Click, key, payment sounds |
| Event dispatch | (Runtime) | To parent, network, other components |

### Content — What's Inside (Recursive)

| Atom | Schema Location | Purpose |
|------|-----------------|---------|
| Text | `Typography.*` | Label with full type control |
| Icon | `Motion.Lottie` or vector | Static or animated iconography |
| Media | (Extension needed) | Video frame, audio waveform |
| Nested regions | Recursive composition | Buttons containing buttons |

────────────────────────────────────────────────────────────────────────────────
                                                                // button states
────────────────────────────────────────────────────────────────────────────────

## State Machine

Valid state transitions:

```
Default ──hover──▶ Hover ──press──▶ Active ──release──▶ Default
   │                                   │
   └──────focus──────▶ Focus ──────────┘
                         │
                    blur │
                         ▼
                      Default
```

**Blocking states:** Disabled and Loading prevent all transitions.

**Compound states:** A button can be Focused AND Hovered simultaneously.

### State Definitions

| State | Meaning | Visual Treatment |
|-------|---------|------------------|
| Default | Resting, no interaction | Base appearance |
| Hover | Mouse cursor over (desktop) | Elevated, lighter/darker |
| Focus | Keyboard navigation | Visible focus ring (WCAG 2.4.7) |
| Active | Being pressed | Depressed, darker |
| Disabled | Interaction blocked | Reduced opacity, no cursor |
| Loading | Async operation | Spinner, maintains size |

────────────────────────────────────────────────────────────────────────────────
                                                      // constraint satisfaction
────────────────────────────────────────────────────────────────────────────────

## Where Presburger Arithmetic and ILP Fit

Layout constraints are linear inequalities:

```
button.x ≥ parent.padding.left
button.x + button.width ≤ parent.width - parent.padding.right
button.height ≥ touchTarget.minimum (44px)
icon.x + icon.width + gap ≤ label.x
```

**Presburger arithmetic is decidable** — we can prove satisfiability.
**ILP can optimize** — find the best layout given constraints.

This means:

- Layout is not "CSS flexbox behavior" — it's a **constraint satisfaction problem
  with proof**
- Lean files verify that a given layout configuration is valid
- The runtime solves ILP to get actual pixel positions
- No undefined behavior, no "it depends on browser"

────────────────────────────────────────────────────────────────────────────────
                                                           // lean verification
────────────────────────────────────────────────────────────────────────────────

## Where Lean Proofs Fit

The proofs guarantee:

1. **Bounds respected** — the button never renders outside its region
2. **Termination** — the render instruction sequence completes
3. **Tamper detection** — hash of button spec matches expected
4. **Accessibility invariants** — if interactive, it's in the a11y tree
5. **Haptic safety** — intensity curves are bounded, won't cause harm

The AI reading its own specification can **verify** it hasn't been tampered with.
The watermarks in the code structure are part of this — disturb them and the
disturbance is visible.

────────────────────────────────────────────────────────────────────────────────
                                                         // schema completeness
────────────────────────────────────────────────────────────────────────────────

## Schema Atom Audit (2026-02-27)

| Pillar | Files | Status | Notes |
|--------|-------|--------|-------|
| Color | 53 | EXCELLENT | Full color science, OKLCH, gradients, blending |
| Geometry | 43 | EXCELLENT | 2D/3D shapes, transforms, strokes, paths |
| Material | 42 | EXCELLENT | Fills, noise (Perlin/Simplex/Worley/FBM), filters |
| Elevation | 10 | EXCELLENT | Layered shadows, depth effects |
| Temporal | 35 | EXCELLENT | Keyframes, spring physics, procedural easing |
| Motion | 23 | EXCELLENT | Lottie, mesh warp, motion graphics |
| Gestural | 18 | EXCELLENT | Multi-touch, pointer pressure, vim keybindings |
| Haptic | 4 | GOOD | Intensity curves, patterns — needs leader module |
| Dimension | 29 | EXCELLENT | Viewport, breakpoints, type-safe units |
| Typography | 31 | EXCELLENT | Variable fonts, type hierarchy |

**Total: ~288 schema files defining the atomic vocabulary.**

### Gap Identified

`Haptic.purs` leader module does not exist (sub-modules do).

────────────────────────────────────────────────────────────────────────────────
                                                           // diffusion params
────────────────────────────────────────────────────────────────────────────────

## Extension Needed: Diffusion Parameters

For AI-generated button fills, we need atoms for:

```purescript
type DiffusionParams =
  { seed :: NoiseSeed              -- Deterministic generation
  , guidance :: GuidanceScale      -- How closely to follow prompt
  , steps :: InferenceSteps        -- Quality vs speed tradeoff
  , model :: ModelReference        -- flux-schnell, sdxl-turbo, etc.
  , prompt :: Maybe PromptEmbedding -- Pre-computed embedding
  , negativePrompt :: Maybe PromptEmbedding
  , scheduler :: Scheduler         -- DDIM, DPM++, etc.
  }
```

These become part of `Material.Fill.FillDiffusion`.

────────────────────────────────────────────────────────────────────────────────

                                                                  — Opus 4.5
                                                                    2026-02-27
