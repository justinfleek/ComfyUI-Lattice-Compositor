# Motion & Temporal Architecture

> "Animation is not decoration. It is the evolution of state over time."

This document outlines the architectural vision for the Hydrogen Motion subsystem, moving away from legacy CSS-bound concepts toward a physics-based, world-model ready implementation.

## 1. Core Philosophy: World-Model Rendering

In the Straylight/Hydrogen vision, we are not just manipulating DOM elements. We are rendering a view into a **World Model**.

*   **Surfaces are Tensor Fields**: Every UI element (button, panel, frame) is potentially a tensor field whose properties (color, noise, displacement) can be driven by AI diffusion models (LATTICE) in real-time.
*   **Time is a Dimension**: Animation is the evolution of these fields along the temporal axis.
*   **Physics, Not Tweens**: We prioritize physics-based motion (springs, fluid dynamics) over fixed-duration tweens because physics preserves causality and agency.

## 2. The Temporal Pillar

The `Hydrogen.Schema.Temporal` namespace defines the laws of time in this universe.

### Atoms (Units of Time & State)
*   **`Duration`**: A span of time (unit-agnostic, stored as ms).
*   **`Timecode`**: SMPTE standard location in a timeline.
*   **`PlayState`**: `Running` | `Paused` (The flow of time).
*   **`Direction`**: `Normal` | `Reverse` | `Alternate` (The arrow of time).
*   **`Iteration`**: Cycle count.

### Molecules (Temporal Structures)
*   **`Keyframe`**: A value anchored at a specific `Progress` (0.0 - 1.0).
*   **`TimeRange`**: An active interval (`Start` to `End`).
*   **`Delay`**: Pre-roll wait time.

### Compounds (Orchestration)
*   **`Animation`**: The definition of a change.
    *   `Transition`: Simple A -> B.
    *   `KeyframeAnim`: Multi-step interpolation.
    *   `SpringAnim`: Simulation without fixed duration.
    *   `PhysicsAnim`: Velocity/Friction simulation.
*   **`Timeline`**: Composition of animations (`Sequence`, `Parallel`, `Stagger`).

## 3. Persistence vs. Fill Mode

We have abandoned the CSS term "Fill Mode" in favor of **Persistence**.

*   **Legacy (CSS)**: "Fill Mode" describes applying styles outside the animation window.
*   **Hydrogen (State)**: "Persistence" describes the thermodynamic behavior of a value after energy input ceases.

**Persistence Atoms:**
*   `None` (Elastic): System returns to ground state (initial value).
*   `PersistEnd` (Plastic): System retains the final high-energy state.
*   `PersistStart` (Anticipatory): System assumes start state immediately upon scheduling.
*   `PersistBoth` (Full): System is fully state-captured at both ends.

## 4. Motion Subsystem Porting Plan

The legacy `Hydrogen.Component.Motion` system is being ported to `Hydrogen.Schema.Motion` and `Hydrogen.Element.Motion`.

### Objectives
1.  **Remove CSS Dependencies**: All motion must be defined by Schema atoms.
2.  **Type Safety**: No "stringly typed" easings or durations.
3.  **Composability**: Animations must be composable data structures.

### Migration Map

| Legacy Concept | New Schema | Notes |
| :--- | :--- | :--- |
| `TransitionType` | `Hydrogen.Schema.Motion.Transition` | Defines the *visual* effect (Slide, Fade) |
| `TransitionConfig` | `Hydrogen.Schema.Temporal.Animation` | Defines the *temporal* behavior |
| `Milliseconds` | `Hydrogen.Schema.Temporal.Duration` | Standardized time unit |
| `Easing` | `Hydrogen.Schema.Temporal.Easing` | Unified easing curves |
| `FillMode` | `Hydrogen.Schema.Temporal.Persistence` | State persistence |

## 5. Future: LATTICE Integration

This architecture prepares for LATTICE by ensuring that **all motion is data**.

*   An AI agent can generate a `Timeline` structure to describe a complex UI interaction.
*   That `Timeline` can be validated, simulated, and rendered deterministically.
*   Noise parameters for textures can be animated using the same `Spring` physics as position.

---
*Created: 2026-02-25*
