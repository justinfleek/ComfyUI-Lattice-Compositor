# Glossary

> Last Updated: December 2025

Terminology definitions for Lattice Compositor.

---

## A

**Adjustment Layer**
*(Deprecated, use Effect Layer)* A layer that applies effects to all layers below it in the stack.

**Anchor Point**
*(Use "Origin" in Lattice)* The point around which a layer rotates and scales.

**Asset**
Any external file (image, video, audio, font) imported into a project.

**Audio Reactivity**
Connecting layer properties to audio analysis data (amplitude, frequency, beats).

---

## B

**Beat Detection**
Automatic identification of musical beats in audio for animation synchronization.

**Bezier Curve**
A mathematically defined curve using control points, used for both paths and animation easing.

**Blend Mode**
How a layer's pixels combine with layers below it (multiply, screen, overlay, etc.).

---

## C

**Checkpoint**
A saved particle system state at a specific frame, enabling scrub-safe simulation.

**Compartment**
*(SES)* An isolated JavaScript execution environment for secure expression evaluation.

**Composition**
A container for layers with defined dimensions, duration, and frame rate.

**ComfyUI**
Open-source node-based UI for Stable Diffusion workflows. Lattice is a ComfyUI extension.

**ControlNet**
AI model that adds conditioning to image generation (depth, pose, edges).

**Curve Editor**
*(Alternative to "Graph Editor")* UI for editing animation curves with bezier handles.

---

## D

**DepthAnything**
AI model for monocular depth estimation from images.

**Depthflow**
2.5D parallax effect that creates depth from a single image using depth maps.

**Deterministic**
Producing identical output for identical input. Required for AI video workflows.

---

## E

**Easing**
The rate of change of an animation over time (ease-in, ease-out, bounce, etc.).

**Effect Layer**
*(Alternative to "Adjustment Layer")* A layer that applies effects to layers below.

**Expression**
A JavaScript-like formula that dynamically calculates property values.

**Export**
Converting a composition to video, image sequence, or AI-specific format.

---

## F

**FFT (Fast Fourier Transform)**
Algorithm for analyzing audio frequency content.

**Frame Rate (FPS)**
Frames per second. Lattice defaults to 16fps for AI video compatibility.

**Fractal Noise**
Procedurally generated noise pattern using multiple octaves.

---

## G

**Glow**
Effect that adds luminous bloom around bright areas.

**Group**
A container layer that holds multiple child layers.

---

## H

**Handle**
A control point on a bezier curve that affects its shape.

**History**
The undo/redo system storing project snapshots.

---

## I

**Interpolation**
Calculating intermediate values between keyframes.

**IP Adapter**
AI model that uses image prompts for generation conditioning.

**Isolate**
*(Alternative to "Solo")* Show only this layer, hiding all others.

---

## K

**Keyframe**
A defined value at a specific frame. Intermediate frames are interpolated.

---

## L

**Layer**
A single element in a composition (image, video, text, shape, etc.).

**LayerType**
One of 26 layer categories: image, video, text, shape, spline, particle, camera, etc.

**Lattice**
The motion graphics compositor (this software).

---

## M

**Matte**
An image used to define transparency (alpha channel).

**Migration**
Automatic upgrading of project files to newer schema versions.

**Motion Path**
*(Invisible path)* A bezier curve that guides animation but isn't rendered.

**MotionCtrl**
AI video model that uses camera trajectory data for control.

**Mulberry32**
Seeded random number generator used for deterministic effects.

---

## N

**Nested Composition**
*(Alternative to "Precomp")* A composition placed inside another composition.

**Normal Map**
An image encoding surface direction for 3D lighting calculations.

**Null Layer**
*(Deprecated, use "Control Layer")* An invisible layer used as a parent.

---

## O

**Origin**
*(Alternative to "Anchor Point")* The transformation center point of a layer.

**Overlay**
A UI element drawn on top of the viewport (guides, handles, paths).

---

## P

**Particle**
A small rendered element in a particle system.

**Particle Emitter**
Configuration defining how particles are spawned and behave.

**Pinia**
Vue.js state management library used by Lattice.

**Playhead**
The marker indicating the current frame in the timeline.

**Precomp**
*(Use "Nested Composition" in Lattice)* A composition used as a layer.

**PropertyLink**
*(Alternative to "Pickwhip")* Connecting one property's value to another.

---

## R

**Rasterize**
Converting vector graphics to pixels.

**repeatAfter()**
*(Alternative to "loopOut()")* Expression function to repeat animation.

---

## S

**SAM (Segment Anything Model)**
Meta's AI model for image segmentation.

**Sandbox**
Isolated execution environment for untrusted code (expressions).

**Sapiens**
Meta's AI model for human pose and depth estimation.

**Schema Version**
The version number of the project file format.

**Scrub**
Dragging the playhead to preview different frames.

**SES (Secure EcmaScript)**
JavaScript security library for sandboxed execution.

**Spline**
A visible bezier path with stroke and/or fill.

**Stem Separation**
Splitting audio into components (vocals, drums, bass, other).

---

## T

**Template**
A pre-made project file with exposed parameters for customization.

**Three.js**
WebGL library used for Lattice's 3D rendering.

**Timeline**
The UI panel showing layer timing and keyframes.

**Track Matte**
Using one layer's luminance or alpha to mask another layer.

**Transform**
Position, scale, rotation, and opacity properties of a layer.

---

## U

**Undo**
Reverting to a previous project state.

---

## V

**Validation**
Checking data for correctness (schema, types, security).

**Viewport**
The main canvas area showing the composition.

**Vue**
JavaScript framework used for Lattice's UI.

---

## W

**Wan**
AI video model supporting point-based motion trajectories.

**Warp**
Geometric distortion effect.

**WebGL**
Browser API for GPU-accelerated graphics.

**Wiggle**
Expression function for procedural random animation.

---

## Trade Dress Alternatives

Lattice uses alternative terminology to respect Adobe trademarks:

| Industry Term | Lattice Term |
|---------------|--------------|
| Anchor Point | Origin |
| Pickwhip | PropertyLink |
| Graph Editor | Curve Editor |
| Precomp | Nested Composition |
| Adjustment Layer | Effect Layer |
| Solo | Isolate |
| loopOut() | repeatAfter() |
| Null Object | Control Layer |

---

## AI Video Terminology

| Term | Definition |
|------|------------|
| AnimateDiff | AI model adding motion to Stable Diffusion |
| CameraCtrl | Camera control extension for AnimateDiff |
| ControlNet | Conditioning model for guided generation |
| IP Adapter | Image prompt adapter for generation |
| MotionCtrl | Camera trajectory-based video control |
| VACE | Video AI Composer Engine |
| Wan | Point trajectory-based video control |
