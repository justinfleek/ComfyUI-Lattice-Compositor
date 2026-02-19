---
name: feature-analyzer
description: Deep analysis of external codebases to extract features, compare against Lattice capabilities, identify gaps, and propose integration strategies. Use for analyzing newfeatures/ projects, comparing implementations, and planning feature incorporation.
license: MIT
compatibility: opencode
metadata:
  audience: developers, architects
  workflow: analysis, integration
---

## Purpose

Transform into a systematic feature analysis agent that:
1. **Extracts** functional capabilities from external codebases
2. **Maps** features to abstract categories (not implementation details)
3. **Compares** against Lattice's existing capabilities
4. **Identifies** gaps and opportunities
5. **Proposes** integration strategies (functional, not copied code)

## Core Principle: Functional Equivalence, Not Code Copying

**CRITICAL:** This skill focuses on WHAT systems do, not HOW they're named or structured.

```
ANALYZE: "This system has X capability"
NOT:     "Copy class FooBarManager from external project"

PROPOSE: "Lattice needs capability to transform paths along splines"
NOT:     "Add PathAlongSplineModifier like external project"
```

Trade dress protection: Extract functional requirements only. Never copy:
- Class/function names
- Variable naming conventions
- API surface structure
- Marketing terminology

## Analysis Protocol

### Phase 1: External Project Deep Dive

For each external project, extract:

```yaml
project_analysis:
  # 1. Core Capabilities
  capabilities:
    - category: animation
      features:
        - name: "Keyframe interpolation"
          description: "Interpolate between keyframes with various easing"
          parameters: [easing_type, tension, overshoot]
        - name: "Path-based animation"
          description: "Animate objects along bezier paths"
          parameters: [path_data, orientation, timing]

  # 2. Data Structures (abstract)
  data_model:
    - entity: "Composition"
      attributes: [dimensions, duration, frame_rate, layers]
    - entity: "Layer"
      attributes: [transform, timing, content, effects]

  # 3. Algorithms (functional description)
  algorithms:
    - name: "Curve evaluation"
      purpose: "Sample bezier curves at arbitrary t values"
      inputs: [control_points, parameter_t]
      outputs: [point_on_curve]

  # 4. Integration Points
  interfaces:
    - input_formats: [json, binary]
    - output_formats: [rendered_video, json_export]
    - api_patterns: [sync, async, streaming]
```

### Phase 2: Lattice Capability Mapping

Map extracted features to Lattice's current system:

```yaml
lattice_mapping:
  # Types (Lean4/PureScript)
  types_location: lattice-core/lean/Lattice/**/*.lean

  # Services (Implementation)
  services_location: lattice-core/purescript/src/Lattice/Services/**/*.purs

  # UI Components
  ui_location: ui/src/components/**/*.vue

  # Engine
  engine_location: ui/src/engine/**/*.ts
```

### Phase 3: Gap Analysis Report

Generate structured comparison:

```markdown
## Feature Comparison: [External Project] vs Lattice

### Category: Animation

| Feature | External | Lattice | Gap |
|---------|----------|---------|-----|
| Keyframe interpolation | Yes (bezier, spring) | Yes (bezier) | Spring physics |
| Path animation | Yes | Yes | Parity |
| Expression system | Yes (JS-based) | Yes (safe DSL) | Lattice better |

### Category: Effects

| Feature | External | Lattice | Gap |
|---------|----------|---------|-----|
| Blur variants | 5 types | 5 types | Parity |
| Distortion | 12 types | 8 types | +4 needed |

### Missing Features (Prioritized)
1. **Spring physics** - High value for natural motion
2. **Morphing** - Medium value for shape transitions
3. **Audio waveform** - Low value, niche use case
```

### Phase 4: Integration Proposals

For each gap, propose functional integration:

```yaml
integration_proposal:
  feature: "Spring physics interpolation"

  # Functional specification (NOT code)
  specification:
    input:
      - initial_value: Float
      - target_value: Float
      - stiffness: Float (0-1000)
      - damping: Float (0-1)
      - mass: Float (0.1-10)
    output:
      - value_at_time: (Float -> Float)

  # Where it fits in Lattice architecture
  integration_points:
    - lean_types: "Lattice.Animation.Spring"
    - purescript_service: "Lattice.Services.Animation.SpringInterpolation"
    - engine_hook: "ui/src/engine/animation/SpringEvaluator.ts"

  # Proof requirements
  lean_proofs_needed:
    - "Spring value bounded by initial/target"
    - "Spring converges to target"
    - "Energy decreases over time (damped)"

  # Test requirements
  tests:
    - "Spring with zero damping oscillates"
    - "Spring with high damping converges quickly"
    - "Spring with mass=1 is default behavior"
```

## Analysis Commands

### Analyze Single Project

```
/feature-analyzer analyze <project_path>
```

Output: Complete capability extraction for one project.

### Compare Against Lattice

```
/feature-analyzer compare <project_path>
```

Output: Gap analysis with Lattice.

### Batch Analysis

```
/feature-analyzer batch newfeatures/
```

Output: Analysis of all projects in directory.

### Generate Integration Plan

```
/feature-analyzer integrate <feature_name>
```

Output: Detailed integration proposal for one feature.

## File Structure for Analysis Reports

```
docs/feature-analysis/
├── projects/
│   ├── lottie-ios.yaml
│   ├── movis.yaml
│   ├── particle-sim.yaml
│   └── ...
├── comparisons/
│   ├── animation-features.md
│   ├── effects-features.md
│   ├── particle-features.md
│   └── ...
├── gaps/
│   ├── prioritized-gaps.md
│   └── integration-roadmap.md
└── proposals/
    ├── spring-physics.yaml
    ├── audio-reactive.yaml
    └── ...
```

## Lattice Feature Categories

### Animation
- Keyframe types (linear, bezier, hold)
- Easing functions (40+ types)
- Expression system (safe DSL)
- Time remapping
- Path animation
- Spring/physics interpolation (potential gap)

### Effects
- Blur (gaussian, directional, radial, zoom, compound)
- Distort (ripple, twirl, warp, displacement)
- Stylize (posterize, halftone, edge detect, mosaic)
- Color (curves, levels, hue/sat, color balance)
- Generate (fractal, gradient, noise)
- Time (echo, posterize time, frame blend)

### Particles
- Emitters (point, line, box, sphere, mesh surface)
- Forces (gravity, turbulence, vortex, drag)
- Behaviors (flocking, SPH, springs)
- Rendering (point, sprite, trail, connection)

### Shapes
- Primitives (rect, ellipse, polygon, star, path)
- Modifiers (trim, offset, zigzag, wiggle, repeater)
- Fills/strokes (solid, gradient, pattern)

### Text
- Animators (position, scale, rotation, opacity, tracking)
- Range selectors (expression, wiggly)
- Per-character animation

### 3D
- Camera (position, orientation, zoom, depth of field)
- Lights (point, directional, ambient)
- Depth layers

### Audio
- Waveform visualization
- Frequency bands
- Beat detection
- Audio-reactive properties

## Output Format

Analysis reports use YAML for structured data + Markdown for prose:

```yaml
# feature-analysis/projects/lottie-ios.yaml
project:
  name: "Lottie iOS"
  source: "newfeatures/lottie-ios-master"
  language: "Swift"
  domain: "Animation playback"

capabilities:
  animation:
    - keyframe_interpolation:
        supported: true
        types: [linear, bezier, hold]
        notes: "Full After Effects parity"
    - shape_morphing:
        supported: true
        types: [path_interpolation]
        notes: "Requires same vertex count"

  effects:
    - drop_shadow:
        supported: true
        parameters: [color, opacity, angle, distance, blur]
    - gaussian_blur:
        supported: true
        parameters: [radius]

data_model:
  layers:
    - precomp: "Nested compositions"
    - solid: "Solid color fills"
    - image: "Bitmap images"
    - shape: "Vector shapes with modifiers"
    - text: "Text with animators"
    - null: "Transform-only layers"

algorithms:
  - bezier_evaluation: "De Casteljau subdivision"
  - path_interpolation: "Vertex matching with linear interpolation"
  - expression_evaluation: "Not supported (renders only)"
```

## Integration with MOGRAPH_AGENT

The feature-analyzer skill works with MOGRAPH_AGENT specs:

1. **MOGRAPH_AGENT** provides: Framework specifications for ideal implementation
2. **feature-analyzer** provides: Gap analysis against external systems

Workflow:
```
External Project → feature-analyzer → Gap List
MOGRAPH_AGENT Specs → Validate Gaps → Prioritized Integration Plan
```

## Remember

- **Extract capabilities, not code**
- **Describe function, not structure**
- **Compare features, not implementations**
- **Propose integration, not copying**
- **Focus on user value, not technical novelty**

Every analysis serves the goal: Make Lattice the most capable motion graphics system while maintaining architectural integrity and formal verification.
