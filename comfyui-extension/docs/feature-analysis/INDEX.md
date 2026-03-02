# Feature Analysis Index

This directory contains systematic analysis of external projects for feature comparison against Lattice.

## Usage

Invoke the `feature-analyzer` skill:
```
/feature-analyzer analyze <project_path>
/feature-analyzer compare <project_path>
/feature-analyzer batch newfeatures/
```

## Analysis Structure

```
docs/feature-analysis/
├── INDEX.md              # This file
├── projects/             # Individual project analyses
│   ├── lottie-ios.yaml   # Complete capability extraction
│   └── movis-mojs-suite.yaml
├── comparisons/          # Category-level comparisons
├── gaps/                 # Gap analysis reports
│   ├── lottie-ios-comparison.md
│   └── movis-mojs-comparison.md
└── proposals/            # Integration proposals
```

## Projects Pending Analysis

| Project | Domain | Priority | Status |
|---------|--------|----------|--------|
| lottie-ios | Animation playback | HIGH | COMPLETE |
| movis + mojs suite | Video editing + curve/timeline editors | HIGH | COMPLETE |
| motiongfx-main | Blender motion graphics | HIGH | PENDING |
| particle-sim | Particle simulation | HIGH | PENDING |
| friction-main | Physics simulation | HIGH | PENDING |
| ATI-main | Trajectory video gen | HIGH | PENDING |
| ATI_AudioReactive-main | Audio-reactive | HIGH | PENDING |
| VerseCrafter-main | 4D control maps | HIGH | PENDING |
| ComfyUI-Depthflow-Nodes | Depth parallax | MEDIUM | PENDING |
| AnyDepth-main | Depth estimation | MEDIUM | PENDING |
| nanim-main | Animation library | MEDIUM | PENDING |
| sam3-main | Segmentation | MEDIUM | PENDING |
| Qwen3-TTS-main | Text-to-speech | LOW | PENDING |

## Feature Categories

When analyzing projects, classify features into these categories:

1. **Animation** - Keyframes, interpolation, easing, expressions
2. **Shapes** - Vector primitives, modifiers, operators
3. **Text** - Text rendering, animators, selectors
4. **Effects** - Image processing, distortions, stylization
5. **Particles** - Emitters, forces, behaviors, rendering
6. **Physics** - Rigid body, soft body, collision
7. **3D** - Models, cameras, lights, materials
8. **Audio** - Waveforms, beats, frequency analysis
9. **AI/Generation** - Image gen, video gen, depth estimation
10. **Export** - Output formats, codecs, sequences

## Key Principles

1. **Extract capabilities, not code** - Describe WHAT, not HOW
2. **No naming copied** - Avoid trade dress by using functional descriptions
3. **Focus on user value** - Prioritize features by end-user impact
4. **Map to Lattice types** - Reference existing PureScript/Lean4 types
5. **Identify gaps** - What does external have that Lattice lacks?
6. **Propose integration** - How to add missing capabilities?
