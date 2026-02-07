# Product Requirements Document: Lattice Compositor

**Version:** 1.0
**Status:** Pre-Release
**Last Updated:** February 2026

---

## Executive Summary

Lattice Compositor is a professional motion graphics engine designed specifically for AI video generation workflows. It integrates directly with ComfyUI to provide industry-standard animation tools that export to formats consumed by AI video models like Wan 2.1, AnimateDiff, MotionCtrl, and VACE.

**Problem:** AI video creators need conditioning data (depth maps, motion trajectories, attention masks) but creating these requires jumping between multiple tools.

**Solution:** Lattice brings After Effects-level compositing directly into ComfyUI with one-click export to AI-native formats.

---

## Target Users

| User Type | Primary Need |
|-----------|--------------|
| AI Video Creators | Create motion trajectories and masks for Wan/AnimateDiff |
| Motion Designers | Professional keyframe animation with AI integration |
| VFX Artists | Depth-based compositing with AI segmentation |
| Content Creators | Quick motion graphics without After Effects |

---

## Core Features (MVP)

### 1. Layer System
- 17 layer types (image, video, text, shape, particle, camera, etc.)
- Hierarchical grouping and parenting
- Blend modes and opacity
- Per-layer effects

### 2. Animation Engine
- Keyframe-based animation for any property
- 35 easing functions (linear, ease, spring, elastic, bounce)
- Bezier curve editor
- Expression language (wiggle, bounce, inertia)
- Property linking between layers

### 3. Particle System
- 24 built-in presets (fire, smoke, rain, confetti, magic)
- Deterministic simulation (scrub-safe)
- Physics forces (gravity, wind, turbulence, attractors)
- Sub-emitters and collision detection

### 4. 3D Camera System
- 22 camera presets (orbit, dolly, crane, spiral)
- Depth of field with bokeh
- Camera shake variations
- Trajectory export for AI models

### 5. Export Formats
| Format | Target Model |
|--------|--------------|
| Matte Sequences | IP Adapter attention masks |
| Wan Trajectories | Wan 2.1 point motion |
| MotionCtrl Poses | MotionCtrl camera data |
| CameraCtrl JSON | AnimateDiff camera control |
| PNG/WebM/MP4 | Standard video output |

### 6. AI Integration
- Natural language animation: "fade in the title over 1 second"
- GPT-4o and Claude API support
- 30+ tool actions for layer creation, keyframing, effects
- Conversation memory for iterative refinement

---

## Technical Requirements

### Frontend
- Vue 3.5 + TypeScript
- Pinia state management
- Three.js r170 for rendering
- WebGL2 required

### Backend
- Python 3.10+
- ComfyUI integration (custom nodes)
- Optional AI models: DepthAnything, SAM, Sapiens, Demucs

### Browser Support
- Chrome 90+ (primary)
- Firefox 90+
- Edge 90+
- Safari 15+

---

## The Determinism Rule

For AI video generation, every frame MUST be reproducible:

> `evaluate(frame, project)` always returns identical results for identical inputs.

Implementation:
- Seeded RNG (Mulberry32 algorithm)
- Checkpoint system for particle state
- Pure evaluation (no Math.random, no Date.now)

---

## Non-Goals (Out of Scope for v1.0)

- Real-time collaboration
- Cloud project storage
- Mobile/tablet support
- Standalone desktop app (ComfyUI extension only)
- Plugin/extension system

---

## Success Metrics

| Metric | Target |
|--------|--------|
| Installation success rate | > 95% |
| Build without errors | 100% |
| Test pass rate | > 99% |
| Export format coverage | 6+ AI formats |
| Performance (100 layers @ 1080p) | > 30 FPS preview |

---

## Security Considerations

See [SECURITY_ASSESSMENT.md](SECURITY_ASSESSMENT.md) for detailed threat model.

Critical areas:
- Template/project file validation
- LLM scope boundaries
- Path traversal prevention
- Expression sandbox (SES/Compartment)

---

## Release Criteria

### Alpha (Current)
- Core compositor functional
- Basic export working
- AI agent integrated
- Tests passing

### Beta
- All export formats validated
- Performance optimized
- Documentation complete
- Security Phase 1 implemented

### v1.0
- Production security hardening complete
- Edge cases handled
- Community feedback incorporated
- Tutorial content available

---

## Documentation Requirements

| Document | Purpose |
|----------|---------|
| README.md | Installation and quick start |
| INSTALL.md | Detailed installation guide |
| CHANGELOG.md | Version history |
| docs/ARCHITECTURE.md | System architecture |
| docs/SERVICE_API_REFERENCE.md | API reference |
| SECURITY_ASSESSMENT.md | Security analysis |

---

## Appendix: Frame Count Formula

AI video models require frame counts following `frames = (seconds x 16) + 1`:

| Duration | Frames |
|----------|--------|
| 1 second | 17 |
| 2 seconds | 33 |
| 3 seconds | 49 |
| 5 seconds | 81 (default) |
| 10 seconds | 161 |
