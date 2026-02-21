# Lattice UI Reference

## lattice-ui-reference.png

Reference screenshot of the Lattice Compositor UI showing the core layout:

### Layout Structure
- **Left Sidebar**: Project panel (Compositions tree, Footage, Solids)
- **Top Toolbar**: Tools, transport controls, timecode display
- **Center Viewport**: Canvas with zoom controls (will become dual-viewport: 3D interactive left, orthographic render right)
- **Bottom**: Timeline with layer controls, playhead, frame ruler
- **Right Sidebar**: Properties panel, AI Tools panel

### Target Architecture
The center viewport will be split:
1. **Left**: Interactive 3D viewport (Cinema 4D-style) for scene manipulation
2. **Right**: Orthographic composition render (flat scene camera view)

### Design Language
- Void background: #0A0A0A
- Surface elevations: #0E0E0E -> #1A1A1A -> #222222
- Accent: Purple/Violet (#8B5CF6)
- Clean typography, subtle borders, collapsed accordion sections

### Context
Lattice is the content creation engine for COMPASS - the autonomous CMO platform. AI agents will write specs and direct layers to render campaign content. The UI serves as both the autonomous rendering pipeline and a manual interface for users who want direct control.

Stack: PureScript Halogen (UI) + Hydrogen Framework (data fetching/state) + WebGPU/Canvas2D (rendering)
