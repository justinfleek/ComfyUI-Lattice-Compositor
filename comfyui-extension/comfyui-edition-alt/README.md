# Lattice Compositor - ComfyUI Edition

A motion graphics compositor built as a ComfyUI extension.

## Stack

- **Frontend:** Vue 3 + TypeScript + Pinia
- **Backend:** Python + ComfyUI
- **Rendering:** Three.js
- **Build:** Vite + npm

## Quick Start

### Prerequisites

- Node.js 20+
- Python 3.10+
- ComfyUI installed

### Installation

```bash
cd ComfyUI/custom_nodes
git clone https://github.com/weyl-ai/lattice-compositor.git
cd lattice-compositor
pip install -r requirements.txt
```

Start ComfyUI. Done.

## Project Structure

```
comfyui-edition/
├── ui/                     # Vue 3 frontend
│   ├── src/
│   │   ├── components/     # Vue components
│   │   ├── stores/         # Pinia stores
│   │   ├── services/       # Business logic
│   │   ├── engine/         # Three.js rendering
│   │   ├── types/          # TypeScript types
│   │   └── utils/          # Utility functions
│   ├── e2e/                # End-to-end tests
│   └── package.json
├── src/                    # Python backend
│   └── nodes/              # ComfyUI nodes
├── web/                    # Built frontend output
├── main.py                 # Entry point
└── requirements.txt        # Python dependencies
```

## Development

### Frontend Development

```bash
cd ui

# Development server with hot reload
npm run dev

# Type checking
npm run typecheck

# Linting
npm run lint

# Testing
npm run test
```

### Building

```bash
cd ui
npm run build
```

Output goes to `web/` directory, which ComfyUI serves.

## Architecture

See [docs/ARCHITECTURE.md](./docs/ARCHITECTURE.md) for detailed system design.

### Key Components

- **WorkspaceLayout.vue** - Main application layout
- **TimelinePanel.vue** - Timeline and keyframe editing
- **ThreeCanvas.vue** - WebGL viewport
- **PropertiesPanel.vue** - Layer property editing
- **EffectsPanel.vue** - Effect stack management

### State Management

- **compositorStore** - Main project state
- **playbackStore** - Timeline playback
- **historyStore** - Undo/redo
- **audioStore** - Audio analysis
- **assetStore** - Asset management

## License

MIT
