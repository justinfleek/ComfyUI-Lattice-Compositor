# Quick Start

Get up and running with Lattice Compositor ComfyUI Edition.

## Prerequisites

- **ComfyUI** installed and working

## Installation

```bash
cd ComfyUI/custom_nodes
git clone https://github.com/weyl-ai/lattice-compositor.git
cd lattice-compositor
pip install -r requirements.txt
```

Start ComfyUI. The Lattice Compositor UI will be available at:
`http://localhost:8188/extensions/lattice-compositor/`

## Development

For contributors building from source:

```bash
cd ui
npm install && npm run build
```

### Dev Server

```bash
cd ui
npm run dev
```

### Tests

```bash
cd ui
npm run test
```

## Project Layout

```
comfyui-edition/
├── ui/                # Vue 3 frontend
│   ├── src/
│   │   ├── components/
│   │   ├── stores/
│   │   ├── services/
│   │   └── engine/
│   └── package.json
├── src/               # Python backend
│   └── nodes/         # ComfyUI nodes
├── web/               # Built output
└── requirements.txt
```

## Next Steps

- Read [docs/ARCHITECTURE.md](./ARCHITECTURE.md) for system design
- See [CONTRIBUTING.md](../CONTRIBUTING.md) for contribution guidelines
