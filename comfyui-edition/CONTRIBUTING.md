# Contributing

## Development Setup

### Prerequisites

- Node.js 20+
- Python 3.10+
- ComfyUI

### Getting Started

```bash
cd comfyui-edition

# Install dependencies
pip install -r requirements.txt
cd ui && npm install

# Start development server
npm run dev
```

## Code Standards

### TypeScript

- Strict mode enabled
- No `any` types without justification
- Explicit return types on functions

### Vue

- Composition API with `<script setup>`
- Props and emits fully typed
- Components in PascalCase

### Python

- Type hints required
- Black formatting
- Ruff linting

## Testing

```bash
cd ui

# Unit tests
npm run test

# E2E tests
npm run test:e2e

# Type checking
npm run typecheck
```

## Pull Request Process

1. Create a branch from `main`
2. Make your changes
3. Ensure tests pass
4. Run linting: `npm run lint`
5. Submit PR with clear description

## Questions?

Open an issue for questions or clarification.
