# Contributing

## Development Setup

### Prerequisites

- Nix (with flakes enabled)
- Git

### Getting Started

```bash
# Clone and enter dev environment
git clone <repo-url>
cd standalone-edition
nix develop

# Verify builds work
cabal build                              # Haskell
cd lattice-core/purescript && spago build # PureScript
cd lattice-core/lean && lake build        # Lean
```

## Code Standards

### No Stubs

Every piece of code must be complete. Forbidden:

- `TODO` comments
- `FIXME` comments
- Placeholder functions
- `undefined`, `error "not implemented"`
- Empty implementations

### Type Safety

- **Haskell:** Use `Either Text` for errors, never partial functions
- **PureScript:** Use `Maybe`, `Either`, explicit error types
- **Lean:** All types must have roundtrip proofs

### Determinism

For reproducibility:

- UUID5 only (no UUID4/random)
- Seeded RNG only
- No `IO` randomness without explicit seed parameter

## Pull Request Process

1. Create a branch from `main`
2. Make your changes
3. Ensure all builds pass:
   ```bash
   cabal build
   cd lattice-core/purescript && spago build
   cd lattice-core/lean && lake build
   ```
4. Submit PR with clear description
5. Address review feedback

## Project Structure

See [ARCHITECTURE.md](./ARCHITECTURE.md) for detailed structure.

## Questions?

Open an issue for questions or clarification.
