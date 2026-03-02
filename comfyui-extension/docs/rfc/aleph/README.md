# Aleph RFCs

Design decisions and rationale for aleph protocols.

## RFC Index

| RFC | Title | Status |
|-----|-------|--------|
| [001](./aleph-001-standard-nix.md) | Standard Nix | Implemented |
| [002](./aleph-002-lint.md) | Linting | Implemented |
| [003](./aleph-003-prelude.md) | The Prelude | Implemented |
| [004](./aleph-004-typed-unix.md) | Aleph.Script | Implemented |
| [005](./aleph-005-profiles.md) | Nix Profiles | Implemented |
| [006](./aleph-006-safe-bash.md) | Safe Bash | Implemented |
| [007](./aleph-007-formalization.md) | Nix Formalization | Draft |
| [008](./aleph-008-continuity/) | The Continuity Project | Draft |

See also: [Conformance Report](./conformance-report.md)

## RFC Format

Each RFC includes:

1. **Summary** - One paragraph overview
1. **Motivation** - Why this is needed
1. **Design** - How it works
1. **Implementation** - Where to find the code
1. **Drawbacks** - Known limitations
1. **Alternatives** - Other approaches considered

## Enforcement

All aleph protocols are enforced via:
- Cursor rules (`.cursor/rules/004_aleph-001-standard-nix.mdc` through `010_aleph-008-continuity.mdc`)
- Validation scripts (`scripts/validate-file.js`)
- Pre-commit hooks (`.husky/pre-commit`)
- CI pipeline (`.github/workflows/`)

## Quick Reference

- **aleph-001**: Use lisp-case, no `with lib;`, no `rec {`, packages need `meta`, modules need `_class`
- **aleph-002**: Mechanical linting via AST rules (ALEPH-E001 through ALEPH-E010)
- **aleph-003**: Use prelude functions (map, filter, fold, maybe, either), platform/stdenv/toolchain
- **aleph-004**: Write Haskell scripts with `import Aleph.Script`, use typed tool wrappers
- **aleph-005**: Use nix-dev, nix-ci, nix-prod profiles for different contexts
- **aleph-006**: Only `exec "$@"` allowed in bash, no logic/variables/conditionals
- **aleph-007**: CA derivations always-on, typed package DSL, isospin builder
- **aleph-008**: Dhall build language, typed toolchains, R2 storage, DICE builds
