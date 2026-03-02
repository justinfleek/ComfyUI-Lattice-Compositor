# Haskell Build (Lattice Library)

**Purpose:** Build and test the entire `src/lattice` Haskell tree so new ports don’t pile up technical debt. Every new `.hs` file must be listed in `lattice.cabal` and the full build must pass.

## Who runs the build

**CI runs it.** The workflow `.github/workflows/haskell-build.yml` runs `cabal build` on push/PR when `src/lattice/**/*.hs`, `lattice.cabal`, or `cabal.project` change. No need to run it locally unless you want to.

To run locally from project root: `cabal build` (or `.\scripts\build-haskell.ps1` / `./scripts/build-haskell.sh`).

- **Success:** All 212+ Lattice modules compile; safe to add more ports.
- **Failure:** Fix reported errors (missing deps, type errors, missing modules in cabal) before adding new ports.

## Local build: WSL + mount

The supported local workflow is **WSL** with the repo on the Windows mount (e.g. `cd /mnt/c/Users/.../ComfyUI-Lattice-Compositor`). From that directory:

```bash
nix develop
cabal build
```

GHC, Cabal, and `gh` are provided by the flake dev shell; no separate install needed.

## Prerequisites (if not using Nix in WSL)

- **GHC:** 9.10.x or 9.8.x (GHC2021).
- **Cabal:** 3.8+ (`cabal --version`).
- **Option A:** Install via [ghcup](https://www.haskell.org/ghcup/).
- **Option B:** Use Nix in WSL (see “Local build: WSL + mount” above).

## Layout

| Item | Location |
| ------ | ---------- |
| Library definition | `lattice.cabal` (root) |
| Project config | `cabal.project` (root) |
| Source tree | `src/lattice/` (Database, FFI, Schema, Services, State, Types, Utils) |
| Module count | 212+ (see `exposed-modules` in `lattice.cabal`) |

## Adding a new Haskell module

1. Add the **module name** to `exposed-modules` in `lattice.cabal` (keep alphabetical).
2. Add any new **build-depends** if the module uses packages not already listed.
3. Run `cabal build` and fix any errors.
4. Update `docs/PORT_PROGRESS.md` if this is a TypeScript port.

## Dependencies (current)

- `base`, `aeson`, `bytestring`, `containers`, `cryptohash-sha1`, `hashable`, `regex-tdfa`, `text`, `time`, `unordered-containers`.

If a module fails with “Could not find module …”, add the corresponding package to `build-depends` in `lattice.cabal`.

## Verification

- **Full build:** `cabal build`
- **With stricter warnings:** Already set in `cabal.project` for package `lattice` (`-Wall -Wcompat -Widentities`).

## Relation to porting

- Port progress: `docs/PORT_PROGRESS.md`
- Port rules (zero escapes): `docs/HASKELL_PORT_RULES.md`
- TypeScript files still to port: `docs/TYPESCRIPT_MISSING_PORTS.md`

Keeping the Haskell build green after every new port prevents technical debt and ensures the whole tree stays compilable.
