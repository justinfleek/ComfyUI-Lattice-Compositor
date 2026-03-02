# Session continuation todo – next box / next session

**Purpose:** After migrating to a new machine or starting a new session, use this list to know exactly what exists and what to do. Work through sections in order or by priority. Do not delete this file until migration is complete and the list has been updated for the next session.

**Last updated:** 2025-02-02 (pre-migration commit)

---

## 0. Git: commit and push (do this first on the OLD box)

If you have not yet committed and pushed:

```bash
cd /path/to/ComfyUI-Lattice-Compositor
git add -A
git status   # review
git commit -m "WIP: Haskell build fixes, CompositionSettings field order, FFI AnimationState, parse/layout fixes, session todo for migration"
git push origin main
```

**If `git add -A` fails with permission denied (e.g. `.git/objects/...` or `failed to insert into database`):**

- Run Git from an **elevated** terminal (Run as Administrator on Windows), or
- Fix permissions on the repo: e.g. take ownership of `.git` and contents, or run from a directory where your user can write to `.git/objects`, or
- Exclude the failing path temporarily: e.g. add `NEWSPECS/` to `.gitignore` and run `git add -A` again, then commit and push. You can revert the ignore later and add NEWSPECS in a second commit once permissions are fixed.

On the new box, clone the repo; you do not need to run the above there.

---

## 1. New box setup (one-time)

- [ ] Clone repo: `git clone <repo-url> ComfyUI-Lattice-Compositor && cd ComfyUI-Lattice-Compositor`
- [ ] Install Nix (if using): see `docs/NIX_SETUP.md`
- [ ] Enter dev shell: `nix develop` or `nix-shell` (if flake/shell exists)
- [ ] Python: `scripts/setup-python-env.ps1` or `scripts/setup-python-env.sh` (or `uv`, `pip -r requirements.txt`)
- [ ] Node (for UI): `cd ui && npm ci` or `npm install`
- [ ] Verify Haskell: `cabal build` (see Section 2)

---

## 2. Haskell / Cabal (src/lattice → Haskell, cabal.project, lattice.cabal)

**Status:** Build was failing; fixes were applied (CompositionSettings, FFI, parse errors, Keyframe.Evaluation). **Verify build on new box.**

- [ ] Run `cabal build` (or `cabal build 2>&1 | tee build.log`) and fix any remaining errors.
- [ ] If new GHC version: update `cabal.project` / `lattice.cabal` and fix warnings.
- [ ] Clean build: `cabal clean && cabal build`.
- [ ] Key files to touch if types change:
  - `src/Lattice/Types/Project.hs` – CompositionSettings (12 fields)
  - `src/Lattice/State/Composition.hs` – patterns for CompositionSettings
  - `src/Lattice/FFI/AnimationState.hs` – AnimationState from Maybe Int
  - `src/Lattice/State/Layer/Specialized.hs` – splineDataFill = Just fillColor, isNothing, mapMaybe
  - `src/Lattice/State/Keyframe/Evaluation.hs` – targetLayerId + T.pack for error strings
  - `src/Lattice/State/Keyframe/CRUD.hs` – let-block indentation for newTransform/newLayer
  - `src/Lattice/State/Keyframe/Interpolation.hs` – let/in indentation inside lambda
  - `src/Lattice/State/Layer/Spline.hs`, `Path.hs`, `Clipboard.hs`, `Batch.hs` – map/lambda layout
- [ ] Optional: fix remaining GHC warnings (unused imports, type-defaults, unused matches) across `src/Lattice/**/*.hs`.
- [ ] Run Haskell tests if present: `cabal test` or `tests/` under `test/`.

---

## 3. Python / ComfyUI (src/lattice/nodes, routes, main.py)

- [ ] Ensure ComfyUI is installed/linked per `docs/COMFYUI_LOCAL_SETUP.md`.
- [ ] From repo root: `python main.py` or run ComfyUI with this repo as a custom node path.
- [ ] Verify nodes load: `src/lattice/nodes/` (routes, decomposition, preprocessors, vectorize, etc.).
- [ ] Key entrypoints:
  - `src/lattice/nodes/routes/` – export_routes, render_routes, lattice_api_proxy (large file).
  - `src/lattice/nodes/routes.py` – routing.
- [ ] Run Python tests: `pytest` (or `pytest tests/`, `src/`) – see `pytest.ini`; aim for ≥70% coverage on `src/lattice`.
- [ ] Lint/format: `ruff check`, `ruff format` (see `ruff.toml`).

---

## 4. UI (ui/) – Vue, TypeScript, Vite

- [ ] `cd ui && npm ci` (or `npm install`).
- [ ] `npm run build` and fix any type/lint errors.
- [ ] `npx tsc --noEmit` (strict types; no `any`/escapes per project rules).
- [ ] `npm run test:unit` (or `vitest run`).
- [ ] Key areas:
  - `ui/src/stores/` – keyframeStore, layerStore, compositorStore, etc.
  - `ui/src/engine/` – LatticeEngine, MotionEngine, layers, particles.
  - `ui/src/components/` – timeline, properties, curve-editor, dialogs.
  - `ui/src/services/` – AI, security, export, expressions, etc.
- [ ] Port status: see `docs/TYPESCRIPT_MISSING_PORTS.md`, `docs/PORT_PROGRESS.md` – continue TypeScript → Haskell ports if that’s the plan.
- [ ] E2E: `npm run test:playwright` if configured.

---

## 5. Nix (nix/, flake if present)

- [ ] If using Nix: `nix develop` or `nix-shell` and confirm Haskell/Python/Node tools.
- [ ] `nix flake check` or equivalent if repo has a flake.
- [ ] Overlays: `nix/overlays/` – haskell, lean, scripts, etc.; adjust for new box if needed.
- [ ] Scripts: `nix/scripts/`, `nix/templates/` – ensure any invoked scripts are executable and paths are correct on new box.

---

## 6. Lean (leancomfy/lean/, leancomfy/lean/Lattice, leancomfy/haskell/)

- [ ] Lean4: build Lean project (e.g. `lake build` or project-specific command under `leancomfy/lean/`).
- [ ] Fix any broken proofs or imports in `leancomfy/lean/Lattice/`, `leancomfy/lean/Interpolation/`, etc.
- [ ] Docs: `leandocs/` – update or regenerate if needed.
- [ ] `leancomfy/haskell/` – keep in sync with `src/Lattice` if there is a shared spec.

---

## 7. Docs (docs/)

- [ ] Central index: `docs/INDEX.md` – update links and status when you change behavior or ports.
- [ ] Build/status: `docs/ACTUAL_BUILD_STATUS.md`, `docs/HASKELL_BUILD.md`, `docs/PORT_PROGRESS.md`.
- [ ] API/specs: `docs/LATTICE_API_VS_SPECS.md`, `docs/SERVICE_API_REFERENCE.md`.
- [ ] Architecture: `docs/ARCHITECTURE.md`, `docs/SYSTEM_MAP.md`.
- [ ] Security: `docs/AGENT_SECURITY_FRAMEWORK.md`, `docs/SECURITY_HEADERS.md`, `docs/SECURITY_THREAT_MODEL.md`.
- [ ] DB: `docs/DATABASE_SCHEMA.md`, `docs/DATABASE_SETUP.md`, `docs/DATABASE_MODULAR_ARCHITECTURE.md`.
- [ ] Testing: `docs/TEST_STRATEGY.md`, `docs/TESTING_SETUP_CHECKLIST.md`.
- [ ] Deprecated: `docs/deprecated/` – only update or remove when you’ve fully migrated or retired content.
- [ ] RFCs: `docs/rfc/`, `docs/feature-analysis/` – align with current Nix/Haskell/Lean decisions.

---

## 8. Scripts (scripts/)

- [ ] Haskell build: `scripts/build-haskell.ps1`, `scripts/build-haskell.sh` – run and fix paths for new box.
- [ ] DB: `scripts/init-database.sql`, `scripts/setup-database.sh`, `scripts/init-database.js` – run if DB is required.
- [ ] Env: `scripts/setup-python-env.ps1`, `scripts/setup-python-env.sh`, `scripts/setup-claude-mcp.*`.
- [ ] Validation/checks: `scripts/validate-*.js`, `scripts/check-*.sh`, `scripts/test-*.js` – run and fix failures.
- [ ] ComfyUI: `scripts/start-comfyui*.sh`, `scripts/quick-start-comfyui.sh` – test on new box.

---

## 9. Tests (test/, tests/, ui/src/__tests__)

- [ ] Haskell: `test/` – run via cabal or test runner.
- [ ] JS/Node: `tests/` – run with project test command (e.g. node, jest, or repo-specific).
- [ ] UI unit: `ui/src/__tests__/` – Vitest; fix failing tests after any port or refactor.
- [ ] UI E2E: `ui/src/__tests__/browser/` or Playwright config – run and fix.
- [ ] Python: `tests/` (pytest) – run and keep coverage ≥70% for `src/lattice`.

---

## 10. Web bundle (web/js/)

- [ ] Ensure UI build outputs (e.g. `lattice-compositor.js`, `lattice-vue-vendor.js`, workers) are built and committed or built on deploy.
- [ ] If ComfyUI serves from `web/`, verify paths and that extension/lattice scripts load.

---

## 11. Straylight / protocol (straylight-protocol/, .cursor/rules)

- [ ] If you use Straylight: run any protocol checks (Nix, bash, literate) per `.cursor/rules` and `straylight-protocol/`.
- [ ] `.cursor/rules/*.mdc` – keep in sync with HASKELL_PORT_RULES and zero-escapes; update if you change policy.

---

## 12. Large or critical files (tackle in sections if needed)

- [ ] `src/lattice/nodes/lattice_api_proxy.py` – large; any API changes or new endpoints should be documented and tested.
- [ ] `ui/src/engine/` – many layer and particle files; run tests after edits.
- [ ] `ui/src/stores/keyframeStore/`, `layerStore/` – align with Haskell ports in `src/Lattice/State/`.
- [ ] `src/Lattice/` (Haskell) – 200+ modules; use `cabal build` and test suite as the main regression check.

---

## 13. Optional / cleanup

- [ ] Remove or archive `VerseCrafter-main/` if it was only for reference and is no longer needed.
- [ ] `newfeatures/`, `ComfyUI-EnhancedLinksandNodes-main/` – decide whether to keep or document as external/vendor.
- [ ] `dist-newstyle/` – already in `.gitignore`; do not commit; run `cabal build` on new box.
- [ ] `.github/workflows/` – ensure CI (e.g. haskell-build, cd) runs on push and fix any failing jobs.

---

## 14. Checklist summary (quick pass)

- [ ] Git: pushed latest from old box; cloned on new box.
- [ ] Haskell: `cabal build` succeeds.
- [ ] Python: env set up; `pytest` passes (or known failures documented).
- [ ] UI: `npm run build` and `npx tsc --noEmit` pass; tests run.
- [ ] Nix (if used): `nix develop` works.
- [ ] Lean (if used): Lean build succeeds.
- [ ] Docs: INDEX and build/status docs updated.
- [ ] This file: update “Last updated” and any new sections when you finish a chunk of work.

---

**When you’re done with a section:** tick the boxes, commit with a short message (e.g. “Haskell: fix remaining warnings in State.Layer”), and push. If you hit permission or tooling issues on the new box, note them in this file or in a short migration note so the next session can continue.
