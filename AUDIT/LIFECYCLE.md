# Lifecycle Stability Tracker

## Stabilized & Frozen

- **compositor/ui/src/main.ts**
  Explicit mount/unmount, bridge teardown, no auto-mount

- **web/js/extension.js**
  Idempotent sidebar render, guarded listeners, module-based mount/unmount

## In Lifecycle Review

*(none)*

## Rules

- Files listed under "Stabilized & Frozen" must not be modified unless lifecycle invariants are explicitly revisited
- Lifecycle Review files must be stabilized before feature work continues
