# Build Fix Required

## Issues Found

1. **Extension Path Detection** ✅ FIXED
   - Updated `web/js/extension.js` to use `ComfyUI-Lattice-Compositor` as fallback
   - Added better path detection logic

2. **Missing Vue Exports** ❌ NEEDS REBUILD
   - `lattice-ui-vendor.js` imports `Fragment` and other Vue exports from `lattice-vue-vendor.js`
   - These exports are defined in `lattice-vue-vendor.js` but not exported
   - Root cause: Vite build is too aggressively tree-shaking Vue exports

## Solution

The UI needs to be rebuilt with the updated `vite.config.ts` that:
- Preserves Vue side effects to ensure all exports are available
- Ensures Vue chunk is loaded before PrimeVue chunk

## Rebuild Command

```bash
cd ui
npm run build
```

If you get permission errors (`EPERM`), try:
1. Close any processes that might be locking files (antivirus, file explorers)
2. Run PowerShell as Administrator
3. Or temporarily disable antivirus real-time scanning

## Expected Output

After rebuild, `lattice-vue-vendor.js` should export:
- `Fragment` (as `F`)
- `computed` (as `c`)
- `createBaseVNode` (as `t`)
- `createCommentVNode` (as `C`)
- `createElementBlock` (as `a`)
- `createTextVNode` (as `v`)
- `createVNode` (as `E`)
- `getCurrentInstance` (as `j`)
- `h` (as `l`)
- `inject` (as `i`)
- `mergeProps` (as `s`)
- `nextTick` (as `k`)
- `normalizeClass` (as `D`)
- `normalizeStyle` (as `n`)
- `onBeforeUnmount` (as `b`)
- `provide` (as `p`)
- `readonly` (as `m`)
- `ref` (as `r`)
- `renderSlot` (as `e`)
- `resolveDirective` (as `z`)
- `resolveDynamicComponent` (as `h`)
- `Teleport` (as `T`)
- `Transition` (as `G`)
- `toDisplayString` (as `x`)
- `unref` (as `u`)
- `useId` (as `q`)
- `useSlots` (as `f`)
- `watch` (as `w`)
- `withCtx` (as `B`)
- `withDirectives` (as `A`)
- And all other Vue core exports that PrimeVue needs

## Temporary Workaround

If rebuild is not possible immediately, you can manually patch `web/js/lattice-vue-vendor.js` by updating the export statement at the end (line 6345) to include all missing exports. However, this is error-prone and a rebuild is strongly recommended.
