# Project Status Audit

## 1. Core Architecture

### State Management (`compositorStore.ts`)
- **Undo/Redo:** YES - Implemented via `historyStack` and `historyIndex`. `pushHistory()` creates JSON snapshots, `undo()`/`redo()` restore them. Limited to 50 entries.
- **Separated Dimensions:** PARTIAL - `GraphEditorCanvas.vue` manually separates Position X/Y, Scale X/Y for display, but this is display-only. The store does NOT natively support separated dimension keyframes - it stores `{x, y}` objects, and the graph editor just extracts components for viewing.
- **Missing Core State Features:**
  - No clipboard state (copy/paste layers/keyframes)
  - No snapping preferences (snap to keyframes, snap to grid)
  - No ruler/guide system
  - No composition markers in store (only local to TimelinePanel)
  - No layer grouping/pre-compose
  - No expression system

### Layout (`TimelinePanel.vue`)
- **Sidebar Persistent:** YES - Uses split-pane layout with `layoutMode="sidebar"` and `layoutMode="track"` on separate `EnhancedLayerTrack` instances. Sidebar stays visible when switching to graph mode.
- **Scrolling Synchronized:** NO - The sidebar (`.property-tree-sidebar`) and track viewport (`.track-viewport`) have independent `overflow-y: auto` on sidebar only. Track viewport has `overflow: hidden`. There is NO scroll synchronization code - when you scroll the sidebar, the tracks don't scroll with it.

---

## 2. Feature Checklist (vs After Effects)

| Feature | Status | Notes/Bugs |
| :--- | :--- | :--- |
| **Layer Management** | | |
| Create Layers | [x] | Dropdown menu: spline, text, solid, null, camera, light. Working via `store.createLayer()`. |
| Delete Layers | [ ] | `store.deleteLayer()` exists but NO UI button or shortcut to trigger it. |
| Rename Layers | [x] | Double-click layer name in sidebar triggers rename input. Working. |
| Duplicate Layers | [ ] | Not implemented. No `duplicateLayer()` action. |
| Hierarchy (Parenting) | [x] | Parent dropdown in sidebar. `setLayerParent()` works. Circular dependency prevention exists. |
| Layer Reordering | [ ] | `store.moveLayer()` exists but NO drag-drop UI. |
| **Timeline UI** | | |
| Sidebar Rendering | [x] | Now correctly shows layer info, twirl arrows, property names with values. No input bleeding. |
| Track Rendering | [x] | Shows duration bars and keyframe diamonds only. No text elements. |
| Scroll Sync | [ ] | BROKEN - Sidebar and track area scroll independently. |
| Row Height Alignment | [?] | Layer row = 28px, Property row = 24px. Heights match between sidebar/track but untested with many layers. |
| Playhead Sync | [x] | Single playhead in `TimelinePanel.vue` spans entire area. |
| **Properties** | | |
| Expand/Collapse | [x] | Twirl arrows work. `expandedLayerIds` Set syncs sidebar and track expansion. |
| Stopwatch Toggle | [x] | Click stopwatch in sidebar calls `store.setPropertyAnimated()`. |
| Add Keyframe | [x] | Via `store.addKeyframe()`. UI: stopwatch enables animation and adds keyframe. |
| Remove Keyframe | [x] | `store.removeKeyframe()` exists. UI access unclear (no delete button on diamond). |
| Keyframe Editing | [~] | Can click to select. Dragging exists in `PropertyTrack.vue` but `startKeyframeDrag()` only emits select, doesn't actually drag. |
| **Graph Editor** | | |
| Toggle Button | [x] | Graph toggle button in header switches `viewMode`. |
| Value Curves | [x] | `GraphEditorCanvas.vue` draws curves with canvas 2D. Bezier interpolation supported. |
| Speed Curves | [x] | "Speed" mode shows derivative (bell curves). Math implemented. |
| Zoom/Pan | [x] | Mouse wheel + Ctrl for zoom, wheel alone for pan. `zoomLevel` and `scrollOffset` refs. |
| Keyframe Points | [x] | DOM elements for keyframes with drag handlers. |
| Bezier Handles | [~] | Rendered when `interpolation === 'bezier'` but handle dragging may not update store correctly. |
| **Playback** | | |
| Play/Pause | [x] | Space key, button click. `setInterval` based on FPS. |
| Loop Modes | [x] | None, Loop, Ping-pong. Works with work area. |
| Frame Navigation | [x] | Home/End, Page Up/Down, frame input field. |
| Work Area | [x] | Draggable handles on ruler. B/N keys set in/out. |
| **Selection** | | |
| Layer Selection | [x] | Single select works. Multi-select via shift not implemented for layers. |
| Keyframe Selection | [~] | Toggle selection works. Shift-click should add but may replace. |
| Property Selection | [x] | For graph filtering. `selectedPropertyIds` Set. |

---

## 3. Critical Bugs

### Bug #1: No Scroll Synchronization
**Location:** `TimelinePanel.vue` lines 1214-1228
**Problem:** `.property-tree-sidebar` and `.track-viewport` are sibling divs with independent overflow. When you scroll the sidebar to see more layers/properties, the track area stays stationary, causing row misalignment.
**Impact:** Unusable with more than ~10 layers. Users cannot match which track belongs to which layer.

### Bug #2: Keyframe Dragging Does Not Move Keyframes
**Location:** `PropertyTrack.vue` line 123-127
**Problem:** `startKeyframeDrag()` only calls `emit('selectKeyframe')`. It does NOT set up mousemove/mouseup handlers or call `store.moveKeyframe()`. The drag functionality is incomplete.
**Impact:** Users cannot drag keyframes to new positions in keyframe mode.

### Bug #3: No Delete Layer UI
**Location:** `TimelinePanel.vue` (missing)
**Problem:** `store.deleteLayer()` exists but there is no button, context menu, or keyboard shortcut (Delete/Backspace) to trigger it.
**Impact:** Users can create layers but cannot remove them without code.

---

## 4. Missing "Must Have" Features

1. **Delete Layer UI** - No button or shortcut to delete selected layer(s)
2. **Scroll Synchronization** - Left/right panels must scroll together
3. **Keyframe Dragging** - Must be able to drag keyframes to new frame positions
4. **Copy/Paste** - No clipboard for layers or keyframes
5. **Multi-Selection** - Shift-click for multiple layers, box-select for keyframes
6. **Delete Keyframe UI** - No button/shortcut to delete selected keyframes
7. **Keyboard Shortcuts for Timeline** - No J/K/L for shuttle, no arrow keys for frame stepping while focused
8. **Context Menus** - No right-click menus for layers, keyframes, or properties
9. **Value Editing in Graph** - Cannot type numeric values for keyframes in graph editor
10. **Snap to Keyframes** - Playhead/keyframe dragging doesn't snap to existing keyframes

---

**End of Audit.**
