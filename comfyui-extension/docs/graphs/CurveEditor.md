# CurveEditor.vue Dependency Analysis

> Generated: 2026-01-10
> Verified via symbol usage

## File Stats
- **Lines:** 2,006
- **Location:** `ui/src/components/curve-editor/CurveEditor.vue`
- **Role:** Graph editor for keyframe interpolation curves

---

## IMPORTS (What it depends on) - ~8 dependencies

### Vue
| Import | From |
|--------|------|
| `computed`, `onMounted`, `onUnmounted`, `reactive`, `ref`, `watch` | `vue` |

### Services
| Import | From |
|--------|------|
| `EASING_PRESETS` | `@/services/interpolation` |
| `findNearestSnap` | `@/services/timelineSnap` |

### Stores
| Import | From |
|--------|------|
| `useCompositorStore` | `@/stores/compositorStore` |

### Types
| Import | From |
|--------|------|
| `AnimatableProperty`, `Keyframe` | `@/types/project` |

### Components
| Import | From |
|--------|------|
| `CurveEditorHeader` | `./CurveEditorHeader.vue` |
| `CurveMode`, `EasingPreset` types | `./CurveEditorHeader.vue` |

---

## DEPENDENTS (What imports it) - 11 files (VERIFIED)

**Blast radius: 11 files - MEDIUM**

> Verified 2026-01-10 via: `grep -r "CurveEditor" | grep -v CurveEditorCanvas | grep -v useCurveEditor`

| File | Purpose |
|------|---------|
| `components/controls/index.ts` | Barrel export |
| `components/curve-editor/CurveEditorHeader.vue` | Header component |
| `components/curve-editor/CurveEditorPropertyList.vue` | Property list |
| `components/curve-editor/CurveEditor.vue` | Self |
| `components/layout/CenterViewport.vue` | Layout container |
| `components/layout/MenuBar.vue` | Menu toggle |
| `components/layout/WorkspaceLayout.vue` | Main layout |
| `composables/index.ts` | Composables barrel |
| `composables/useKeyboardShortcuts.ts` | Keyboard handling |
| `composables/useMenuActions.ts` | Menu actions |
| `stores/compositorStore.ts` | Visibility state |

---

## Component Structure

The curve editor has a **complex UI** for editing animation curves:

```
┌─────────────────────────────────────────────────────────────┐
│ CurveEditor.vue                                              │
├─────────────────────────────────────────────────────────────┤
│ ┌─────────────────────────────────────────────────────────┐ │
│ │ CurveEditorHeader.vue                                   │ │
│ │ [Mode] [Easing Presets] [Snap] [Zoom Fit]              │ │
│ └─────────────────────────────────────────────────────────┘ │
│ ┌──────────────┬──────────────────────────────────────────┐ │
│ │ PropertyList │ CurveEditorCanvas.vue                    │ │
│ │              │                                          │ │
│ │ ☑ Position X │     •───────•                           │ │
│ │ ☑ Position Y │    /         \                          │ │
│ │ ☐ Rotation   │   •           •────•                    │ │
│ │ ☐ Scale      │                                          │ │
│ │              │ [Grid] [Keyframes] [Handles]            │ │
│ └──────────────┴──────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────┘
```

---

## Why This File Is Large

1. **Curve Rendering** (~400 lines)
   - Bezier curve drawing
   - Multiple properties
   - Grid and axes

2. **Keyframe Interaction** (~500 lines)
   - Selection (single, box, multi)
   - Dragging keyframes
   - Dragging handles

3. **Coordinate Systems** (~200 lines)
   - Time ↔ pixels
   - Value ↔ pixels
   - Zoom and pan

4. **Easing Presets** (~200 lines)
   - Apply preset curves
   - Preview animations

5. **Keyboard Shortcuts** (~200 lines)
   - Delete, copy, paste
   - Nudge, select all

6. **Property Management** (~300 lines)
   - Multi-property display
   - Property filtering
   - Color coding

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                     CurveEditor.vue                          │
│                      (2,006 lines)                          │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (~8 dependencies)                             │
│  ├── vue                                                    │
│  ├── @/services (2)                                         │
│  ├── @/stores (1)                                           │
│  ├── @/types (1)                                            │
│  └── ./CurveEditorHeader.vue                                │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (11 files) ← MEDIUM BLAST RADIUS               │
│  ├── 3 curve-editor sub-components                          │
│  ├── 3 layout components                                    │
│  ├── 2 composables                                          │
│  ├── 1 store                                                │
│  └── 2 barrels                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: MEDIUM**

- 11 files depend on it
- Complex interactive component
- Already has related composables (useCurveEditor*)

### Already Partially Modularized

Related composables exist:
- `useCurveEditorCoords.ts`
- `useCurveEditorDraw.ts`
- `useCurveEditorInteraction.ts`
- `useCurveEditorKeyboard.ts`
- `useCurveEditorView.ts`

Sub-components exist:
- `CurveEditorCanvas.vue` (1,247 lines)
- `CurveEditorHeader.vue`
- `CurveEditorPropertyList.vue`

### Further Modularization

The main `CurveEditor.vue` could be further split:
1. Move more logic to existing composables
2. Extract property panel to separate component
3. Reduce to orchestration layer (~500 lines)

**Note:** This component already follows good patterns - the composables just need more logic extracted to them.
