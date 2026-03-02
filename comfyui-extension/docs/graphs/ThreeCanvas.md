# ThreeCanvas.vue Dependency Analysis

> Generated: 2026-01-10
> Verified via symbol usage

## File Stats
- **Lines:** 2,197
- **Location:** `ui/src/components/canvas/ThreeCanvas.vue`
- **Role:** Main viewport canvas - renders layers via Three.js/WebGL

---

## IMPORTS (What it depends on) - ~15 dependencies

### External
| Import | From |
|--------|------|
| `THREE` (namespace) | `three` |

### Vue
| Import | From |
|--------|------|
| Reactivity APIs | `vue` |

### Engine
| Import | From |
|--------|------|
| `LatticeEngine`, `LatticeEngineConfig`, `PerformanceStats` | `@/engine` |
| `LayerTransformUpdate` | `@/engine/LatticeEngine` |

### Services
| Import | From |
|--------|------|
| `markLayerDirty` | `@/services/layerEvaluationCache` |

### Stores
| Import | From |
|--------|------|
| `useCompositorStore` | `@/stores/compositorStore` |
| `useSelectionStore` | `@/stores/selectionStore` |

### Types
| Import | From |
|--------|------|
| `ControlPoint`, `Layer` | `@/types/project` |

### Components
| Import | From |
|--------|------|
| `SplineEditor` | `./SplineEditor.vue` |

---

## DEPENDENTS (What imports it) - 10 files (VERIFIED)

**Blast radius: 10 files - MEDIUM**

> Verified 2026-01-10 via: `grep -r "ThreeCanvas" | grep -v __tests__`

| File | Purpose |
|------|---------|
| `components/canvas/ThreeCanvas.vue` | Self |
| `components/dialogs/PathSuggestionDialog.vue` | Preview canvas |
| `components/layout/CenterViewport.vue` | Viewport container |
| `components/layout/WorkspaceLayout.vue` | Main layout |
| `components/panels/ExportPanel.vue` | Export preview |
| `composables/useAssetHandlers.ts` | Asset drop handling |
| `composables/useViewportControls.ts` | Zoom/pan controls |
| `composables/useViewportGuides.ts` | Guide rendering |
| `engine/core/CameraController.ts` | Camera sync |
| `engine/LatticeEngine.ts` | Engine reference |

---

## Component Responsibilities

ThreeCanvas is the **main viewport** handling:

1. **Three.js Scene Setup** (~300 lines)
   - WebGL renderer
   - Scene graph
   - Camera management

2. **Layer Rendering** (~400 lines)
   - Render loop
   - Layer visibility
   - Blend modes

3. **User Interaction** (~500 lines)
   - Mouse events (click, drag, wheel)
   - Selection handling
   - Transform gizmos

4. **Coordinate Systems** (~200 lines)
   - Screen to scene conversion
   - Viewport transform
   - 2D/3D coordinate mapping

5. **Performance** (~200 lines)
   - Frame timing
   - Stats collection
   - Quality settings

6. **Tool Integration** (~300 lines)
   - Selection tool
   - Pan/zoom
   - Shape drawing
   - Spline editing

---

## Dependency Graph

```
┌─────────────────────────────────────────────────────────────┐
│                     ThreeCanvas.vue                          │
│                      (2,197 lines)                          │
├─────────────────────────────────────────────────────────────┤
│  IMPORTS FROM (~15 dependencies)                            │
│  ├── three                                                  │
│  ├── vue                                                    │
│  ├── @/engine (LatticeEngine)                               │
│  ├── @/services (1)                                         │
│  ├── @/stores (2)                                           │
│  ├── @/types (1)                                            │
│  └── ./SplineEditor.vue                                     │
├─────────────────────────────────────────────────────────────┤
│  IMPORTED BY (10 files) ← MEDIUM BLAST RADIUS               │
│  ├── 3 layout components                                    │
│  ├── 2 dialog/panel components                              │
│  ├── 3 composables                                          │
│  └── 2 engine files                                         │
└─────────────────────────────────────────────────────────────┘
```

---

## Risk Assessment

**Risk Level: MEDIUM**

- 10 files depend on it
- Central to the application (main viewport)
- Complex interactions with engine and stores

### Why This File Is Large

ThreeCanvas is the **heart of the UI** - everything visual happens here:
- All layer rendering
- All user interaction with layers
- All viewport controls
- Coordinate system bridging

### Modularization Strategy

Extract to composables (Vue pattern for logic extraction):

```
composables/
├── useThreeScene.ts        (~300 lines - Three.js setup)
├── useLayerRendering.ts    (~400 lines - render loop)
├── useCanvasInteraction.ts (~500 lines - mouse/touch)
├── useCoordinateSystems.ts (~200 lines - screen↔scene)
├── useCanvasPerformance.ts (~200 lines - stats, quality)
└── useCanvasTools.ts       (~300 lines - tool integration)

components/canvas/
└── ThreeCanvas.vue         (~300 lines - template + composition)
```

**Benefits:**
- Each composable is independently testable
- Logic reusable in other canvas contexts
- Main component becomes thin orchestrator

**Risks:**
- Composables need careful coordination
- Shared state management complexity
- Some tight coupling may be hard to break
