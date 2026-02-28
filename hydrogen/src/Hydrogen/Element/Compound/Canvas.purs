-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // compound // canvas
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas — Infinite pannable/zoomable surface compound component.
-- |
-- | ## Submodules
-- |
-- | Import the specific submodules you need:
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Canvas.Types (CanvasObject, CanvasObjectId, CanvasTool)
-- | import Hydrogen.Element.Compound.Canvas.State (CanvasState, initialCanvasState, addObject)
-- | import Hydrogen.Element.Compound.Canvas.Render (canvas, canvasWithConfig, CanvasMsg)
-- | import Hydrogen.Element.Compound.Canvas.Selection (hitTestPoint, LassoPath)
-- | import Hydrogen.Element.Compound.Canvas.Transform (moveObject, scaleObject)
-- | import Hydrogen.Element.Compound.Canvas.Grid (GridSpacing, gridSpacing)
-- | import Hydrogen.Element.Compound.Canvas.Grid3D (Grid3DConfig, WorldPlane)
-- | ```
-- |
-- | ## Module Structure
-- |
-- | - **Types**: Core types (CanvasObject, GridConfig, SelectionState, etc.)
-- | - **State**: State management (viewport, selection, history, objects)
-- | - **Render**: Pure render function (CanvasState -> Element CanvasMsg)
-- | - **Selection**: Hit testing, marquee, lasso, handles
-- | - **Transform**: Object transforms (move, scale, rotate)
-- | - **Grid**: 2D grid generation and snap
-- | - **Grid3D**: 3D grid for motion graphics / VFX

module Hydrogen.Element.Compound.Canvas
  ( module Hydrogen.Element.Compound.Canvas
  ) where
