-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // element // compound // canvas // transform
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Transform — Object transformation operations.
-- |
-- | ## Purpose
-- |
-- | This module provides operations for transforming objects ON the canvas:
-- | - Moving objects (translate)
-- | - Scaling objects from anchor points
-- | - Rotating objects around pivot
-- | - Transforming selections as a group
-- |
-- | **Note:** Viewport transforms (pan/zoom of the canvas itself) are handled
-- | by Schema.Graph.Viewport and Canvas.State. This module handles individual
-- | object transforms.
-- |
-- | ## Coordinate Spaces
-- |
-- | - **Screen space**: Pixel coordinates on the display
-- | - **Canvas space**: Logical coordinates in the infinite canvas
-- | - **Object space**: Local coordinates relative to object origin
-- |
-- | Transforms apply in object space, then converted to canvas space.
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Transform (Transform2D, Scale, Rotate, Translate)
-- | - Canvas.Types (CanvasObject, CanvasObjectId)
-- | - Canvas.State (CanvasState, updateObject)

module Hydrogen.Element.Compound.Canvas.Transform
  ( -- * Object Movement
    moveObject
  , moveObjectBy
  , moveObjectTo
  , moveObjects
  , moveSelection
  
  -- * Object Scaling
  , scaleObject
  , scaleObjectUniform
  , scaleObjectFromAnchor
  , scaleSelection
  
  -- * Object Rotation
  , rotateObject
  , rotateObjectAround
  , rotateSelection
  
  -- * Object Bounds
  , setObjectBounds
  , resizeObject
  , resizeObjectFromCorner
  
  -- * Anchor/Pivot Points
  , AnchorPoint(..)
  , anchorPosition
  , objectAnchor
  
  -- * Transform Composition
  , applyTransform
  , resetTransform
  , combineTransforms
  
  -- * Coordinate Conversion
  , screenToCanvas
  , canvasToScreen
  , screenToObject
  , objectToScreen
  
  -- * Comparison
  , objectsOverlap
  , pointInObject
  , anchorPointsEqual
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  , (&&)
  , (||)
  , (>)
  , (<)
  , (>=)
  , (<=)
  , (+)
  , (-)
  , (*)
  , (/)
  , ($)
  , not
  , max
  , min
  )

import Data.Array (filter, head)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Transform as T
import Hydrogen.Schema.Geometry.Angle (Degrees, degrees, unwrapDegrees)
import Hydrogen.Schema.Graph.Viewport as VP

import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Element.Compound.Canvas.State (CanvasState, updateObject, getObjects)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // anchor point
-- ═════════════════════════════════════════════════════════════════════════════

-- | Anchor point for transformations.
-- |
-- | Determines the fixed point when scaling/rotating.
data AnchorPoint
  = AnchorCenter       -- ^ Center of bounds
  | AnchorTopLeft      -- ^ Top-left corner
  | AnchorTop          -- ^ Top center
  | AnchorTopRight     -- ^ Top-right corner
  | AnchorLeft         -- ^ Left center
  | AnchorRight        -- ^ Right center
  | AnchorBottomLeft   -- ^ Bottom-left corner
  | AnchorBottom       -- ^ Bottom center
  | AnchorBottomRight  -- ^ Bottom-right corner
  | AnchorCustom Number Number  -- ^ Custom position (0-1 normalized)

derive instance eqAnchorPoint :: Eq AnchorPoint

instance showAnchorPoint :: Show AnchorPoint where
  show AnchorCenter = "center"
  show AnchorTopLeft = "top-left"
  show AnchorTop = "top"
  show AnchorTopRight = "top-right"
  show AnchorLeft = "left"
  show AnchorRight = "right"
  show AnchorBottomLeft = "bottom-left"
  show AnchorBottom = "bottom"
  show AnchorBottomRight = "bottom-right"
  show (AnchorCustom x y) = "custom(" <> show x <> "," <> show y <> ")"

-- | Get normalized position (0-1) for anchor point.
anchorPosition :: AnchorPoint -> { x :: Number, y :: Number }
anchorPosition AnchorCenter = { x: 0.5, y: 0.5 }
anchorPosition AnchorTopLeft = { x: 0.0, y: 0.0 }
anchorPosition AnchorTop = { x: 0.5, y: 0.0 }
anchorPosition AnchorTopRight = { x: 1.0, y: 0.0 }
anchorPosition AnchorLeft = { x: 0.0, y: 0.5 }
anchorPosition AnchorRight = { x: 1.0, y: 0.5 }
anchorPosition AnchorBottomLeft = { x: 0.0, y: 1.0 }
anchorPosition AnchorBottom = { x: 0.5, y: 1.0 }
anchorPosition AnchorBottomRight = { x: 1.0, y: 1.0 }
anchorPosition (AnchorCustom x y) = { x, y }

-- | Get anchor position in canvas coordinates for an object.
objectAnchor :: AnchorPoint -> Types.CanvasObject -> { x :: Number, y :: Number }
objectAnchor anchor obj =
  let 
    bounds = Types.objectBounds obj
    norm = anchorPosition anchor
  in 
    { x: bounds.x + bounds.width * norm.x
    , y: bounds.y + bounds.height * norm.y
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // object movement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Move an object by a delta.
moveObject :: Types.CanvasObjectId -> Number -> Number -> CanvasState -> CanvasState
moveObject objId dx dy state =
  updateObject objId (\obj -> 
    let bounds = obj.bounds
    in obj { bounds = bounds { x = bounds.x + dx, y = bounds.y + dy } }
  ) state

-- | Move object by delta (alias for moveObject).
moveObjectBy :: Types.CanvasObjectId -> { dx :: Number, dy :: Number } -> CanvasState -> CanvasState
moveObjectBy objId delta state = moveObject objId delta.dx delta.dy state

-- | Move object to absolute position.
moveObjectTo :: Types.CanvasObjectId -> { x :: Number, y :: Number } -> CanvasState -> CanvasState
moveObjectTo objId pos state =
  updateObject objId (\obj -> 
    obj { bounds = obj.bounds { x = pos.x, y = pos.y } }
  ) state

-- | Move multiple objects by the same delta.
moveObjects :: Array Types.CanvasObjectId -> Number -> Number -> CanvasState -> CanvasState
moveObjects objIds dx dy state =
  foldObjects (\s objId -> moveObject objId dx dy s) state objIds

-- | Move all selected objects by delta.
moveSelection :: Number -> Number -> CanvasState -> CanvasState
moveSelection dx dy state =
  let selectedIds = getSelectedIds state
  in moveObjects selectedIds dx dy state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // object scaling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale an object by factors.
-- |
-- | Scales around the object's center by default.
scaleObject :: Types.CanvasObjectId -> Number -> Number -> CanvasState -> CanvasState
scaleObject objId sx sy state = scaleObjectFromAnchor objId sx sy AnchorCenter state

-- | Scale object uniformly (same factor for X and Y).
scaleObjectUniform :: Types.CanvasObjectId -> Number -> CanvasState -> CanvasState
scaleObjectUniform objId s state = scaleObject objId s s state

-- | Scale object from a specific anchor point.
-- |
-- | The anchor point remains fixed while other parts scale away from it.
scaleObjectFromAnchor :: Types.CanvasObjectId -> Number -> Number -> AnchorPoint -> CanvasState -> CanvasState
scaleObjectFromAnchor objId sx sy anchor state =
  updateObject objId (\obj -> 
    let 
      bounds = obj.bounds
      anchorPos = objectAnchor anchor obj
      -- New dimensions
      newWidth = bounds.width * sx
      newHeight = bounds.height * sy
      -- Adjust position so anchor stays fixed
      anchorNorm = anchorPosition anchor
      newX = anchorPos.x - newWidth * anchorNorm.x
      newY = anchorPos.y - newHeight * anchorNorm.y
    in obj { bounds = { x: newX, y: newY, width: newWidth, height: newHeight } }
  ) state

-- | Scale all selected objects uniformly from selection center.
scaleSelection :: Number -> CanvasState -> CanvasState
scaleSelection s state =
  let selectedIds = getSelectedIds state
  in foldObjects (\st objId -> scaleObjectUniform objId s st) state selectedIds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // object rotation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate an object by degrees.
-- |
-- | Adds rotation to the object's transform.
rotateObject :: Types.CanvasObjectId -> Number -> CanvasState -> CanvasState
rotateObject objId degs state =
  updateObject objId (\obj -> 
    let 
      currentTransform = obj.transform
      currentRotation = T.getRotation $ getTransformRotate currentTransform
      currentDegs = unwrapDegrees currentRotation
      newRotation = T.rotate $ degrees (currentDegs + degs)
      newTransform = T.withRotate newRotation currentTransform
    in obj { transform = newTransform }
  ) state

-- | Rotate object around a specific point in canvas coordinates.
rotateObjectAround :: Types.CanvasObjectId -> Number -> { x :: Number, y :: Number } -> CanvasState -> CanvasState
rotateObjectAround objId degs pivot state =
  updateObject objId (\obj -> 
    let 
      bounds = obj.bounds
      -- Center of object
      cx = bounds.x + bounds.width / 2.0
      cy = bounds.y + bounds.height / 2.0
      -- Rotate center around pivot
      radians = degs * 3.14159265359 / 180.0
      cos' = cosApprox radians
      sin' = sinApprox radians
      dx = cx - pivot.x
      dy = cy - pivot.y
      newCx = pivot.x + dx * cos' - dy * sin'
      newCy = pivot.y + dx * sin' + dy * cos'
      -- Update bounds position
      newX = newCx - bounds.width / 2.0
      newY = newCy - bounds.height / 2.0
      -- Also add rotation to transform
      currentTransform = obj.transform
      currentRotation = T.getRotation $ getTransformRotate currentTransform
      currentDegs = unwrapDegrees currentRotation
      newRotation = T.rotate $ degrees (currentDegs + degs)
      newTransform = T.withRotate newRotation currentTransform
    in obj 
      { bounds = bounds { x = newX, y = newY }
      , transform = newTransform 
      }
  ) state

-- | Rotate all selected objects around selection center.
rotateSelection :: Number -> CanvasState -> CanvasState
rotateSelection degs state =
  case getSelectionCenter state of
    Nothing -> state
    Just center ->
      let selectedIds = getSelectedIds state
      in foldObjects (\st objId -> rotateObjectAround objId degs center st) state selectedIds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // object bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set object bounds directly.
setObjectBounds :: Types.CanvasObjectId -> { x :: Number, y :: Number, width :: Number, height :: Number } -> CanvasState -> CanvasState
setObjectBounds objId newBounds state =
  updateObject objId (\obj -> obj { bounds = newBounds }) state

-- | Resize object by changing width and height.
resizeObject :: Types.CanvasObjectId -> Number -> Number -> CanvasState -> CanvasState
resizeObject objId newWidth newHeight state =
  updateObject objId (\obj -> 
    obj { bounds = obj.bounds { width = newWidth, height = newHeight } }
  ) state

-- | Resize object by dragging a corner/edge.
-- |
-- | The opposite corner/edge stays fixed.
resizeObjectFromCorner :: Types.CanvasObjectId -> AnchorPoint -> Number -> Number -> CanvasState -> CanvasState
resizeObjectFromCorner objId corner newX newY state =
  updateObject objId (\obj -> 
    let 
      bounds = obj.bounds
      fixedAnchor = oppositeAnchor corner
      fixed = objectAnchor fixedAnchor obj
      newBounds = case corner of
        AnchorTopLeft -> 
          { x: newX, y: newY, width: fixed.x - newX, height: fixed.y - newY }
        AnchorTopRight -> 
          { x: bounds.x, y: newY, width: newX - bounds.x, height: fixed.y - newY }
        AnchorBottomLeft -> 
          { x: newX, y: bounds.y, width: fixed.x - newX, height: newY - bounds.y }
        AnchorBottomRight -> 
          { x: bounds.x, y: bounds.y, width: newX - bounds.x, height: newY - bounds.y }
        AnchorTop ->
          { x: bounds.x, y: newY, width: bounds.width, height: fixed.y - newY }
        AnchorBottom ->
          { x: bounds.x, y: bounds.y, width: bounds.width, height: newY - bounds.y }
        AnchorLeft ->
          { x: newX, y: bounds.y, width: fixed.x - newX, height: bounds.height }
        AnchorRight ->
          { x: bounds.x, y: bounds.y, width: newX - bounds.x, height: bounds.height }
        AnchorCenter -> bounds  -- No resize from center
        AnchorCustom _ _ -> bounds  -- Not supported for custom
    in obj { bounds = newBounds }
  ) state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // transform composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply a Transform2D to an object (replaces current transform).
applyTransform :: Types.CanvasObjectId -> T.Transform2D -> CanvasState -> CanvasState
applyTransform objId newTransform state =
  updateObject objId (\obj -> obj { transform = newTransform }) state

-- | Reset object transform to identity.
resetTransform :: Types.CanvasObjectId -> CanvasState -> CanvasState
resetTransform objId state = applyTransform objId T.identityTransform state

-- | Combine two transforms and apply to object.
combineTransforms :: Types.CanvasObjectId -> T.Transform2D -> CanvasState -> CanvasState
combineTransforms objId additionalTransform state =
  updateObject objId (\obj -> 
    obj { transform = T.composeTransform obj.transform additionalTransform }
  ) state

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // coordinate conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert screen coordinates to canvas coordinates.
screenToCanvas :: CanvasState -> { x :: Number, y :: Number } -> { x :: Number, y :: Number }
screenToCanvas state screen =
  let 
    zoom = VP.zoomLevel $ VP.viewportZoomLevel state.viewport
    pan = VP.viewportPan state.viewport
  in
    { x: (screen.x / zoom) + pan.x
    , y: (screen.y / zoom) + pan.y
    }

-- | Convert canvas coordinates to screen coordinates.
canvasToScreen :: CanvasState -> { x :: Number, y :: Number } -> { x :: Number, y :: Number }
canvasToScreen state canvas =
  let 
    zoom = VP.zoomLevel $ VP.viewportZoomLevel state.viewport
    pan = VP.viewportPan state.viewport
  in
    { x: (canvas.x - pan.x) * zoom
    , y: (canvas.y - pan.y) * zoom
    }

-- | Convert screen coordinates to object-local coordinates.
screenToObject :: CanvasState -> Types.CanvasObject -> { x :: Number, y :: Number } -> { x :: Number, y :: Number }
screenToObject state obj screen =
  let 
    canvas = screenToCanvas state screen
    bounds = Types.objectBounds obj
  in
    { x: canvas.x - bounds.x
    , y: canvas.y - bounds.y
    }

-- | Convert object-local coordinates to screen coordinates.
objectToScreen :: CanvasState -> Types.CanvasObject -> { x :: Number, y :: Number } -> { x :: Number, y :: Number }
objectToScreen state obj local =
  let 
    bounds = Types.objectBounds obj
    canvas = { x: local.x + bounds.x, y: local.y + bounds.y }
  in canvasToScreen state canvas

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get opposite anchor (for resize operations).
oppositeAnchor :: AnchorPoint -> AnchorPoint
oppositeAnchor AnchorTopLeft = AnchorBottomRight
oppositeAnchor AnchorTopRight = AnchorBottomLeft
oppositeAnchor AnchorBottomLeft = AnchorTopRight
oppositeAnchor AnchorBottomRight = AnchorTopLeft
oppositeAnchor AnchorTop = AnchorBottom
oppositeAnchor AnchorBottom = AnchorTop
oppositeAnchor AnchorLeft = AnchorRight
oppositeAnchor AnchorRight = AnchorLeft
oppositeAnchor AnchorCenter = AnchorCenter
oppositeAnchor (AnchorCustom x y) = AnchorCustom (1.0 - x) (1.0 - y)

-- | Get selected object IDs from canvas state.
getSelectedIds :: CanvasState -> Array Types.CanvasObjectId
getSelectedIds state = state.selection.selectedIds

-- | Get center of selection bounds.
getSelectionCenter :: CanvasState -> Maybe { x :: Number, y :: Number }
getSelectionCenter state =
  let 
    selectedObjects = filter (\obj -> isSelected (Types.objectId obj) state) (getObjects state)
  in case selectedObjects of
    [] -> Nothing
    objs -> 
      let 
        bounds = calculateBounds objs
      in Just { x: bounds.x + bounds.width / 2.0, y: bounds.y + bounds.height / 2.0 }

-- | Check if object is selected.
isSelected :: Types.CanvasObjectId -> CanvasState -> Boolean
isSelected objId state = Types.isSelected objId state.selection

-- | Calculate combined bounds of multiple objects.
calculateBounds :: Array Types.CanvasObject -> { x :: Number, y :: Number, width :: Number, height :: Number }
calculateBounds objs =
  case objs of
    [] -> { x: 0.0, y: 0.0, width: 0.0, height: 0.0 }
    _ -> 
      let 
        getBounds = Types.objectBounds
        minX = foldMin (\obj -> (getBounds obj).x) objs
        minY = foldMin (\obj -> (getBounds obj).y) objs
        maxX = foldMax (\obj -> (getBounds obj).x + (getBounds obj).width) objs
        maxY = foldMax (\obj -> (getBounds obj).y + (getBounds obj).height) objs
      in { x: minX, y: minY, width: maxX - minX, height: maxY - minY }

-- | Fold over array to apply function to state for each element.
foldObjects :: forall a. (CanvasState -> a -> CanvasState) -> CanvasState -> Array a -> CanvasState
foldObjects f initialState arr = foldl f initialState arr

-- | Extract rotation from Transform2D.
-- |
-- | Returns the rotation if set, or no rotation (0 degrees).
-- | Note: This accesses the internal structure of Transform2D.
getTransformRotate :: T.Transform2D -> T.Rotate
getTransformRotate (T.Transform2D t) = 
  case t.rotate of
    Just r -> r
    Nothing -> T.rotateNone

-- | Get rotation angle in degrees from a transform.
getRotationDegrees :: T.Transform2D -> Degrees
getRotationDegrees transform = T.getRotation $ getTransformRotate transform

-- | Approximate cosine using Taylor series.
-- |
-- | Good accuracy for small angles (within 2π).
-- | cos(x) ≈ 1 - x²/2! + x⁴/4! - x⁶/6!
cosApprox :: Number -> Number
cosApprox x = 
  let x2 = x * x
      x4 = x2 * x2
      x6 = x4 * x2
  in 1.0 - (x2 / 2.0) + (x4 / 24.0) - (x6 / 720.0)

-- | Approximate sine using Taylor series.
-- |
-- | Good accuracy for small angles (within 2π).
-- | sin(x) ≈ x - x³/3! + x⁵/5! - x⁷/7!
sinApprox :: Number -> Number
sinApprox x = 
  let x2 = x * x
      x3 = x2 * x
      x5 = x3 * x2
      x7 = x5 * x2
  in x - (x3 / 6.0) + (x5 / 120.0) - (x7 / 5040.0)

-- | Fold to find minimum value.
foldMin :: forall a. (a -> Number) -> Array a -> Number
foldMin f arr = case head arr of
  Nothing -> 0.0
  Just first -> foldl (\acc x -> min acc (f x)) (f first) arr

-- | Fold to find maximum value.
foldMax :: forall a. (a -> Number) -> Array a -> Number
foldMax f arr = case head arr of
  Nothing -> 0.0
  Just first -> foldl (\acc x -> max acc (f x)) (f first) arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two objects' bounds overlap.
objectsOverlap :: Types.CanvasObject -> Types.CanvasObject -> Boolean
objectsOverlap obj1 obj2 =
  let 
    b1 = Types.objectBounds obj1
    b2 = Types.objectBounds obj2
  in boundsOverlap b1 b2

-- | Check if two bounds overlap.
-- |
-- | Two bounds overlap if neither is completely to the left, right,
-- | above, or below the other.
boundsOverlap :: { x :: Number, y :: Number, width :: Number, height :: Number } 
              -> { x :: Number, y :: Number, width :: Number, height :: Number } 
              -> Boolean
boundsOverlap b1 b2 =
  let
    -- Right edge of b1 is past left edge of b2
    horizontalOverlap = b1.x + b1.width > b2.x && b2.x + b2.width > b1.x
    -- Bottom edge of b1 is past top edge of b2
    verticalOverlap = b1.y + b1.height > b2.y && b2.y + b2.height > b1.y
  in horizontalOverlap && verticalOverlap

-- | Check if a point is inside an object's bounds.
pointInObject :: { x :: Number, y :: Number } -> Types.CanvasObject -> Boolean
pointInObject point obj =
  let bounds = Types.objectBounds obj
  in point.x >= bounds.x 
    && point.x <= bounds.x + bounds.width
    && point.y >= bounds.y
    && point.y <= bounds.y + bounds.height

-- | Check if two anchor points are equal.
anchorPointsEqual :: AnchorPoint -> AnchorPoint -> Boolean
anchorPointsEqual AnchorCenter AnchorCenter = true
anchorPointsEqual AnchorTopLeft AnchorTopLeft = true
anchorPointsEqual AnchorTop AnchorTop = true
anchorPointsEqual AnchorTopRight AnchorTopRight = true
anchorPointsEqual AnchorLeft AnchorLeft = true
anchorPointsEqual AnchorRight AnchorRight = true
anchorPointsEqual AnchorBottomLeft AnchorBottomLeft = true
anchorPointsEqual AnchorBottom AnchorBottom = true
anchorPointsEqual AnchorBottomRight AnchorBottomRight = true
anchorPointsEqual (AnchorCustom x1 y1) (AnchorCustom x2 y2) = x1 == x2 && y1 == y2
anchorPointsEqual _ _ = false
