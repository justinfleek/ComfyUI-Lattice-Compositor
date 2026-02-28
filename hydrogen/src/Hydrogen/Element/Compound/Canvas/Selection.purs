-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // element // compound // canvas // selection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Selection — Hit testing, marquee, lasso, and selection handles.
-- |
-- | ## Design Philosophy
-- |
-- | Professional design tools provide multiple selection methods:
-- |
-- | 1. **Click selection**: Point hit test against objects
-- | 2. **Marquee selection**: Rectangular drag selection
-- | 3. **Lasso selection**: Freeform polygon selection
-- | 4. **Selection handles**: Visual transform affordances
-- |
-- | ## Hit Testing
-- |
-- | Hit testing is hierarchical:
-- | 1. Check handles first (if selection exists)
-- | 2. Check objects from front to back (highest zIndex first)
-- | 3. Return first hit, or Nothing
-- |
-- | ## Selection Handles
-- |
-- | Handles provide direct manipulation:
-- | - **Corner handles**: Scale from corner
-- | - **Edge handles**: Scale from edge
-- | - **Rotation handle**: Rotate around center
-- | - **Center handle**: Move object
-- |
-- | ## Coordinate System
-- |
-- | All hit testing operates in canvas space. Screen coordinates must be
-- | converted using viewport transform before testing.
-- |
-- | ## Dependencies
-- |
-- | - Canvas.Types (CanvasObject, CanvasObjectId, SelectionState)
-- | - Schema.Gestural.Selection (SelectionRect)
-- | - Schema.Geometry.Point (Point2D)

module Hydrogen.Element.Compound.Canvas.Selection
  ( -- * Hit Testing
    HitTestResult(..)
  , hitTestPoint
  , hitTestRect
  , hitTestLasso
  , objectContainsPoint
  , objectIntersectsRect
  
  -- * Lasso Path
  , LassoPath
  , emptyLasso
  , addLassoPoint
  , closeLasso
  , lassoPoints
  , lassoContainsPoint
  , lassoIntersectsRect
  , lassoArea
  
  -- * Selection Handles
  , HandleType(..)
  , SelectionHandle
  , selectionHandle
  , handleType
  , handlePosition
  , handleSize
  , handleContainsPoint
  
  -- * Selection Frame
  , SelectionFrame
  , computeSelectionFrame
  , frameHandles
  , frameBounds
  , frameRotation
  , hitTestHandle
  
  -- * Marquee State
  , MarqueeState
  , startMarquee
  , updateMarquee
  , endMarquee
  , marqueeRect
  , marqueeActive
  
  -- * Selection Operations
  , selectObjectsInRect
  , selectObjectsInLasso
  , selectTopObjectAtPoint
  , selectAllObjectsAtPoint
  
  -- * Handle Operations
  , HandleDragState
  , startHandleDrag
  , updateHandleDrag
  , endHandleDrag
  , computeTransformFromDrag
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , ($)
  , max
  , min
  , negate
  , not
  )

import Data.Array (length, filter, snoc, foldl, sortBy)
import Data.Functor (map)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Ordering (Ordering(GT, LT, EQ))

import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Schema.Gestural.Selection as GSelection

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // hit testing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of a hit test.
data HitTestResult
  = HitObject Types.CanvasObjectId     -- ^ Hit a canvas object
  | HitHandle HandleType               -- ^ Hit a selection handle
  | HitGuide String                    -- ^ Hit a guide (guide ID)
  | HitNothing                         -- ^ No hit

derive instance eqHitTestResult :: Eq HitTestResult

instance showHitTestResult :: Show HitTestResult where
  show (HitObject id) = "HitObject(" <> show id <> ")"
  show (HitHandle h) = "HitHandle(" <> show h <> ")"
  show (HitGuide id) = "HitGuide(" <> id <> ")"
  show HitNothing = "HitNothing"

-- | Hit test a point against objects.
-- |
-- | Tests objects from front to back (highest zIndex first).
-- | Returns the first object whose bounds contain the point.
-- |
-- | Does not test locked or invisible objects unless specified.
hitTestPoint :: { x :: Number, y :: Number }
             -> Array Types.CanvasObject
             -> { testLocked :: Boolean, testInvisible :: Boolean }
             -> Maybe Types.CanvasObjectId
hitTestPoint point objects opts =
  findFirstHit point $ sortByZIndexDesc $ filter (isTestable opts) objects

-- | Hit test a rectangle against objects.
-- |
-- | Returns all objects that intersect with the rectangle.
hitTestRect :: GSelection.SelectionRect
            -> Array Types.CanvasObject
            -> { testLocked :: Boolean, testInvisible :: Boolean }
            -> Array Types.CanvasObjectId
hitTestRect rect objects opts =
  let
    testable = filter (isTestable opts) objects
    hits = filter (objectIntersectsRect rect) testable
  in map Types.objectId hits

-- | Hit test a lasso path against objects.
-- |
-- | Returns all objects that intersect with the lasso polygon.
hitTestLasso :: LassoPath
             -> Array Types.CanvasObject
             -> { testLocked :: Boolean, testInvisible :: Boolean }
             -> Array Types.CanvasObjectId
hitTestLasso lasso objects opts =
  let
    testable = filter (isTestable opts) objects
    hits = filter (objectIntersectsLasso lasso) testable
  in map Types.objectId hits

-- | Check if object contains a point.
objectContainsPoint :: { x :: Number, y :: Number } -> Types.CanvasObject -> Boolean
objectContainsPoint point obj =
  let bounds = Types.objectBounds obj
  in point.x >= bounds.x && point.x <= bounds.x + bounds.width
     && point.y >= bounds.y && point.y <= bounds.y + bounds.height

-- | Check if object intersects a rectangle.
objectIntersectsRect :: GSelection.SelectionRect -> Types.CanvasObject -> Boolean
objectIntersectsRect rect obj =
  let bounds = Types.objectBounds obj
  in rect.x < bounds.x + bounds.width && rect.x + rect.width > bounds.x
     && rect.y < bounds.y + bounds.height && rect.y + rect.height > bounds.y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // lasso path
-- ═════════════════════════════════════════════════════════════════════════════

-- | A freeform lasso selection path.
-- |
-- | The path is a sequence of points forming a polygon.
-- | The polygon is implicitly closed between last and first point.
newtype LassoPath = LassoPath
  { points :: Array { x :: Number, y :: Number }
  , closed :: Boolean
  }

derive instance eqLassoPath :: Eq LassoPath

instance showLassoPath :: Show LassoPath where
  show (LassoPath lp) = 
    "Lasso(" <> show (length lp.points) <> " points, " <>
    (if lp.closed then "closed" else "open") <> ")"

-- | Create an empty lasso path.
emptyLasso :: LassoPath
emptyLasso = LassoPath { points: [], closed: false }

-- | Add a point to the lasso path.
addLassoPoint :: { x :: Number, y :: Number } -> LassoPath -> LassoPath
addLassoPoint point (LassoPath lp) =
  LassoPath lp { points = snoc lp.points point }

-- | Close the lasso path.
closeLasso :: LassoPath -> LassoPath
closeLasso (LassoPath lp) = LassoPath lp { closed = true }

-- | Get lasso points.
lassoPoints :: LassoPath -> Array { x :: Number, y :: Number }
lassoPoints (LassoPath lp) = lp.points

-- | Check if lasso contains a point (point-in-polygon test).
-- |
-- | Uses ray casting algorithm: count intersections with polygon edges.
-- | Odd count = inside, even count = outside.
lassoContainsPoint :: { x :: Number, y :: Number } -> LassoPath -> Boolean
lassoContainsPoint point (LassoPath lp) =
  let pts = lp.points
      n = length pts
  in if n < 3 then false
     else pointInPolygon point pts

-- | Check if lasso intersects a rectangle.
-- |
-- | True if any corner of rect is inside lasso, or if lasso path
-- | crosses through the rectangle.
lassoIntersectsRect :: GSelection.SelectionRect -> LassoPath -> Boolean
lassoIntersectsRect rect lasso =
  let 
    corners = 
      [ { x: rect.x, y: rect.y }
      , { x: rect.x + rect.width, y: rect.y }
      , { x: rect.x + rect.width, y: rect.y + rect.height }
      , { x: rect.x, y: rect.y + rect.height }
      ]
    -- Check if any corner is inside
    anyCornerInside = anyPoint (\c -> lassoContainsPoint c lasso) corners
  in anyCornerInside

-- | Calculate approximate area of lasso polygon.
-- |
-- | Uses shoelace formula for polygon area.
lassoArea :: LassoPath -> Number
lassoArea (LassoPath lp) =
  let pts = lp.points
      n = length pts
  in if n < 3 then 0.0
     else abs' (shoelaceArea pts) / 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // selection handles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of selection handle.
data HandleType
  = HandleTopLeft        -- ^ Top-left corner (scale)
  | HandleTopCenter      -- ^ Top edge center (scale height)
  | HandleTopRight       -- ^ Top-right corner (scale)
  | HandleMiddleLeft     -- ^ Left edge center (scale width)
  | HandleMiddleRight    -- ^ Right edge center (scale width)
  | HandleBottomLeft     -- ^ Bottom-left corner (scale)
  | HandleBottomCenter   -- ^ Bottom edge center (scale height)
  | HandleBottomRight    -- ^ Bottom-right corner (scale)
  | HandleRotation       -- ^ Rotation handle (above selection)
  | HandleCenter         -- ^ Center handle (move)

derive instance eqHandleType :: Eq HandleType
derive instance ordHandleType :: Ord HandleType

instance showHandleType :: Show HandleType where
  show HandleTopLeft = "top-left"
  show HandleTopCenter = "top-center"
  show HandleTopRight = "top-right"
  show HandleMiddleLeft = "middle-left"
  show HandleMiddleRight = "middle-right"
  show HandleBottomLeft = "bottom-left"
  show HandleBottomCenter = "bottom-center"
  show HandleBottomRight = "bottom-right"
  show HandleRotation = "rotation"
  show HandleCenter = "center"

-- | A selection handle.
type SelectionHandle =
  { handleType :: HandleType
  , x :: Number                  -- Handle center X
  , y :: Number                  -- Handle center Y
  , size :: Number               -- Handle size (width/height)
  }

-- | Create a selection handle.
selectionHandle :: HandleType -> Number -> Number -> Number -> SelectionHandle
selectionHandle ht x y size = { handleType: ht, x, y, size }

-- | Get handle type.
handleType :: SelectionHandle -> HandleType
handleType h = h.handleType

-- | Get handle position.
handlePosition :: SelectionHandle -> { x :: Number, y :: Number }
handlePosition h = { x: h.x, y: h.y }

-- | Get handle size.
handleSize :: SelectionHandle -> Number
handleSize h = h.size

-- | Check if handle contains a point.
handleContainsPoint :: { x :: Number, y :: Number } -> SelectionHandle -> Boolean
handleContainsPoint point h =
  let halfSize = h.size / 2.0
  in point.x >= h.x - halfSize && point.x <= h.x + halfSize
     && point.y >= h.y - halfSize && point.y <= h.y + halfSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // selection frame
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual frame around selection with handles.
type SelectionFrame =
  { bounds :: { x :: Number, y :: Number, width :: Number, height :: Number }
  , rotation :: Number           -- Rotation in degrees
  , handles :: Array SelectionHandle
  , handleSize :: Number         -- Size of handles in screen pixels
  }

-- | Compute selection frame from selected objects.
computeSelectionFrame :: Number -> Array Types.CanvasObject -> Maybe SelectionFrame
computeSelectionFrame hSize objects =
  if length objects == 0
    then Nothing
    else 
      let 
        bounds = computeBounds objects
        handles = generateHandles bounds hSize
      in Just
        { bounds
        , rotation: 0.0  -- Combined rotation is complex; default to 0
        , handles
        , handleSize: hSize
        }

-- | Get frame handles.
frameHandles :: SelectionFrame -> Array SelectionHandle
frameHandles frame = frame.handles

-- | Get frame bounds.
frameBounds :: SelectionFrame -> { x :: Number, y :: Number, width :: Number, height :: Number }
frameBounds frame = frame.bounds

-- | Get frame rotation.
frameRotation :: SelectionFrame -> Number
frameRotation frame = frame.rotation

-- | Hit test selection handles.
-- |
-- | Returns the handle hit, or Nothing if no handle was hit.
hitTestHandle :: { x :: Number, y :: Number } -> SelectionFrame -> Maybe HandleType
hitTestHandle point frame =
  case filter (handleContainsPoint point) frame.handles of
    [] -> Nothing
    hs -> case arrayHead hs of
      Nothing -> Nothing
      Just h -> Just (handleType h)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // marquee state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of marquee (rectangular drag) selection.
type MarqueeState =
  { active :: Boolean
  , startPoint :: { x :: Number, y :: Number }
  , currentPoint :: { x :: Number, y :: Number }
  }

-- | Start a marquee selection.
startMarquee :: { x :: Number, y :: Number } -> MarqueeState
startMarquee point =
  { active: true
  , startPoint: point
  , currentPoint: point
  }

-- | Update marquee position.
updateMarquee :: { x :: Number, y :: Number } -> MarqueeState -> MarqueeState
updateMarquee point state = state { currentPoint = point }

-- | End marquee selection.
endMarquee :: MarqueeState -> MarqueeState
endMarquee state = state { active = false }

-- | Get current marquee rectangle.
marqueeRect :: MarqueeState -> GSelection.SelectionRect
marqueeRect state = GSelection.rectFromPoints state.startPoint state.currentPoint

-- | Check if marquee is active.
marqueeActive :: MarqueeState -> Boolean
marqueeActive state = state.active

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // selection operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select all objects within a rectangle.
selectObjectsInRect :: GSelection.SelectionRect
                    -> Array Types.CanvasObject
                    -> Array Types.CanvasObjectId
selectObjectsInRect rect objects =
  hitTestRect rect objects { testLocked: false, testInvisible: false }

-- | Select all objects within a lasso path.
selectObjectsInLasso :: LassoPath
                     -> Array Types.CanvasObject
                     -> Array Types.CanvasObjectId
selectObjectsInLasso lasso objects =
  hitTestLasso lasso objects { testLocked: false, testInvisible: false }

-- | Select the topmost object at a point.
selectTopObjectAtPoint :: { x :: Number, y :: Number }
                       -> Array Types.CanvasObject
                       -> Maybe Types.CanvasObjectId
selectTopObjectAtPoint point objects =
  hitTestPoint point objects { testLocked: false, testInvisible: false }

-- | Select all objects at a point (for stacked objects).
selectAllObjectsAtPoint :: { x :: Number, y :: Number }
                        -> Array Types.CanvasObject
                        -> Array Types.CanvasObjectId
selectAllObjectsAtPoint point objects =
  let 
    testable = filter (isTestable { testLocked: false, testInvisible: false }) objects
    hits = filter (objectContainsPoint point) testable
  in map Types.objectId hits

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // handle operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of a handle drag operation.
type HandleDragState =
  { handle :: HandleType
  , startPoint :: { x :: Number, y :: Number }
  , currentPoint :: { x :: Number, y :: Number }
  , originalBounds :: { x :: Number, y :: Number, width :: Number, height :: Number }
  }

-- | Start dragging a handle.
startHandleDrag :: HandleType
                -> { x :: Number, y :: Number }
                -> { x :: Number, y :: Number, width :: Number, height :: Number }
                -> HandleDragState
startHandleDrag handle point bounds =
  { handle
  , startPoint: point
  , currentPoint: point
  , originalBounds: bounds
  }

-- | Update handle drag position.
updateHandleDrag :: { x :: Number, y :: Number } -> HandleDragState -> HandleDragState
updateHandleDrag point state = state { currentPoint = point }

-- | End handle drag.
endHandleDrag :: HandleDragState -> HandleDragState
endHandleDrag state = state

-- | Compute transform from handle drag.
-- |
-- | Returns new bounds based on which handle was dragged and how far.
computeTransformFromDrag :: HandleDragState 
                         -> { x :: Number, y :: Number, width :: Number, height :: Number }
computeTransformFromDrag state =
  let
    dx = state.currentPoint.x - state.startPoint.x
    dy = state.currentPoint.y - state.startPoint.y
    ob = state.originalBounds
  in case state.handle of
    HandleTopLeft ->
      { x: ob.x + dx
      , y: ob.y + dy
      , width: ob.width - dx
      , height: ob.height - dy
      }
    HandleTopCenter ->
      { x: ob.x
      , y: ob.y + dy
      , width: ob.width
      , height: ob.height - dy
      }
    HandleTopRight ->
      { x: ob.x
      , y: ob.y + dy
      , width: ob.width + dx
      , height: ob.height - dy
      }
    HandleMiddleLeft ->
      { x: ob.x + dx
      , y: ob.y
      , width: ob.width - dx
      , height: ob.height
      }
    HandleMiddleRight ->
      { x: ob.x
      , y: ob.y
      , width: ob.width + dx
      , height: ob.height
      }
    HandleBottomLeft ->
      { x: ob.x + dx
      , y: ob.y
      , width: ob.width - dx
      , height: ob.height + dy
      }
    HandleBottomCenter ->
      { x: ob.x
      , y: ob.y
      , width: ob.width
      , height: ob.height + dy
      }
    HandleBottomRight ->
      { x: ob.x
      , y: ob.y
      , width: ob.width + dx
      , height: ob.height + dy
      }
    HandleRotation ->
      -- Rotation doesn't change bounds directly
      ob
    HandleCenter ->
      -- Move entire selection
      { x: ob.x + dx
      , y: ob.y + dy
      , width: ob.width
      , height: ob.height
      }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if object is testable based on options.
isTestable :: { testLocked :: Boolean, testInvisible :: Boolean } 
           -> Types.CanvasObject 
           -> Boolean
isTestable opts obj =
  let visibleOk = Types.objectVisible obj || opts.testInvisible
      lockedOk = not (Types.objectLocked obj) || opts.testLocked
  in visibleOk && lockedOk

-- | Sort objects by zIndex descending.
sortByZIndexDesc :: Array Types.CanvasObject -> Array Types.CanvasObject
sortByZIndexDesc = sortBy compareZIndexDesc
  where
    compareZIndexDesc a b =
      let za = Types.objectZIndex a
          zb = Types.objectZIndex b
      in if za > zb then LT
         else if za < zb then GT
         else EQ

-- | Find first object that contains point.
findFirstHit :: { x :: Number, y :: Number } 
             -> Array Types.CanvasObject 
             -> Maybe Types.CanvasObjectId
findFirstHit point objects =
  case filter (objectContainsPoint point) objects of
    [] -> Nothing
    hits -> case arrayHead hits of
      Nothing -> Nothing
      Just obj -> Just (Types.objectId obj)

-- | Check if object intersects lasso.
objectIntersectsLasso :: LassoPath -> Types.CanvasObject -> Boolean
objectIntersectsLasso lasso obj =
  let bounds = Types.objectBounds obj
      rect = GSelection.selectionRect bounds.x bounds.y bounds.width bounds.height
  in lassoIntersectsRect rect lasso

-- | Compute combined bounds of objects.
computeBounds :: Array Types.CanvasObject 
              -> { x :: Number, y :: Number, width :: Number, height :: Number }
computeBounds objects =
  let
    initial = { minX: infinity, minY: infinity, maxX: negInfinity, maxY: negInfinity }
    result = foldl accumulateBounds initial objects
  in
    { x: result.minX
    , y: result.minY
    , width: result.maxX - result.minX
    , height: result.maxY - result.minY
    }
  where
    accumulateBounds acc obj =
      let bounds = Types.objectBounds obj
      in
        { minX: min acc.minX bounds.x
        , minY: min acc.minY bounds.y
        , maxX: max acc.maxX (bounds.x + bounds.width)
        , maxY: max acc.maxY (bounds.y + bounds.height)
        }
    
    infinity :: Number
    infinity = 1.0e308
    
    negInfinity :: Number
    negInfinity = negate 1.0e308

-- | Generate handles for a bounding box.
generateHandles :: { x :: Number, y :: Number, width :: Number, height :: Number }
                -> Number
                -> Array SelectionHandle
generateHandles bounds size =
  let
    x = bounds.x
    y = bounds.y
    w = bounds.width
    h = bounds.height
    cx = x + w / 2.0
    cy = y + h / 2.0
    rotationOffset = 20.0  -- Pixels above top center
  in
    [ selectionHandle HandleTopLeft x y size
    , selectionHandle HandleTopCenter cx y size
    , selectionHandle HandleTopRight (x + w) y size
    , selectionHandle HandleMiddleLeft x cy size
    , selectionHandle HandleMiddleRight (x + w) cy size
    , selectionHandle HandleBottomLeft x (y + h) size
    , selectionHandle HandleBottomCenter cx (y + h) size
    , selectionHandle HandleBottomRight (x + w) (y + h) size
    , selectionHandle HandleRotation cx (y - rotationOffset) size
    , selectionHandle HandleCenter cx cy size
    ]

-- | Point-in-polygon test using ray casting.
pointInPolygon :: { x :: Number, y :: Number } 
               -> Array { x :: Number, y :: Number } 
               -> Boolean
pointInPolygon point pts =
  let n = length pts
  in if n < 3 then false
     else raycastCount point pts 0 0

raycastCount :: { x :: Number, y :: Number }
             -> Array { x :: Number, y :: Number }
             -> Int
             -> Int
             -> Boolean
raycastCount point pts idx count =
  let n = length pts
  in if idx >= n then (count `mod'` 2) /= 0
     else
       case arrayIndex pts idx of
         Nothing -> (count `mod'` 2) /= 0
         Just p1 ->
           let nextIdx = if idx + 1 >= n then 0 else idx + 1
           in case arrayIndex pts nextIdx of
             Nothing -> (count `mod'` 2) /= 0
             Just p2 ->
               let newCount = if rayIntersects point p1 p2 
                              then count + 1 
                              else count
               in raycastCount point pts (idx + 1) newCount

-- | Check if horizontal ray from point intersects line segment.
rayIntersects :: { x :: Number, y :: Number }
              -> { x :: Number, y :: Number }
              -> { x :: Number, y :: Number }
              -> Boolean
rayIntersects point p1 p2 =
  let
    minY = min p1.y p2.y
    maxY = max p1.y p2.y
  in
    if point.y < minY || point.y > maxY then false
    else if point.y == p1.y && point.y == p2.y then false  -- Horizontal edge
    else
      let 
        -- X coordinate where ray intersects the line
        t = (point.y - p1.y) / (p2.y - p1.y)
        xIntersect = p1.x + t * (p2.x - p1.x)
      in xIntersect > point.x

-- | Shoelace formula for polygon area.
shoelaceArea :: Array { x :: Number, y :: Number } -> Number
shoelaceArea pts = shoelaceHelper pts 0 0.0

shoelaceHelper :: Array { x :: Number, y :: Number } -> Int -> Number -> Number
shoelaceHelper pts idx acc =
  let n = length pts
  in if idx >= n then acc
     else
       case arrayIndex pts idx of
         Nothing -> acc
         Just p1 ->
           let nextIdx = if idx + 1 >= n then 0 else idx + 1
           in case arrayIndex pts nextIdx of
             Nothing -> acc
             Just p2 ->
               let term = (p1.x * p2.y) - (p2.x * p1.y)
               in shoelaceHelper pts (idx + 1) (acc + term)

-- | Check if any point satisfies predicate.
anyPoint :: ({ x :: Number, y :: Number } -> Boolean) 
         -> Array { x :: Number, y :: Number } 
         -> Boolean
anyPoint f pts = length (filter f pts) > 0

-- | Absolute value.
abs' :: Number -> Number
abs' n = if n < 0.0 then negate n else n

-- | Integer modulo.
mod' :: Int -> Int -> Int
mod' a b = a - ((a / b) * b)

-- | Safe array head.
arrayHead :: forall a. Array a -> Maybe a
arrayHead arr = arrayIndex arr 0

-- | Safe array index.
arrayIndex :: forall a. Array a -> Int -> Maybe a
arrayIndex arr idx =
  if idx < 0 || idx >= length arr
    then Nothing
    else unsafeArrayIndex arr idx

-- | Unsafe array index (bounds already checked).
unsafeArrayIndex :: forall a. Array a -> Int -> Maybe a
unsafeArrayIndex arr idx = 
  -- Use foldl to find element at index
  let result = foldl (\acc item -> 
        case acc of
          { found: Just _, idx: _ } -> acc
          { found: Nothing, idx: i } ->
            if i == idx 
              then { found: Just item, idx: i + 1 }
              else { found: Nothing, idx: i + 1 }
      ) { found: Nothing, idx: 0 } arr
  in result.found
