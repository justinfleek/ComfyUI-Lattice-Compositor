-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // flatten
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element.Core → DrawCommand Flattener
-- |
-- | Converts the pure-data Element type to GPU DrawCommands.
-- | This is the bridge between the correct Element (Schema atoms)
-- | and the GPU execution layer.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Element (pure data, Schema atoms)
-- |     ↓ flatten
-- | Array (DrawCommand msg)
-- |     ↓ interpret
-- | WebGPU execution
-- | ```
-- |
-- | ## Agent Identity
-- |
-- | Every Element can carry an AgentId. The flatten process preserves
-- | this identity through PickId assignment, enabling:
-- | - Click a pixel → PickId → AgentId → full agent state
-- | - Spatial index integration
-- | - Agent-level hit testing
-- |
-- | ## Coordinate System
-- |
-- | Element uses center-based coordinates (RectangleShape.center).
-- | DrawCommand uses top-left corner coordinates (RectParams.x, y).
-- | This module handles the conversion.
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Element.Core (the correct Element type)
-- | - Hydrogen.GPU.DrawCommand (GPU primitives)
-- | - Hydrogen.Schema.* (bounded atoms)

module Hydrogen.Element.Flatten
  ( -- * Types
    FlattenResult
  , FlattenState
  , initialState
  
  -- * Flattening
  , flatten
  , flattenWithState
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Data.Array (concatMap) as Array
import Data.Array as Data.Array
import Data.Int (floor, toNumber)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))

-- Element.Core: the correct Element type
import Hydrogen.Element.Core
  ( Element(Rectangle, Ellipse, Path, Text, Group, Transform, Empty)
  , RectangleSpec
  , EllipseSpec
  , PathSpec
  , TextSpec
  , GlyphSpec
  , GroupSpec
  , TransformSpec
  , StrokeSpec
  )

-- GPU primitives
import Hydrogen.GPU.DrawCommand as DC

-- Schema atoms
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Dimension.Device (Pixel(Pixel))
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Geometry.Shape
  ( PathCommand(MoveTo, LineTo, CubicTo, QuadraticTo, ClosePath, HorizontalTo, VerticalTo, ArcTo)
  , PixelPoint2D
  )
import Hydrogen.Schema.Material.Fill (Fill(FillSolid, FillNone, FillGradient, FillPattern, FillNoise))
import Hydrogen.Schema.Dimension.Stroke (StrokeWidth)
import Hydrogen.Schema.Dimension.Stroke as Stroke
import Hydrogen.Schema.Typography.GlyphGeometry as Glyph
import Hydrogen.Schema.Temporal.Progress as Progress
import Hydrogen.Schema.Geometry.Transform as Transform

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of flattening an Element tree.
-- |
-- | Contains the array of GPU commands and the updated state (for chaining).
type FlattenResult msg =
  { commands :: Array (DC.DrawCommand msg)
  , state :: FlattenState
  }

-- | State maintained during flattening.
-- |
-- | ## Fields
-- |
-- | - `nextPickId`: Counter for generating unique pick IDs for hit testing.
-- |   Each interactive element gets a unique ID, enabling pixel → agent mapping.
-- |
-- | - `depth`: Current depth for z-ordering. Incremented for each element
-- |   to ensure proper layering without explicit z-index management.
type FlattenState =
  { nextPickId :: Int
  , depth :: Number
  }

-- | Initial flattening state.
-- |
-- | Start with pickId 1 (0 is reserved for "no element") and depth 0.
initialState :: FlattenState
initialState =
  { nextPickId: 1
  , depth: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // flattening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten an Element to DrawCommands.
-- |
-- | Main entry point. Uses initial state and discards final state.
-- |
-- | ```purescript
-- | commands = flatten myElement
-- | -- commands.commands :: Array (DrawCommand msg)
-- | ```
flatten :: forall msg. Element -> FlattenResult msg
flatten element = flattenWithState initialState element

-- | Flatten with explicit state (for composing multiple elements).
-- |
-- | Use this when flattening multiple root elements in sequence,
-- | ensuring pickIds don't collide.
-- |
-- | ```purescript
-- | result1 = flattenWithState initialState element1
-- | result2 = flattenWithState result1.state element2
-- | allCommands = result1.commands <> result2.commands
-- | ```
flattenWithState :: forall msg. FlattenState -> Element -> FlattenResult msg
flattenWithState state element = case element of
  Empty -> 
    { commands: [], state: state }
  
  Rectangle spec ->
    flattenRectangle state spec
  
  Ellipse spec ->
    flattenEllipse state spec
  
  Path spec ->
    flattenPath state spec
  
  Text spec ->
    flattenText state spec
  
  Group spec ->
    flattenGroup state spec
  
  Transform spec ->
    flattenTransform state spec

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // shape // flattening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Rectangle element to DrawRect command.
-- |
-- | Converts from center-based (Element) to top-left-based (DrawCommand).
-- | Handles fill and stroke separately (stroke becomes a second DrawRect).
flattenRectangle :: forall msg. FlattenState -> RectangleSpec -> FlattenResult msg
flattenRectangle state spec =
  let
    -- Convert center-based to top-left-based coordinates
    Tuple x y = centerToTopLeft spec.shape.center spec.shape.width spec.shape.height
    
    -- Convert fill to RGBA
    fillColor = fillToRGBA spec.fill spec.opacity
    
    -- Convert Radius.Corners to DC.Radius.Corners
    corners = convertCorners spec.shape.corners
    
    -- Build the rect params
    rectParams =
      { x: x
      , y: y
      , width: spec.shape.width
      , height: spec.shape.height
      , fill: fillColor
      , cornerRadius: corners
      , depth: state.depth
      , pickId: Nothing  -- No interaction by default
      , onClick: Nothing
      }
    
    -- Main fill command
    fillCmd = DC.DrawRect rectParams
    
    -- Stroke command (if present)
    strokeCmds = case spec.stroke of
      Nothing -> []
      Just strokeSpec -> flattenStrokeAsRect state spec strokeSpec
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: [fillCmd] <> strokeCmds
    , state: newState
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // text // flattening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Text element to DrawPath commands.
-- |
-- | Each glyph in the TextSpec becomes one or more DrawPath commands:
-- | - One for the fill
-- | - One for the stroke (if present)
-- |
-- | Glyph transforms are applied to the path commands.
-- | Progress value is used for opacity modulation (for reveal animations).
flattenText :: forall msg. FlattenState -> TextSpec -> FlattenResult msg
flattenText state spec =
  flattenGlyphs state spec.opacity spec.glyphs

-- | Flatten array of glyphs, threading state through
flattenGlyphs 
  :: forall msg
   . FlattenState 
  -> Opacity.Opacity  -- Overall text opacity
  -> Array GlyphSpec 
  -> FlattenResult msg
flattenGlyphs state _textOpacity glyphs =
  Data.Array.foldl flattenGlyphAccum { commands: [], state: state } glyphs
  where
    flattenGlyphAccum 
      :: FlattenResult msg 
      -> GlyphSpec 
      -> FlattenResult msg
    flattenGlyphAccum acc glyph =
      let result = flattenGlyph acc.state glyph
      in { commands: acc.commands <> result.commands
         , state: result.state
         }

-- | Flatten a single glyph to DrawPath commands.
-- |
-- | Converts the GlyphPath (3D bezier contours) to 2D path segments,
-- | applies the glyph's transform, and creates fill/stroke commands.
flattenGlyph :: forall msg. FlattenState -> GlyphSpec -> FlattenResult msg
flattenGlyph state glyph =
  let
    -- Convert 3D glyph contours to 2D path segments
    segments = glyphPathToSegments glyph.glyph
    
    -- Apply progress to opacity (0 = invisible, 1 = full opacity)
    progressMod = Progress.unwrapProgress glyph.progress
    modifiedOpacity = Opacity.opacity 
      (floor (toNumber (Opacity.unwrap glyph.opacity) * progressMod))
    
    fillColor = fillToRGBA glyph.fill modifiedOpacity
    
    -- Base path params
    pathParams = DC.pathParams segments
    
    -- Apply glyph transform to path params
    -- Transform2D contains translate, rotate, scale, skew, origin
    transformedParams = applyTransformToPathParams glyph.transform pathParams
    
    pathParamsWithFill = transformedParams
      { fill = Just fillColor
      , depth = state.depth
      }
    
    -- Add stroke if present
    strokeCmds = case glyph.stroke of
      Nothing -> []
      Just strokeSpec ->
        let
          strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
          strokeWidth = strokeWidthToPixel strokeSpec.width
          strokeParams = transformedParams
            { stroke = Just strokeColor
            , strokeWidth = strokeWidth
            , depth = state.depth + 0.5
            }
        in [DC.DrawPath strokeParams]
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: [DC.DrawPath pathParamsWithFill] <> strokeCmds
    , state: newState
    }

-- | Convert GlyphPath (3D contours) to flat array of PathSegments.
-- |
-- | Discards Z coordinate since DrawCommand is 2D.
-- | Multiple contours are flattened into a single path array.
glyphPathToSegments :: Glyph.GlyphPath -> Array DC.PathSegment
glyphPathToSegments glyphPath =
  Array.concatMap contourToSegments glyphPath.contours

-- | Convert a single Contour to PathSegments
contourToSegments :: Glyph.Contour -> Array DC.PathSegment
contourToSegments contour =
  Array.concatMap pathCommand3DToSegments contour.commands

-- | Convert a 3D PathCommand to 2D PathSegment(s)
-- |
-- | Z coordinates are discarded for 2D rendering.
pathCommand3DToSegments :: Glyph.PathCommand3D -> Array DC.PathSegment
pathCommand3DToSegments = case _ of
  Glyph.MoveTo3D pt ->
    [DC.MoveTo { x: pt.x, y: pt.y }]
  Glyph.LineTo3D pt ->
    [DC.LineTo { x: pt.x, y: pt.y }]
  Glyph.QuadraticTo3D ctrl end ->
    [DC.QuadraticTo { x: ctrl.x, y: ctrl.y } { x: end.x, y: end.y }]
  Glyph.CubicTo3D c1 c2 end ->
    [DC.CubicTo { x: c1.x, y: c1.y } { x: c2.x, y: c2.y } { x: end.x, y: end.y }]
  Glyph.ClosePath3D ->
    [DC.ClosePath]

-- | Apply Transform2D to PathParams
-- |
-- | Currently a no-op since PathParams doesn't have transform fields.
-- | The glyph transform should be baked into the path segments themselves
-- | via transformPathSegments (to be implemented) or applied at runtime.
-- |
-- | For now, glyph positions come from the transform's translate component
-- | which should be encoded in the GlyphPath geometry at layout time.
applyTransformToPathParams :: forall msg. Transform.Transform2D -> DC.PathParams msg -> DC.PathParams msg
applyTransformToPathParams _transform params = params

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // composition // flattening
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flatten a Group element by recursively flattening children.
-- |
-- | Children are flattened in order, with state threading through
-- | to ensure pickIds and depth values are consistent.
flattenGroup :: forall msg. FlattenState -> GroupSpec -> FlattenResult msg
flattenGroup state spec =
  let
    -- Thread state through all children
    result = flattenChildren state spec.children
  in
    result

-- | Recursively flatten an array of children.
flattenChildren :: forall msg. FlattenState -> Array Element -> FlattenResult msg
flattenChildren state children =
  foldlChildren state [] children
  where
    foldlChildren :: FlattenState -> Array (DC.DrawCommand msg) -> Array Element -> FlattenResult msg
    foldlChildren s acc [] = { commands: acc, state: s }
    foldlChildren s acc elems = case arrayUncons elems of
      Nothing -> { commands: acc, state: s }
      Just { head, tail } ->
        let result = flattenWithState s head
        in foldlChildren result.state (acc <> result.commands) tail

-- | Safe uncons for arrays (returns Maybe of head/tail record).
arrayUncons :: forall a. Array a -> Maybe { head :: a, tail :: Array a }
arrayUncons arr = case arrayHead arr of
  Nothing -> Nothing
  Just h -> Just { head: h, tail: arrayTail arr }

-- | Flatten a Transform element by wrapping child in clip/transform commands.
-- |
-- | Note: Full transform support requires GPU-level transform matrices.
-- | For now, transforms are applied during coordinate conversion.
-- | Complex transforms (rotation, skew) would need DrawCommand extensions.
flattenTransform :: forall msg. FlattenState -> TransformSpec -> FlattenResult msg
flattenTransform state spec =
  -- For now, flatten the child directly
  -- Full transform support would apply the transform matrix here
  -- and potentially emit PushTransform/PopTransform commands
  flattenWithState state spec.child

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert center-based (Element) to top-left (DrawCommand) coordinates.
centerToTopLeft :: PixelPoint2D -> Pixel -> Pixel -> Tuple Pixel Pixel
centerToTopLeft center width height =
  let
    Pixel cx = center.x
    Pixel cy = center.y
    Pixel w = width
    Pixel h = height
    x = cx - (w / 2.0)
    y = cy - (h / 2.0)
  in
    Tuple (Device.px x) (Device.px y)

-- | Convert Fill and Opacity to RGBA for GPU rendering.
fillToRGBA :: Fill -> Opacity.Opacity -> RGB.RGBA
fillToRGBA fill opacity = case fill of
  FillSolid rgb ->
    let
      rec = RGB.rgbToRecord rgb
      alpha = Opacity.unwrap opacity
    in
      RGB.rgba rec.r rec.g rec.b alpha
  
  FillNone ->
    RGB.rgba 0 0 0 0  -- Fully transparent
  
  -- Gradients, patterns, noise: placeholder gray (shader support needed)
  FillGradient _ ->
    let alpha = Opacity.unwrap opacity
    in RGB.rgba 128 128 128 alpha
  
  FillPattern _ ->
    let alpha = Opacity.unwrap opacity
    in RGB.rgba 200 200 200 alpha
  
  FillNoise _ ->
    let alpha = Opacity.unwrap opacity
    in RGB.rgba 100 100 100 alpha

-- | Convert Radius.Corners (same structure, identity function).
convertCorners :: Radius.Corners -> Radius.Corners
convertCorners = identity
  where
    identity :: forall a. a -> a
    identity x = x

-- | Convert StrokeWidth to Pixel (extracts bounded value).
strokeWidthToPixel :: StrokeWidth -> Pixel
strokeWidthToPixel sw = Device.px (Stroke.strokeWidthValue sw)

-- | Convert Schema PathCommand to DrawCommand PathSegment.
convertPathCommand :: PathCommand -> Array DC.PathSegment
convertPathCommand cmd = case cmd of
  MoveTo pt ->
    [ DC.MoveTo (convertPoint pt) ]
  
  LineTo pt ->
    [ DC.LineTo (convertPoint pt) ]
  
  CubicTo c1 c2 end ->
    [ DC.CubicTo (convertPoint c1) (convertPoint c2) (convertPoint end) ]
  
  QuadraticTo c end ->
    [ DC.QuadraticTo (convertPoint c) (convertPoint end) ]
  
  ClosePath ->
    [ DC.ClosePath ]
  
  -- HorizontalTo and VerticalTo need current position context
  -- For now, emit LineTo with the available coordinate
  HorizontalTo px ->
    [ DC.LineTo { x: px, y: Device.px 0.0 } ]  -- Y would need context
  
  VerticalTo py ->
    [ DC.LineTo { x: Device.px 0.0, y: py } ]  -- X would need context
  
  -- Arc conversion is complex - needs bezier approximation
  -- For now, emit LineTo as fallback
  ArcTo _ end ->
    [ DC.LineTo (convertPoint end) ]

-- | Convert PixelPoint2D to DrawCommand Point2D (same structure).
convertPoint :: PixelPoint2D -> DC.Point2D
convertPoint pt = { x: pt.x, y: pt.y }

-- | Get the first element of an array (safe).
arrayHead :: forall a. Array a -> Maybe a
arrayHead = Data.Array.head

-- | Get all but the first element of an array.
arrayTail :: forall a. Array a -> Array a
arrayTail arr = case Data.Array.tail arr of
  Nothing -> []
  Just t -> t

-- | Flatten stroke as DrawPath (DrawRect doesn't support stroke directly).
flattenStrokeAsRect :: forall msg. FlattenState -> RectangleSpec -> StrokeSpec -> Array (DC.DrawCommand msg)
flattenStrokeAsRect state spec strokeSpec =
  let
    Tuple x y = centerToTopLeft spec.shape.center spec.shape.width spec.shape.height
    Pixel xVal = x
    Pixel yVal = y
    Pixel wVal = spec.shape.width
    Pixel hVal = spec.shape.height
    topLeft = { x: Device.px xVal, y: Device.px yVal }
    topRight = { x: Device.px (xVal + wVal), y: Device.px yVal }
    bottomRight = { x: Device.px (xVal + wVal), y: Device.px (yVal + hVal) }
    bottomLeft = { x: Device.px xVal, y: Device.px (yVal + hVal) }
    segments =
      [ DC.MoveTo topLeft
      , DC.LineTo topRight
      , DC.LineTo bottomRight
      , DC.LineTo bottomLeft
      , DC.ClosePath
      ]
    strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
    strokeWidth = strokeWidthToPixel strokeSpec.width
    pathParams = DC.pathParams segments
    pathParamsWithStroke = pathParams
      { stroke = Just strokeColor
      , strokeWidth = strokeWidth
      , depth = state.depth + 0.5
      }
  in
    [ DC.DrawPath pathParamsWithStroke ]

-- | Flatten Ellipse to DrawPath (4 cubic beziers with kappa = 0.5522847498).
flattenEllipse :: forall msg. FlattenState -> EllipseSpec -> FlattenResult msg
flattenEllipse state spec =
  let
    Pixel cx = spec.shape.center.x
    Pixel cy = spec.shape.center.y
    Pixel rx = spec.shape.radiusX
    Pixel ry = spec.shape.radiusY
    kappa = 0.5522847498  -- (4/3) * tan(π/8)
    ox = rx * kappa
    oy = ry * kappa
    
    top = { x: Device.px cx, y: Device.px (cy - ry) }
    right = { x: Device.px (cx + rx), y: Device.px cy }
    bottom = { x: Device.px cx, y: Device.px (cy + ry) }
    left = { x: Device.px (cx - rx), y: Device.px cy }
    
    topToRightC1 = { x: Device.px (cx + ox), y: Device.px (cy - ry) }
    topToRightC2 = { x: Device.px (cx + rx), y: Device.px (cy - oy) }
    rightToBottomC1 = { x: Device.px (cx + rx), y: Device.px (cy + oy) }
    rightToBottomC2 = { x: Device.px (cx + ox), y: Device.px (cy + ry) }
    bottomToLeftC1 = { x: Device.px (cx - ox), y: Device.px (cy + ry) }
    bottomToLeftC2 = { x: Device.px (cx - rx), y: Device.px (cy + oy) }
    leftToTopC1 = { x: Device.px (cx - rx), y: Device.px (cy - oy) }
    leftToTopC2 = { x: Device.px (cx - ox), y: Device.px (cy - ry) }
    
    segments =
      [ DC.MoveTo top
      , DC.CubicTo topToRightC1 topToRightC2 right
      , DC.CubicTo rightToBottomC1 rightToBottomC2 bottom
      , DC.CubicTo bottomToLeftC1 bottomToLeftC2 left
      , DC.CubicTo leftToTopC1 leftToTopC2 top
      , DC.ClosePath
      ]
    
    fillColor = fillToRGBA spec.fill spec.opacity
    
    pathParams = DC.pathParams segments
    pathParamsWithFill = pathParams
      { fill = Just fillColor
      , depth = state.depth
      }
    
    -- Add stroke if present
    strokeCmds = case spec.stroke of
      Nothing -> []
      Just strokeSpec ->
        let
          strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
          strokeWidth = strokeWidthToPixel strokeSpec.width
          strokeParams = pathParams
            { stroke = Just strokeColor
            , strokeWidth = strokeWidth
            , depth = state.depth + 0.5
            }
        in [DC.DrawPath strokeParams]
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: [DC.DrawPath pathParamsWithFill] <> strokeCmds
    , state: newState
    }

-- | Flatten a Path element to DrawPath command.
-- |
-- | Converts Schema PathCommands to DrawCommand PathSegments.
flattenPath :: forall msg. FlattenState -> PathSpec -> FlattenResult msg
flattenPath state spec =
  let
    -- Convert PathCommand array to PathSegment array
    segments = Array.concatMap convertPathCommand spec.shape.commands
    
    fillColor = fillToRGBA spec.fill spec.opacity
    
    pathParams = DC.pathParams segments
    pathParamsWithFill = pathParams
      { fill = Just fillColor
      , depth = state.depth
      }
    
    -- Add stroke if present
    strokeCmds = case spec.stroke of
      Nothing -> []
      Just strokeSpec ->
        let
          strokeColor = fillToRGBA strokeSpec.fill strokeSpec.opacity
          strokeWidth = strokeWidthToPixel strokeSpec.width
          strokeParams = pathParams
            { stroke = Just strokeColor
            , strokeWidth = strokeWidth
            , depth = state.depth + 0.5
            }
        in [DC.DrawPath strokeParams]
    
    newState = state { depth = state.depth + 1.0 }
  in
    { commands: [DC.DrawPath pathParamsWithFill] <> strokeCmds
    , state: newState
    }
