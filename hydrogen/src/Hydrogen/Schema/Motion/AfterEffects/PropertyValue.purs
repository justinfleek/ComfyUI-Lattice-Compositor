-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--              // hydrogen // schema // motion // aftereffects // propertyvalue
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | After Effects Property Values — Complete AE property value type system.
-- |
-- | Every animatable property in After Effects has a value type. This module
-- | defines ALL value types exactly as they exist in AE's scripting API.
-- |
-- | ## AE Property Value Types
-- |
-- | From Adobe's ExtendScript documentation:
-- |
-- | | PropertyValueType | Description | Example Properties |
-- | |-------------------|-------------|--------------------|
-- | | NO_VALUE | No value | Groups, indexed groups |
-- | | ThreeD_SPATIAL | [x,y,z] with spatial tangents | 3D Position |
-- | | ThreeD | [x,y,z] without spatial tangents | 3D Scale, Orientation |
-- | | TwoD_SPATIAL | [x,y] with spatial tangents | 2D Position |
-- | | TwoD | [x,y] without spatial tangents | 2D Scale, Anchor Point |
-- | | OneD | Single number | Opacity, Rotation |
-- | | COLOR | [r,g,b,a] 0-1 range | Fill Color |
-- | | CUSTOM_VALUE | Opaque data | Text Source |
-- | | MARKER | Marker data | Markers |
-- | | LAYER_INDEX | Layer reference (1-based) | Layer parameter |
-- | | MASK_INDEX | Mask reference (1-based) | Mask parameter |
-- | | SHAPE | Shape data | Path property |
-- | | TEXT_DOCUMENT | Text document | Source Text |

module Hydrogen.Schema.Motion.AfterEffects.PropertyValue
  ( -- * Property Value Type Enum
    PropertyValueType(..)
  , propertyValueTypeToString
  , propertyValueTypeFromString
  
  -- * Spatial 3D Value
  , Spatial3D
  , spatial3D
  , spatial3DFromArray
  , spatial3DX
  , spatial3DY
  , spatial3DZ
  , spatial3DToArray
  
  -- * Non-Spatial 3D Value  
  , ThreeD
  , threeD
  , threeDFromArray
  , threeDX
  , threeDY
  , threeDZ
  , threeDToArray
  
  -- * Spatial 2D Value
  , Spatial2D
  , spatial2D
  , spatial2DFromArray
  , spatial2DX
  , spatial2DY
  , spatial2DToArray
  
  -- * Non-Spatial 2D Value
  , TwoD
  , twoD
  , twoDFromArray
  , twoDX
  , twoDY
  , twoDToArray
  
  -- * 1D Value
  , OneD
  , oneD
  , oneDValue
  
  -- * Color Value (0-1 range RGBA)
  , ColorValue
  , colorValue
  , colorValueRGB
  , colorValueR
  , colorValueG
  , colorValueB
  , colorValueA
  , colorValueToArray
  
  -- * Shape Value
  , ShapeValue
  , shapeValue
  , shapeVertices
  , shapeInTangents
  , shapeOutTangents
  , shapeClosed
  
  -- * Marker Value
  , MarkerValue
  , markerValue
  , markerComment
  , markerChapter
  , markerUrl
  , markerFrameTarget
  , markerCuePointName
  , markerCuePointParams
  , markerDuration
  , markerProtectedRegion
  
  -- * Text Document Value
  , TextDocumentValue
  , textDocumentValue
  , textDocumentText
  , textDocumentFont
  , textDocumentFontSize
  , textDocumentFillColor
  , textDocumentStrokeColor
  , textDocumentStrokeWidth
  , textDocumentApplyFill
  , textDocumentApplyStroke
  , textDocumentJustification
  , textDocumentTracking
  , textDocumentLeading
  , textDocumentBaselineShift
  , textDocumentSmallCaps
  , textDocumentAllCaps
  , textDocumentFauxBold
  , textDocumentFauxItalic
  , textDocumentSuperscript
  , textDocumentSubscript
  
  -- * Justification
  , ParagraphJustification(..)
  , paragraphJustificationToInt
  , paragraphJustificationFromInt
  
  -- * Layer/Mask Index
  , LayerIndex
  , layerIndex
  , layerIndexValue
  , MaskIndex
  , maskIndex
  , maskIndexValue
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , ($)
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , compare
  , min
  , max
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , show
  , map
  , pure
  , bind
  , apply
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (index, length) as Array
import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // property // value // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Property value type enum - exactly matches AE's PropertyValueType.
data PropertyValueType
  = PVTNoValue        -- ^ Property has no value (group)
  | PVTThreeDSpatial  -- ^ 3D spatial value with bezier path tangents
  | PVTThreeD         -- ^ 3D value without spatial tangents
  | PVTTwoDSpatial    -- ^ 2D spatial value with bezier path tangents
  | PVTTwoD           -- ^ 2D value without spatial tangents
  | PVTOneD           -- ^ Single numeric value
  | PVTColor          -- ^ RGBA color (0-1 per channel)
  | PVTCustomValue    -- ^ Opaque custom data
  | PVTMarker         -- ^ Composition/layer marker
  | PVTLayerIndex     -- ^ Reference to another layer (1-based)
  | PVTMaskIndex      -- ^ Reference to a mask (1-based)
  | PVTShape          -- ^ Bezier shape path
  | PVTTextDocument   -- ^ Text source document

derive instance eqPropertyValueType :: Eq PropertyValueType
derive instance ordPropertyValueType :: Ord PropertyValueType

instance showPropertyValueType :: Show PropertyValueType where
  show PVTNoValue = "NO_VALUE"
  show PVTThreeDSpatial = "ThreeD_SPATIAL"
  show PVTThreeD = "ThreeD"
  show PVTTwoDSpatial = "TwoD_SPATIAL"
  show PVTTwoD = "TwoD"
  show PVTOneD = "OneD"
  show PVTColor = "COLOR"
  show PVTCustomValue = "CUSTOM_VALUE"
  show PVTMarker = "MARKER"
  show PVTLayerIndex = "LAYER_INDEX"
  show PVTMaskIndex = "MASK_INDEX"
  show PVTShape = "SHAPE"
  show PVTTextDocument = "TEXT_DOCUMENT"

propertyValueTypeToString :: PropertyValueType -> String
propertyValueTypeToString = show

propertyValueTypeFromString :: String -> Maybe PropertyValueType
propertyValueTypeFromString "NO_VALUE" = Just PVTNoValue
propertyValueTypeFromString "ThreeD_SPATIAL" = Just PVTThreeDSpatial
propertyValueTypeFromString "ThreeD" = Just PVTThreeD
propertyValueTypeFromString "TwoD_SPATIAL" = Just PVTTwoDSpatial
propertyValueTypeFromString "TwoD" = Just PVTTwoD
propertyValueTypeFromString "OneD" = Just PVTOneD
propertyValueTypeFromString "COLOR" = Just PVTColor
propertyValueTypeFromString "CUSTOM_VALUE" = Just PVTCustomValue
propertyValueTypeFromString "MARKER" = Just PVTMarker
propertyValueTypeFromString "LAYER_INDEX" = Just PVTLayerIndex
propertyValueTypeFromString "MASK_INDEX" = Just PVTMaskIndex
propertyValueTypeFromString "SHAPE" = Just PVTShape
propertyValueTypeFromString "TEXT_DOCUMENT" = Just PVTTextDocument
propertyValueTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // spatial // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D spatial value - position in 3D space WITH motion path tangents.
-- |
-- | In AE, 3D Position is Spatial3D because the keyframes form a bezier
-- | motion path in 3D space. The tangent handles control the curve shape.
newtype Spatial3D = Spatial3D { x :: Number, y :: Number, z :: Number }

derive instance eqSpatial3D :: Eq Spatial3D
derive instance ordSpatial3D :: Ord Spatial3D

instance showSpatial3D :: Show Spatial3D where
  show (Spatial3D v) = "[" <> show v.x <> ", " <> show v.y <> ", " <> show v.z <> "]"

spatial3D :: Number -> Number -> Number -> Spatial3D
spatial3D x y z = Spatial3D { x, y, z }

spatial3DFromArray :: Array Number -> Maybe Spatial3D
spatial3DFromArray arr = 
  case Array.length arr of
    3 -> do
      x <- Array.index arr 0
      y <- Array.index arr 1
      z <- Array.index arr 2
      Just (Spatial3D { x, y, z })
    _ -> Nothing

spatial3DX :: Spatial3D -> Number
spatial3DX (Spatial3D v) = v.x

spatial3DY :: Spatial3D -> Number
spatial3DY (Spatial3D v) = v.y

spatial3DZ :: Spatial3D -> Number
spatial3DZ (Spatial3D v) = v.z

spatial3DToArray :: Spatial3D -> Array Number
spatial3DToArray (Spatial3D v) = [v.x, v.y, v.z]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // three // d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D non-spatial value - 3 numbers WITHOUT motion path tangents.
-- |
-- | Used for: Scale, Orientation, 3D Point Control, etc.
-- | These animate in value space, not spatial space.
newtype ThreeD = ThreeD { x :: Number, y :: Number, z :: Number }

derive instance eqThreeD :: Eq ThreeD
derive instance ordThreeD :: Ord ThreeD

instance showThreeD :: Show ThreeD where
  show (ThreeD v) = "[" <> show v.x <> ", " <> show v.y <> ", " <> show v.z <> "]"

threeD :: Number -> Number -> Number -> ThreeD
threeD x y z = ThreeD { x, y, z }

threeDFromArray :: Array Number -> Maybe ThreeD
threeDFromArray arr = 
  case Array.length arr of
    3 -> do
      x <- Array.index arr 0
      y <- Array.index arr 1
      z <- Array.index arr 2
      Just (ThreeD { x, y, z })
    _ -> Nothing

threeDX :: ThreeD -> Number
threeDX (ThreeD v) = v.x

threeDY :: ThreeD -> Number
threeDY (ThreeD v) = v.y

threeDZ :: ThreeD -> Number
threeDZ (ThreeD v) = v.z

threeDToArray :: ThreeD -> Array Number
threeDToArray (ThreeD v) = [v.x, v.y, v.z]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // spatial // 2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D spatial value - position in 2D space WITH motion path tangents.
-- |
-- | In AE, 2D Position is Spatial2D because keyframes form a bezier
-- | motion path. When "Separate Dimensions" is disabled.
newtype Spatial2D = Spatial2D { x :: Number, y :: Number }

derive instance eqSpatial2D :: Eq Spatial2D
derive instance ordSpatial2D :: Ord Spatial2D

instance showSpatial2D :: Show Spatial2D where
  show (Spatial2D v) = "[" <> show v.x <> ", " <> show v.y <> "]"

spatial2D :: Number -> Number -> Spatial2D
spatial2D x y = Spatial2D { x, y }

spatial2DFromArray :: Array Number -> Maybe Spatial2D
spatial2DFromArray arr = 
  case Array.length arr of
    2 -> do
      x <- Array.index arr 0
      y <- Array.index arr 1
      Just (Spatial2D { x, y })
    _ -> Nothing

spatial2DX :: Spatial2D -> Number
spatial2DX (Spatial2D v) = v.x

spatial2DY :: Spatial2D -> Number
spatial2DY (Spatial2D v) = v.y

spatial2DToArray :: Spatial2D -> Array Number
spatial2DToArray (Spatial2D v) = [v.x, v.y]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // two // d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D non-spatial value - 2 numbers WITHOUT motion path tangents.
-- |
-- | Used for: Anchor Point, Scale (2D), 2D Point Control, etc.
newtype TwoD = TwoD { x :: Number, y :: Number }

derive instance eqTwoD :: Eq TwoD
derive instance ordTwoD :: Ord TwoD

instance showTwoD :: Show TwoD where
  show (TwoD v) = "[" <> show v.x <> ", " <> show v.y <> "]"

twoD :: Number -> Number -> TwoD
twoD x y = TwoD { x, y }

twoDFromArray :: Array Number -> Maybe TwoD
twoDFromArray arr = 
  case Array.length arr of
    2 -> do
      x <- Array.index arr 0
      y <- Array.index arr 1
      Just (TwoD { x, y })
    _ -> Nothing

twoDX :: TwoD -> Number
twoDX (TwoD v) = v.x

twoDY :: TwoD -> Number
twoDY (TwoD v) = v.y

twoDToArray :: TwoD -> Array Number
twoDToArray (TwoD v) = [v.x, v.y]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // one // d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 1D value - single number.
-- |
-- | Used for: Opacity, Rotation, Slider Controls, etc.
-- | The graph editor shows this as a value graph.
newtype OneD = OneD Number

derive instance eqOneD :: Eq OneD
derive instance ordOneD :: Ord OneD

instance showOneD :: Show OneD where
  show (OneD v) = show v

oneD :: Number -> OneD
oneD = OneD

oneDValue :: OneD -> Number
oneDValue (OneD v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color value - RGBA in 0-1 range.
-- |
-- | AE uses 0-1 floating point for colors internally.
-- | This maps to Fill Color, Stroke Color, etc.
newtype ColorValue = ColorValue { r :: Number, g :: Number, b :: Number, a :: Number }

derive instance eqColorValue :: Eq ColorValue
derive instance ordColorValue :: Ord ColorValue

instance showColorValue :: Show ColorValue where
  show (ColorValue c) = 
    "[" <> show c.r <> ", " <> show c.g <> ", " <> show c.b <> ", " <> show c.a <> "]"

colorValue :: Number -> Number -> Number -> Number -> ColorValue
colorValue r g b a = ColorValue 
  { r: clampNumber 0.0 1.0 r
  , g: clampNumber 0.0 1.0 g
  , b: clampNumber 0.0 1.0 b
  , a: clampNumber 0.0 1.0 a
  }

colorValueRGB :: Number -> Number -> Number -> ColorValue
colorValueRGB r g b = colorValue r g b 1.0

colorValueR :: ColorValue -> Number
colorValueR (ColorValue c) = c.r

colorValueG :: ColorValue -> Number
colorValueG (ColorValue c) = c.g

colorValueB :: ColorValue -> Number
colorValueB (ColorValue c) = c.b

colorValueA :: ColorValue -> Number
colorValueA (ColorValue c) = c.a

colorValueToArray :: ColorValue -> Array Number
colorValueToArray (ColorValue c) = [c.r, c.g, c.b, c.a]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape value - bezier path data.
-- |
-- | Exactly matches AE's Shape object:
-- | - vertices: Array of [x,y] anchor points
-- | - inTangents: Array of [x,y] incoming tangent handles (relative)
-- | - outTangents: Array of [x,y] outgoing tangent handles (relative)
-- | - closed: Whether the path is closed
-- |
-- | All tangent values are RELATIVE to their vertex.
type ShapeValue =
  { vertices :: Array (Array Number)     -- ^ Array of [x,y] points
  , inTangents :: Array (Array Number)   -- ^ Array of [x,y] relative tangents
  , outTangents :: Array (Array Number)  -- ^ Array of [x,y] relative tangents
  , closed :: Boolean
  }

shapeValue 
  :: Array (Array Number) 
  -> Array (Array Number) 
  -> Array (Array Number) 
  -> Boolean 
  -> ShapeValue
shapeValue verts inT outT cl =
  { vertices: verts
  , inTangents: inT
  , outTangents: outT
  , closed: cl
  }

shapeVertices :: ShapeValue -> Array (Array Number)
shapeVertices s = s.vertices

shapeInTangents :: ShapeValue -> Array (Array Number)
shapeInTangents s = s.inTangents

shapeOutTangents :: ShapeValue -> Array (Array Number)
shapeOutTangents s = s.outTangents

shapeClosed :: ShapeValue -> Boolean
shapeClosed s = s.closed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // marker
-- ═════════════════════════════════════════════════════════════════════════════

-- | Marker value - composition or layer marker.
-- |
-- | Exactly matches AE's MarkerValue object properties.
type MarkerValue =
  { comment :: String                       -- ^ Marker comment text
  , chapter :: String                       -- ^ Chapter name (for chapter markers)
  , url :: String                           -- ^ Web URL
  , frameTarget :: String                   -- ^ Frame target for URL
  , cuePointName :: String                  -- ^ Cue point name (for video cue points)
  , cuePointParams :: Array { key :: String, value :: String }  -- ^ Cue point parameters
  , duration :: Number                      -- ^ Marker duration in seconds
  , protectedRegion :: Boolean              -- ^ Whether marker defines protected region
  }

markerValue :: String -> MarkerValue
markerValue comment =
  { comment: comment
  , chapter: ""
  , url: ""
  , frameTarget: ""
  , cuePointName: ""
  , cuePointParams: []
  , duration: 0.0
  , protectedRegion: false
  }

markerComment :: MarkerValue -> String
markerComment m = m.comment

markerChapter :: MarkerValue -> String
markerChapter m = m.chapter

markerUrl :: MarkerValue -> String
markerUrl m = m.url

markerFrameTarget :: MarkerValue -> String
markerFrameTarget m = m.frameTarget

markerCuePointName :: MarkerValue -> String
markerCuePointName m = m.cuePointName

markerCuePointParams :: MarkerValue -> Array { key :: String, value :: String }
markerCuePointParams m = m.cuePointParams

markerDuration :: MarkerValue -> Number
markerDuration m = m.duration

markerProtectedRegion :: MarkerValue -> Boolean
markerProtectedRegion m = m.protectedRegion

-- ═════════════════════════════════════════════════════════════════════════════
--                                            // paragraph // justification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Paragraph justification - exactly matches AE's ParagraphJustification enum.
data ParagraphJustification
  = PJLeftJustify            -- ^ 7213 - Left align
  | PJCenterJustify          -- ^ 7214 - Center align
  | PJRightJustify           -- ^ 7215 - Right align
  | PJFullJustifyLastLineLeft    -- ^ 7216 - Full justify, last line left
  | PJFullJustifyLastLineRight   -- ^ 7217 - Full justify, last line right
  | PJFullJustifyLastLineCenter  -- ^ 7218 - Full justify, last line center
  | PJFullJustifyLastLineFull    -- ^ 7219 - Full justify all lines

derive instance eqParagraphJustification :: Eq ParagraphJustification
derive instance ordParagraphJustification :: Ord ParagraphJustification

instance showParagraphJustification :: Show ParagraphJustification where
  show PJLeftJustify = "LEFT_JUSTIFY"
  show PJCenterJustify = "CENTER_JUSTIFY"
  show PJRightJustify = "RIGHT_JUSTIFY"
  show PJFullJustifyLastLineLeft = "FULL_JUSTIFY_LASTLINE_LEFT"
  show PJFullJustifyLastLineRight = "FULL_JUSTIFY_LASTLINE_RIGHT"
  show PJFullJustifyLastLineCenter = "FULL_JUSTIFY_LASTLINE_CENTER"
  show PJFullJustifyLastLineFull = "FULL_JUSTIFY_LASTLINE_FULL"

paragraphJustificationToInt :: ParagraphJustification -> Int
paragraphJustificationToInt PJLeftJustify = 7213
paragraphJustificationToInt PJCenterJustify = 7214
paragraphJustificationToInt PJRightJustify = 7215
paragraphJustificationToInt PJFullJustifyLastLineLeft = 7216
paragraphJustificationToInt PJFullJustifyLastLineRight = 7217
paragraphJustificationToInt PJFullJustifyLastLineCenter = 7218
paragraphJustificationToInt PJFullJustifyLastLineFull = 7219

paragraphJustificationFromInt :: Int -> Maybe ParagraphJustification
paragraphJustificationFromInt 7213 = Just PJLeftJustify
paragraphJustificationFromInt 7214 = Just PJCenterJustify
paragraphJustificationFromInt 7215 = Just PJRightJustify
paragraphJustificationFromInt 7216 = Just PJFullJustifyLastLineLeft
paragraphJustificationFromInt 7217 = Just PJFullJustifyLastLineRight
paragraphJustificationFromInt 7218 = Just PJFullJustifyLastLineCenter
paragraphJustificationFromInt 7219 = Just PJFullJustifyLastLineFull
paragraphJustificationFromInt _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // text // document
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text document value - complete text layer source.
-- |
-- | Exactly matches AE's TextDocument object.
-- | This is the value type for the "Source Text" property.
type TextDocumentValue =
  { text :: String                          -- ^ The actual text content
  , font :: String                          -- ^ Font PostScript name
  , fontSize :: Number                      -- ^ Font size in pixels
  , fillColor :: ColorValue                 -- ^ Text fill color
  , strokeColor :: ColorValue               -- ^ Text stroke color
  , strokeWidth :: Number                   -- ^ Stroke width in pixels
  , applyFill :: Boolean                    -- ^ Whether fill is applied
  , applyStroke :: Boolean                  -- ^ Whether stroke is applied
  , justification :: ParagraphJustification -- ^ Paragraph alignment
  , tracking :: Number                      -- ^ Tracking (letter spacing) in 1/1000 em
  , leading :: Number                       -- ^ Line spacing (auto if negative)
  , baselineShift :: Number                 -- ^ Baseline shift in pixels
  , smallCaps :: Boolean                    -- ^ Small caps enabled
  , allCaps :: Boolean                      -- ^ All caps enabled
  , fauxBold :: Boolean                     -- ^ Faux bold enabled
  , fauxItalic :: Boolean                   -- ^ Faux italic enabled
  , superscript :: Boolean                  -- ^ Superscript enabled
  , subscript :: Boolean                    -- ^ Subscript enabled
  }

textDocumentValue :: String -> TextDocumentValue
textDocumentValue txt =
  { text: txt
  , font: "Arial"
  , fontSize: 72.0
  , fillColor: colorValueRGB 1.0 1.0 1.0
  , strokeColor: colorValueRGB 0.0 0.0 0.0
  , strokeWidth: 0.0
  , applyFill: true
  , applyStroke: false
  , justification: PJLeftJustify
  , tracking: 0.0
  , leading: negate 1.0  -- Auto leading
  , baselineShift: 0.0
  , smallCaps: false
  , allCaps: false
  , fauxBold: false
  , fauxItalic: false
  , superscript: false
  , subscript: false
  }

textDocumentText :: TextDocumentValue -> String
textDocumentText t = t.text

textDocumentFont :: TextDocumentValue -> String
textDocumentFont t = t.font

textDocumentFontSize :: TextDocumentValue -> Number
textDocumentFontSize t = t.fontSize

textDocumentFillColor :: TextDocumentValue -> ColorValue
textDocumentFillColor t = t.fillColor

textDocumentStrokeColor :: TextDocumentValue -> ColorValue
textDocumentStrokeColor t = t.strokeColor

textDocumentStrokeWidth :: TextDocumentValue -> Number
textDocumentStrokeWidth t = t.strokeWidth

textDocumentApplyFill :: TextDocumentValue -> Boolean
textDocumentApplyFill t = t.applyFill

textDocumentApplyStroke :: TextDocumentValue -> Boolean
textDocumentApplyStroke t = t.applyStroke

textDocumentJustification :: TextDocumentValue -> ParagraphJustification
textDocumentJustification t = t.justification

textDocumentTracking :: TextDocumentValue -> Number
textDocumentTracking t = t.tracking

textDocumentLeading :: TextDocumentValue -> Number
textDocumentLeading t = t.leading

textDocumentBaselineShift :: TextDocumentValue -> Number
textDocumentBaselineShift t = t.baselineShift

textDocumentSmallCaps :: TextDocumentValue -> Boolean
textDocumentSmallCaps t = t.smallCaps

textDocumentAllCaps :: TextDocumentValue -> Boolean
textDocumentAllCaps t = t.allCaps

textDocumentFauxBold :: TextDocumentValue -> Boolean
textDocumentFauxBold t = t.fauxBold

textDocumentFauxItalic :: TextDocumentValue -> Boolean
textDocumentFauxItalic t = t.fauxItalic

textDocumentSuperscript :: TextDocumentValue -> Boolean
textDocumentSuperscript t = t.superscript

textDocumentSubscript :: TextDocumentValue -> Boolean
textDocumentSubscript t = t.subscript

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // layer // mask // index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layer index - 1-based reference to a layer.
-- |
-- | In AE, layer indices are 1-based (topmost layer = 1).
newtype LayerIndex = LayerIndex Int

derive instance eqLayerIndex :: Eq LayerIndex
derive instance ordLayerIndex :: Ord LayerIndex

instance showLayerIndex :: Show LayerIndex where
  show (LayerIndex i) = "Layer[" <> show i <> "]"

layerIndex :: Int -> Maybe LayerIndex
layerIndex i
  | i >= 1 = Just (LayerIndex i)
  | otherwise = Nothing

layerIndexValue :: LayerIndex -> Int
layerIndexValue (LayerIndex i) = i

-- | Mask index - 1-based reference to a mask.
-- |
-- | In AE, mask indices are 1-based.
newtype MaskIndex = MaskIndex Int

derive instance eqMaskIndex :: Eq MaskIndex
derive instance ordMaskIndex :: Ord MaskIndex

instance showMaskIndex :: Show MaskIndex where
  show (MaskIndex i) = "Mask[" <> show i <> "]"

maskIndex :: Int -> Maybe MaskIndex
maskIndex i
  | i >= 1 = Just (MaskIndex i)
  | otherwise = Nothing

maskIndexValue :: MaskIndex -> Int
maskIndexValue (MaskIndex i) = i
