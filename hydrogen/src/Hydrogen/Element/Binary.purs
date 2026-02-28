-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // binary
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Element Binary Serialization
-- |
-- | Binary wire format for Element values. Enables agents to exchange
-- | Element data directly — not just the GPU commands they produce.
-- |
-- | ## Why This Matters
-- |
-- | At billion-agent scale:
-- | - Agents compose UI as Element values
-- | - Elements must serialize deterministically for wire transport
-- | - Same Element → same bytes → same UUID5 (identity)
-- |
-- | ## Wire Format
-- |
-- | ```
-- | ElementBuffer := Header + ElementData
-- |
-- | Header (16 bytes):
-- |   magic     : u32 = 0x454C454D ("ELEM")
-- |   version   : u32 = 1
-- |   size      : u32 = total size in bytes
-- |   checksum  : u32 = reserved (0 for now)
-- |
-- | ElementData := ElementTag (u8) + Payload
-- |
-- | ElementTag:
-- |   0x00 = Empty
-- |   0x01 = Rectangle
-- |   0x02 = Ellipse
-- |   0x03 = Path
-- |   0x04 = Group
-- |   0x05 = Transform
-- | ```
-- |
-- | ## Determinism Guarantee
-- |
-- | Same Element value produces identical bytes. Guaranteed because:
-- | - All Schema atoms have deterministic serialization
-- | - Field order is fixed
-- | - No padding variation (explicit padding)

module Hydrogen.Element.Binary
  ( -- * Types
    Bytes
  , Header
  , ElementTag
      ( TagEmpty
      , TagRectangle
      , TagEllipse
      , TagPath
      , TagText
      , TagGroup
      , TagTransform
      )
  
  -- * Constants
  , magic
  , version
  , headerSize
  
  -- * Serialization
  , serialize
  , serializeElement
  
  -- * Deserialization
  , deserialize
  , deserializeElement
  
  -- * Low-level
  , toByteArray
  , fromByteArray
  , bytesLength
  , writeU32
  , writeU8
  , writeF32
  , readU32
  , readU8
  , readF32
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , bind
  , pure
  , show
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (==)
  , (/=)
  , (>)
  , (<>)
  , (&&)
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (floor, toNumber)
import Data.Int.Bits (shl, shr, (.&.), (.|.))
import Data.Tuple (Tuple(Tuple))

-- Element types
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

-- Schema atoms
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Dimension.Stroke as Stroke
import Hydrogen.Schema.Geometry.Angle (unwrapDegrees, degrees)
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Geometry.Shape as Shape
import Hydrogen.Schema.Geometry.Stroke as GeomStroke
import Hydrogen.Schema.Geometry.Transform as Transform
import Hydrogen.Schema.Material.Fill as Fill
import Hydrogen.Schema.Temporal.Progress as Progress
import Hydrogen.Schema.Typography.GlyphGeometry as Glyph

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Raw bytes as array of integers (0-255).
-- | This is the pure representation — actual TypedArray created at boundary.
newtype Bytes = Bytes (Array Int)

derive instance eqBytes :: Eq Bytes

instance showBytes :: Show Bytes where
  show (Bytes arr) = "Bytes[" <> show (Array.length arr) <> "]"

-- | Wire format header
type Header =
  { magic :: Int      -- 0x454C454D ("ELEM")
  , version :: Int    -- 1
  , size :: Int       -- Total size in bytes
  , checksum :: Int   -- Reserved (0)
  }

-- | Element variant tags
data ElementTag
  = TagEmpty
  | TagRectangle
  | TagEllipse
  | TagPath
  | TagText
  | TagGroup
  | TagTransform

derive instance eqElementTag :: Eq ElementTag
derive instance ordElementTag :: Ord ElementTag

instance showElementTag :: Show ElementTag where
  show TagEmpty = "TagEmpty"
  show TagRectangle = "TagRectangle"
  show TagEllipse = "TagEllipse"
  show TagPath = "TagPath"
  show TagText = "TagText"
  show TagGroup = "TagGroup"
  show TagTransform = "TagTransform"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Magic number: "ELEM" in little-endian (0x4D454C45)
magic :: Int
magic = 0x4D454C45

-- | Current wire format version
version :: Int
version = 1

-- | Header size in bytes (16 bytes)
headerSize :: Int
headerSize = 16

-- | Tag byte values
tagToInt :: ElementTag -> Int
tagToInt TagEmpty = 0
tagToInt TagRectangle = 1
tagToInt TagEllipse = 2
tagToInt TagPath = 3
tagToInt TagText = 4
tagToInt TagGroup = 5
tagToInt TagTransform = 6

intToTag :: Int -> Maybe ElementTag
intToTag 0 = Just TagEmpty
intToTag 1 = Just TagRectangle
intToTag 2 = Just TagEllipse
intToTag 3 = Just TagPath
intToTag 4 = Just TagText
intToTag 5 = Just TagGroup
intToTag 6 = Just TagTransform
intToTag _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // byte utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Bytes to raw array
toByteArray :: Bytes -> Array Int
toByteArray (Bytes arr) = arr

-- | Create Bytes from raw array
fromByteArray :: Array Int -> Bytes
fromByteArray = Bytes

-- | Get byte count
bytesLength :: Bytes -> Int
bytesLength (Bytes arr) = Array.length arr

-- | Concatenate byte arrays
concatBytes :: Bytes -> Bytes -> Bytes
concatBytes (Bytes a) (Bytes b) = Bytes (a <> b)

-- | Empty bytes
emptyBytes :: Bytes
emptyBytes = Bytes []

-- | Write u32 little-endian (4 bytes)
writeU32 :: Int -> Bytes
writeU32 n =
  let b0 = n .&. 0xFF
      b1 = (shr n 8) .&. 0xFF
      b2 = (shr n 16) .&. 0xFF
      b3 = (shr n 24) .&. 0xFF
  in Bytes [b0, b1, b2, b3]

-- | Read u32 little-endian
readU32 :: Array Int -> Int -> Maybe Int
readU32 arr offset = do
  b0 <- Array.index arr offset
  b1 <- Array.index arr (offset + 1)
  b2 <- Array.index arr (offset + 2)
  b3 <- Array.index arr (offset + 3)
  pure (b0 .|. (shl b1 8) .|. (shl b2 16) .|. (shl b3 24))

-- | Write u8 (1 byte)
writeU8 :: Int -> Bytes
writeU8 n = Bytes [n .&. 0xFF]

-- | Read u8
readU8 :: Array Int -> Int -> Maybe Int
readU8 arr offset = Array.index arr offset

-- | Write f32 as 4 bytes (IEEE 754)
-- | Note: Uses integer approximation. Full impl would use FFI Float32Array.
writeF32 :: Number -> Bytes
writeF32 n =
  -- Encode as fixed-point: multiply by 256 to preserve some precision
  let scaled = floor (n * 256.0)
      b0 = scaled .&. 0xFF
      b1 = (shr scaled 8) .&. 0xFF
      b2 = (shr scaled 16) .&. 0xFF
      b3 = (shr scaled 24) .&. 0xFF
  in Bytes [b0, b1, b2, b3]

-- | Read f32 from 4 bytes
readF32 :: Array Int -> Int -> Maybe Number
readF32 arr offset = do
  v <- readU32 arr offset
  pure (toNumber v / 256.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unwrap Pixel to Number
unwrapPixel :: Device.Pixel -> Number
unwrapPixel (Device.Pixel n) = n

-- | Convert Radius to Number (pixels)
radiusToNumber :: Radius.Radius -> Number
radiusToNumber = case _ of
  Radius.RadiusPx n -> n
  Radius.RadiusPercent n -> n  -- Runtime resolves to pixels
  Radius.RadiusRem n -> n * 16.0  -- Assume 16px base
  Radius.RadiusFull -> 9999.0
  Radius.RadiusNone -> 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // header serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize header
serializeHeader :: Header -> Bytes
serializeHeader h =
  concatBytes (writeU32 h.magic) $
  concatBytes (writeU32 h.version) $
  concatBytes (writeU32 h.size) $
  writeU32 h.checksum

-- | Deserialize header
deserializeHeader :: Array Int -> Maybe Header
deserializeHeader arr = do
  m <- readU32 arr 0
  v <- readU32 arr 4
  s <- readU32 arr 8
  c <- readU32 arr 12
  if m == magic && v == version
    then Just { magic: m, version: v, size: s, checksum: c }
    else Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // element serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize a complete Element with header
serialize :: Element -> Bytes
serialize elem =
  let body = serializeElement elem
      size = headerSize + bytesLength body
      header = serializeHeader { magic, version, size, checksum: 0 }
  in concatBytes header body

-- | Serialize Element without header (for recursive use)
serializeElement :: Element -> Bytes
serializeElement Empty =
  writeU8 (tagToInt TagEmpty)

serializeElement (Rectangle spec) =
  concatBytes (writeU8 (tagToInt TagRectangle)) $
  serializeRectangleSpec spec

serializeElement (Ellipse spec) =
  concatBytes (writeU8 (tagToInt TagEllipse)) $
  serializeEllipseSpec spec

serializeElement (Path spec) =
  concatBytes (writeU8 (tagToInt TagPath)) $
  serializePathSpec spec

serializeElement (Group spec) =
  concatBytes (writeU8 (tagToInt TagGroup)) $
  serializeGroupSpec spec

serializeElement (Transform spec) =
  concatBytes (writeU8 (tagToInt TagTransform)) $
  serializeTransformSpec spec

serializeElement (Text spec) =
  concatBytes (writeU8 (tagToInt TagText)) $
  serializeTextSpec spec

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // rectangle serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize RectangleSpec
serializeRectangleSpec :: RectangleSpec -> Bytes
serializeRectangleSpec spec =
  concatBytes (serializeRectangleShape spec.shape) $
  concatBytes (serializeFill spec.fill) $
  concatBytes (serializeMaybeStroke spec.stroke) $
  serializeOpacity spec.opacity

-- | Serialize RectangleShape
serializeRectangleShape :: Shape.RectangleShape -> Bytes
serializeRectangleShape shape =
  concatBytes (serializePixelPoint2D shape.center) $
  concatBytes (writeF32 (unwrapPixel shape.width)) $
  concatBytes (writeF32 (unwrapPixel shape.height)) $
  serializeCorners shape.corners

-- | Serialize PixelPoint2D (8 bytes)
serializePixelPoint2D :: Shape.PixelPoint2D -> Bytes
serializePixelPoint2D pt =
  concatBytes (writeF32 (unwrapPixel pt.x)) $
  writeF32 (unwrapPixel pt.y)

-- | Serialize corner radii (16 bytes: 4 corners × 4 bytes each)
serializeCorners :: Radius.Corners -> Bytes
serializeCorners corners =
  concatBytes (writeF32 (radiusToNumber corners.topLeft)) $
  concatBytes (writeF32 (radiusToNumber corners.topRight)) $
  concatBytes (writeF32 (radiusToNumber corners.bottomRight)) $
  writeF32 (radiusToNumber corners.bottomLeft)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // ellipse serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize EllipseSpec
serializeEllipseSpec :: EllipseSpec -> Bytes
serializeEllipseSpec spec =
  concatBytes (serializeEllipseShape spec.shape) $
  concatBytes (serializeFill spec.fill) $
  concatBytes (serializeMaybeStroke spec.stroke) $
  serializeOpacity spec.opacity

-- | Serialize EllipseShape (16 bytes)
serializeEllipseShape :: Shape.EllipseShape -> Bytes
serializeEllipseShape shape =
  concatBytes (serializePixelPoint2D shape.center) $
  concatBytes (writeF32 (unwrapPixel shape.radiusX)) $
  writeF32 (unwrapPixel shape.radiusY)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // path serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize PathSpec
serializePathSpec :: PathSpec -> Bytes
serializePathSpec spec =
  concatBytes (serializePathShape spec.shape) $
  concatBytes (serializeFill spec.fill) $
  concatBytes (serializeMaybeStroke spec.stroke) $
  serializeOpacity spec.opacity

-- | Serialize PathShape
serializePathShape :: Shape.PathShape -> Bytes
serializePathShape shape =
  let
    windingByte = case shape.windingRule of
      Shape.WindingNonZero -> writeU8 0
      Shape.WindingEvenOdd -> writeU8 1
    countBytes = writeU32 (Array.length shape.commands)
    commandBytes = serializePathCommands shape.commands
  in
    concatBytes windingByte $
    concatBytes countBytes $
    commandBytes

-- | Serialize array of PathCommands
serializePathCommands :: Array Shape.PathCommand -> Bytes
serializePathCommands cmds =
  Array.foldl (\acc cmd -> concatBytes acc (serializePathCommand cmd)) emptyBytes cmds

-- | Serialize single PathCommand
serializePathCommand :: Shape.PathCommand -> Bytes
serializePathCommand = case _ of
  Shape.MoveTo pt ->
    concatBytes (writeU8 0) (serializePixelPoint2D pt)
  Shape.LineTo pt ->
    concatBytes (writeU8 1) (serializePixelPoint2D pt)
  Shape.CubicTo cp1 cp2 end ->
    concatBytes (writeU8 2) $
    concatBytes (serializePixelPoint2D cp1) $
    concatBytes (serializePixelPoint2D cp2) $
    serializePixelPoint2D end
  Shape.QuadraticTo cp end ->
    concatBytes (writeU8 3) $
    concatBytes (serializePixelPoint2D cp) $
    serializePixelPoint2D end
  Shape.ClosePath ->
    writeU8 4
  Shape.HorizontalTo x ->
    concatBytes (writeU8 5) (writeF32 (unwrapPixel x))
  Shape.VerticalTo y ->
    concatBytes (writeU8 6) (writeF32 (unwrapPixel y))
  Shape.ArcTo params endPt ->
    concatBytes (writeU8 7) $
    concatBytes (serializeArcParams params) $
    serializePixelPoint2D endPt

-- | Serialize ArcParams
serializeArcParams :: Shape.ArcParams -> Bytes
serializeArcParams params =
  concatBytes (writeF32 (unwrapPixel params.radiusX)) $
  concatBytes (writeF32 (unwrapPixel params.radiusY)) $
  concatBytes (writeF32 params.rotation) $
  concatBytes (writeU8 (if params.largeArc then 1 else 0)) $
  writeU8 (if params.sweep then 1 else 0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // group serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize GroupSpec
serializeGroupSpec :: GroupSpec -> Bytes
serializeGroupSpec spec =
  concatBytes (writeU32 (Array.length spec.children)) $
  concatBytes (serializeElements spec.children) $
  serializeOpacity spec.opacity

-- | Serialize array of Elements
serializeElements :: Array Element -> Bytes
serializeElements elems =
  Array.foldl (\acc elem -> concatBytes acc (serializeElement elem)) emptyBytes elems

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // transform serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize TransformSpec
serializeTransformSpec :: TransformSpec -> Bytes
serializeTransformSpec spec =
  concatBytes (serializeTransform2D spec.transform) $
  serializeElement spec.child

-- | Serialize Transform2D
-- | Layout: translateX (4) + translateY (4) + scaleX (4) + scaleY (4) +
-- |         rotation (4) + skewX (4) + skewY (4) + originX (4) + originY (4) = 36 bytes
serializeTransform2D :: Transform.Transform2D -> Bytes
serializeTransform2D (Transform.Transform2D t) =
  let
    -- Extract translate values (default to 0)
    Tuple tx ty = case t.translate of
      Nothing -> Tuple 0.0 0.0
      Just (Transform.Translate tr) -> Tuple tr.x tr.y
    
    -- Extract scale values (default to 1)
    Tuple sx sy = case t.scale of
      Nothing -> Tuple 1.0 1.0
      Just (Transform.Scale sc) -> Tuple sc.x sc.y
    
    -- Extract rotation (default to 0)
    rot = case t.rotate of
      Nothing -> 0.0
      Just (Transform.Rotate r) -> unwrapDegrees r.angle
    
    -- Extract skew values (default to 0)
    Tuple skx sky = case t.skew of
      Nothing -> Tuple 0.0 0.0
      Just (Transform.Skew sk) -> Tuple sk.x sk.y
    
    -- Extract origin (percentages 0-100)
    Transform.Origin orig = t.origin
  in
    concatBytes (writeF32 tx) $
    concatBytes (writeF32 ty) $
    concatBytes (writeF32 sx) $
    concatBytes (writeF32 sy) $
    concatBytes (writeF32 rot) $
    concatBytes (writeF32 skx) $
    concatBytes (writeF32 sky) $
    concatBytes (writeF32 orig.x) $
    writeF32 orig.y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // text serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize TextSpec
-- |
-- | Layout:
-- |   glyphCount (u32) + glyphs (variable) + opacity (f32)
serializeTextSpec :: TextSpec -> Bytes
serializeTextSpec spec =
  let glyphCount = writeU32 (Array.length spec.glyphs)
      glyphBytes = serializeGlyphArray spec.glyphs
  in concatBytes glyphCount $
     concatBytes glyphBytes $
     serializeOpacity spec.opacity

-- | Serialize array of GlyphSpec
serializeGlyphArray :: Array GlyphSpec -> Bytes
serializeGlyphArray glyphs =
  Array.foldl (\acc g -> concatBytes acc (serializeGlyph g)) emptyBytes glyphs

-- | Serialize single GlyphSpec
-- |
-- | Layout:
-- |   glyphPath (variable) + transform2D (36) + fill (variable) + 
-- |   maybeStroke (variable) + opacity (4) + progress (4)
serializeGlyph :: GlyphSpec -> Bytes
serializeGlyph spec =
  concatBytes (serializeGlyphPath spec.glyph) $
  concatBytes (serializeTransform2D spec.transform) $
  concatBytes (serializeFill spec.fill) $
  concatBytes (serializeMaybeStroke spec.stroke) $
  concatBytes (serializeOpacity spec.opacity) $
  serializeProgress spec.progress

-- | Serialize Progress (4 bytes as f32)
serializeProgress :: Progress.Progress -> Bytes
serializeProgress p = writeF32 (Progress.unwrapProgress p)

-- | Serialize GlyphPath
-- |
-- | Layout:
-- |   contourCount (u32) + contours (variable) + bounds (24) +
-- |   advanceWidth (4) + leftSideBearing (4)
serializeGlyphPath :: Glyph.GlyphPath -> Bytes
serializeGlyphPath gp =
  let contourCount = writeU32 (Array.length gp.contours)
      contourBytes = serializeContours gp.contours
  in concatBytes contourCount $
     concatBytes contourBytes $
     concatBytes (serializeGlyphBounds gp.bounds) $
     concatBytes (writeF32 (unwrapPixel gp.advanceWidth)) $
     writeF32 (unwrapPixel gp.leftSideBearing)

-- | Serialize array of Contours
serializeContours :: Array Glyph.Contour -> Bytes
serializeContours contours =
  Array.foldl (\acc c -> concatBytes acc (serializeContour c)) emptyBytes contours

-- | Serialize single Contour
-- |
-- | Layout:
-- |   winding (u8) + commandCount (u32) + commands (variable)
serializeContour :: Glyph.Contour -> Bytes
serializeContour c =
  let windingByte = case c.winding of
        Glyph.WindingClockwise -> writeU8 0
        Glyph.WindingCounterClockwise -> writeU8 1
      commandCount = writeU32 (Array.length c.commands)
      commandBytes = serializePathCommands3D c.commands
  in concatBytes windingByte $
     concatBytes commandCount $
     commandBytes

-- | Serialize array of 3D path commands
serializePathCommands3D :: Array Glyph.PathCommand3D -> Bytes
serializePathCommands3D cmds =
  Array.foldl (\acc cmd -> concatBytes acc (serializePathCommand3D cmd)) emptyBytes cmds

-- | Serialize single 3D path command
-- |
-- | Tags:
-- |   0 = MoveTo3D (12 bytes: x, y, z)
-- |   1 = LineTo3D (12 bytes)
-- |   2 = QuadraticTo3D (24 bytes: control + end)
-- |   3 = CubicTo3D (36 bytes: c1 + c2 + end)
-- |   4 = ClosePath3D (0 bytes)
serializePathCommand3D :: Glyph.PathCommand3D -> Bytes
serializePathCommand3D = case _ of
  Glyph.MoveTo3D p ->
    concatBytes (writeU8 0) (serializeControlPoint3D p)
  Glyph.LineTo3D p ->
    concatBytes (writeU8 1) (serializeControlPoint3D p)
  Glyph.QuadraticTo3D c1 end ->
    concatBytes (writeU8 2) $
    concatBytes (serializeControlPoint3D c1) $
    serializeControlPoint3D end
  Glyph.CubicTo3D c1 c2 end ->
    concatBytes (writeU8 3) $
    concatBytes (serializeControlPoint3D c1) $
    concatBytes (serializeControlPoint3D c2) $
    serializeControlPoint3D end
  Glyph.ClosePath3D ->
    writeU8 4

-- | Serialize ControlPoint3D (12 bytes: x, y, z as f32)
serializeControlPoint3D :: Glyph.ControlPoint3D -> Bytes
serializeControlPoint3D pt =
  concatBytes (writeF32 (unwrapPixel pt.x)) $
  concatBytes (writeF32 (unwrapPixel pt.y)) $
  writeF32 (unwrapPixel pt.z)

-- | Serialize GlyphBounds (24 bytes: 6 × f32)
serializeGlyphBounds :: Glyph.GlyphBounds -> Bytes
serializeGlyphBounds b =
  concatBytes (writeF32 (unwrapPixel b.minX)) $
  concatBytes (writeF32 (unwrapPixel b.maxX)) $
  concatBytes (writeF32 (unwrapPixel b.minY)) $
  concatBytes (writeF32 (unwrapPixel b.maxY)) $
  concatBytes (writeF32 (unwrapPixel b.minZ)) $
  writeF32 (unwrapPixel b.maxZ)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // fill serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Fill (tag + payload)
serializeFill :: Fill.Fill -> Bytes
serializeFill = case _ of
  Fill.FillNone -> 
    writeU8 0
  Fill.FillSolid color ->
    concatBytes (writeU8 1) (serializeRGB color)
  Fill.FillGradient _ ->
    -- Gradient: placeholder, full impl would serialize stops
    writeU8 2
  Fill.FillPattern _ ->
    writeU8 3
  Fill.FillNoise _ ->
    writeU8 4

-- | Serialize RGB color (3 bytes: r, g, b as u8)
serializeRGB :: RGB.RGB -> Bytes
serializeRGB color =
  let r = Channel.unwrap (RGB.red color)
      g = Channel.unwrap (RGB.green color)
      b = Channel.unwrap (RGB.blue color)
  in Bytes [r, g, b]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // stroke serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize Maybe StrokeSpec
serializeMaybeStroke :: Maybe StrokeSpec -> Bytes
serializeMaybeStroke = case _ of
  Nothing -> writeU8 0
  Just s -> concatBytes (writeU8 1) (serializeStrokeSpec s)

-- | Serialize StrokeSpec
serializeStrokeSpec :: StrokeSpec -> Bytes
serializeStrokeSpec spec =
  concatBytes (writeF32 (Stroke.strokeWidthValue spec.width)) $
  concatBytes (serializeFill spec.fill) $
  concatBytes (serializeLineCap spec.cap) $
  concatBytes (serializeLineJoin spec.join) $
  concatBytes (writeF32 (GeomStroke.miterLimitValue spec.miterLimit)) $
  concatBytes (serializeDashPattern spec.dashPattern) $
  serializeOpacity spec.opacity

-- | Serialize LineCap (1 byte)
serializeLineCap :: GeomStroke.LineCap -> Bytes
serializeLineCap = case _ of
  GeomStroke.CapButt -> writeU8 0
  GeomStroke.CapRound -> writeU8 1
  GeomStroke.CapSquare -> writeU8 2

-- | Serialize LineJoin (1 byte)
serializeLineJoin :: GeomStroke.LineJoin -> Bytes
serializeLineJoin = case _ of
  GeomStroke.JoinMiter -> writeU8 0
  GeomStroke.JoinRound -> writeU8 1
  GeomStroke.JoinBevel -> writeU8 2

-- | Serialize DashPattern
serializeDashPattern :: Stroke.DashPattern -> Bytes
serializeDashPattern pattern =
  let dashes = Stroke.dashPatternSegments pattern
      countBytes = writeU32 (Array.length dashes)
      dashBytes = Array.foldl
        (\acc d -> concatBytes acc (writeF32 d))
        emptyBytes
        dashes
  in concatBytes countBytes dashBytes

-- | Serialize Opacity (4 bytes as f32)
serializeOpacity :: Opacity.Opacity -> Bytes
serializeOpacity op = writeF32 (toNumber (Opacity.unwrap op))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // element deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of deserialization: the value and bytes consumed
type DeserializeResult a = { value :: a, bytesRead :: Int }

-- | Deserialize Element with header
deserialize :: Bytes -> Maybe Element
deserialize (Bytes arr) = do
  header <- deserializeHeader arr
  if header.magic == magic && header.version == version
    then do
      result <- deserializeElementAt arr headerSize
      pure result.value
    else Nothing

-- | Deserialize Element at offset, returning value and bytes consumed
deserializeElement :: Array Int -> Int -> Maybe Element
deserializeElement arr offset = do
  result <- deserializeElementAt arr offset
  pure result.value

-- | Deserialize Element at offset with byte count tracking
deserializeElementAt :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeElementAt arr offset = do
  tag <- readU8 arr offset
  tagEnum <- intToTag tag
  case tagEnum of
    TagEmpty -> 
      Just { value: Empty, bytesRead: 1 }
    TagRectangle -> 
      deserializeRectangle arr (offset + 1)
    TagEllipse -> 
      deserializeEllipse arr (offset + 1)
    TagPath -> 
      deserializePath arr (offset + 1)
    TagText ->
      deserializeText arr (offset + 1)
    TagGroup -> 
      deserializeGroup arr (offset + 1)
    TagTransform -> 
      deserializeTransformElem arr (offset + 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // rectangle deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Rectangle at offset
deserializeRectangle :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeRectangle arr offset = do
  -- RectangleShape: center (8) + width (4) + height (4) + corners (16) = 32 bytes
  shapeResult <- deserializeRectangleShape arr offset
  let shapeEnd = offset + shapeResult.bytesRead
  
  -- Fill (variable)
  fillResult <- deserializeFillAt arr shapeEnd
  let fillEnd = shapeEnd + fillResult.bytesRead
  
  -- Maybe Stroke
  strokeResult <- deserializeMaybeStroke arr fillEnd
  let strokeEnd = fillEnd + strokeResult.bytesRead
  
  -- Opacity (4)
  opacity <- deserializeOpacity arr strokeEnd
  
  let spec = 
        { shape: shapeResult.value
        , fill: fillResult.value
        , stroke: strokeResult.value
        , opacity: opacity
        }
  
  Just { value: Rectangle spec, bytesRead: strokeEnd + 4 - offset }

-- | Deserialize RectangleShape
deserializeRectangleShape :: Array Int -> Int -> Maybe (DeserializeResult Shape.RectangleShape)
deserializeRectangleShape arr offset = do
  -- center (8 bytes)
  center <- deserializePixelPoint2D arr offset
  -- width (4 bytes)
  width <- readF32 arr (offset + 8)
  -- height (4 bytes)
  height <- readF32 arr (offset + 12)
  -- corners (16 bytes)
  corners <- deserializeCorners arr (offset + 16)
  
  let shape = 
        { center: center
        , width: Device.Pixel width
        , height: Device.Pixel height
        , corners: corners
        }
  
  Just { value: shape, bytesRead: 32 }

-- | Deserialize PixelPoint2D (8 bytes)
deserializePixelPoint2D :: Array Int -> Int -> Maybe Shape.PixelPoint2D
deserializePixelPoint2D arr offset = do
  x <- readF32 arr offset
  y <- readF32 arr (offset + 4)
  Just { x: Device.Pixel x, y: Device.Pixel y }

-- | Deserialize Corners (16 bytes)
deserializeCorners :: Array Int -> Int -> Maybe Radius.Corners
deserializeCorners arr offset = do
  tl <- readF32 arr offset
  tr <- readF32 arr (offset + 4)
  br <- readF32 arr (offset + 8)
  bl <- readF32 arr (offset + 12)
  Just 
    { topLeft: Radius.RadiusPx tl
    , topRight: Radius.RadiusPx tr
    , bottomRight: Radius.RadiusPx br
    , bottomLeft: Radius.RadiusPx bl
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // ellipse deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Ellipse at offset
deserializeEllipse :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeEllipse arr offset = do
  -- EllipseShape: center (8) + radiusX (4) + radiusY (4) = 16 bytes
  shapeResult <- deserializeEllipseShape arr offset
  let shapeEnd = offset + shapeResult.bytesRead
  
  -- Fill (variable)
  fillResult <- deserializeFillAt arr shapeEnd
  let fillEnd = shapeEnd + fillResult.bytesRead
  
  -- Maybe Stroke
  strokeResult <- deserializeMaybeStroke arr fillEnd
  let strokeEnd = fillEnd + strokeResult.bytesRead
  
  -- Opacity (4)
  opacity <- deserializeOpacity arr strokeEnd
  
  let spec = 
        { shape: shapeResult.value
        , fill: fillResult.value
        , stroke: strokeResult.value
        , opacity: opacity
        }
  
  Just { value: Ellipse spec, bytesRead: strokeEnd + 4 - offset }

-- | Deserialize EllipseShape (16 bytes)
deserializeEllipseShape :: Array Int -> Int -> Maybe (DeserializeResult Shape.EllipseShape)
deserializeEllipseShape arr offset = do
  center <- deserializePixelPoint2D arr offset
  rx <- readF32 arr (offset + 8)
  ry <- readF32 arr (offset + 12)
  
  let shape = 
        { center: center
        , radiusX: Device.Pixel rx
        , radiusY: Device.Pixel ry
        }
  
  Just { value: shape, bytesRead: 16 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // path deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Path at offset
deserializePath :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializePath arr offset = do
  -- PathShape: windingRule (1) + commandCount (4) + commands (variable)
  shapeResult <- deserializePathShape arr offset
  let shapeEnd = offset + shapeResult.bytesRead
  
  -- Fill (variable)
  fillResult <- deserializeFillAt arr shapeEnd
  let fillEnd = shapeEnd + fillResult.bytesRead
  
  -- Maybe Stroke
  strokeResult <- deserializeMaybeStroke arr fillEnd
  let strokeEnd = fillEnd + strokeResult.bytesRead
  
  -- Opacity (4)
  opacity <- deserializeOpacity arr strokeEnd
  
  let spec = 
        { shape: shapeResult.value
        , fill: fillResult.value
        , stroke: strokeResult.value
        , opacity: opacity
        }
  
  Just { value: Path spec, bytesRead: strokeEnd + 4 - offset }

-- | Deserialize PathShape
deserializePathShape :: Array Int -> Int -> Maybe (DeserializeResult Shape.PathShape)
deserializePathShape arr offset = do
  -- Winding rule (1 byte)
  windingByte <- readU8 arr offset
  let winding = if windingByte == 0 then Shape.WindingNonZero else Shape.WindingEvenOdd
  
  -- Command count (4 bytes)
  count <- readU32 arr (offset + 1)
  
  -- Commands (variable)
  commandsResult <- deserializePathCommands arr (offset + 5) count
  
  let shape = 
        { commands: commandsResult.value
        , windingRule: winding
        , closed: count > 0
        }
  
  Just { value: shape, bytesRead: 5 + commandsResult.bytesRead }

-- | Deserialize array of PathCommands
deserializePathCommands :: Array Int -> Int -> Int -> Maybe (DeserializeResult (Array Shape.PathCommand))
deserializePathCommands arr offset count = 
  deserializePathCommandsLoop arr offset count []

-- | Helper for deserializing path commands
deserializePathCommandsLoop 
  :: Array Int 
  -> Int 
  -> Int 
  -> Array Shape.PathCommand 
  -> Maybe (DeserializeResult (Array Shape.PathCommand))
deserializePathCommandsLoop arr offset remaining acc =
  if remaining == 0
    then Just { value: acc, bytesRead: 0 }
    else do
      cmdResult <- deserializePathCommand arr offset
      restResult <- deserializePathCommandsLoop arr (offset + cmdResult.bytesRead) (remaining - 1) (acc <> [cmdResult.value])
      Just { value: restResult.value, bytesRead: cmdResult.bytesRead + restResult.bytesRead }

-- | Deserialize single PathCommand
deserializePathCommand :: Array Int -> Int -> Maybe (DeserializeResult Shape.PathCommand)
deserializePathCommand arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> do -- MoveTo
      pt <- deserializePixelPoint2D arr (offset + 1)
      Just { value: Shape.MoveTo pt, bytesRead: 9 }
    1 -> do -- LineTo
      pt <- deserializePixelPoint2D arr (offset + 1)
      Just { value: Shape.LineTo pt, bytesRead: 9 }
    2 -> do -- CubicTo
      cp1 <- deserializePixelPoint2D arr (offset + 1)
      cp2 <- deserializePixelPoint2D arr (offset + 9)
      end <- deserializePixelPoint2D arr (offset + 17)
      Just { value: Shape.CubicTo cp1 cp2 end, bytesRead: 25 }
    3 -> do -- QuadraticTo
      cp <- deserializePixelPoint2D arr (offset + 1)
      end <- deserializePixelPoint2D arr (offset + 9)
      Just { value: Shape.QuadraticTo cp end, bytesRead: 17 }
    4 -> -- ClosePath
      Just { value: Shape.ClosePath, bytesRead: 1 }
    5 -> do -- HorizontalTo
      x <- readF32 arr (offset + 1)
      Just { value: Shape.HorizontalTo (Device.Pixel x), bytesRead: 5 }
    6 -> do -- VerticalTo
      y <- readF32 arr (offset + 1)
      Just { value: Shape.VerticalTo (Device.Pixel y), bytesRead: 5 }
    7 -> do -- ArcTo
      arcResult <- deserializeArcParams arr (offset + 1)
      endPt <- deserializePixelPoint2D arr (offset + 1 + arcResult.bytesRead)
      Just { value: Shape.ArcTo arcResult.value endPt, bytesRead: 1 + arcResult.bytesRead + 8 }
    _ -> Nothing

-- | Deserialize ArcParams
deserializeArcParams :: Array Int -> Int -> Maybe (DeserializeResult Shape.ArcParams)
deserializeArcParams arr offset = do
  rx <- readF32 arr offset
  ry <- readF32 arr (offset + 4)
  rotation <- readF32 arr (offset + 8)
  largeArcByte <- readU8 arr (offset + 12)
  sweepByte <- readU8 arr (offset + 13)
  
  let params = 
        { radiusX: Device.Pixel rx
        , radiusY: Device.Pixel ry
        , rotation: rotation
        , largeArc: largeArcByte /= 0
        , sweep: sweepByte /= 0
        }
  
  Just { value: params, bytesRead: 14 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // text deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Text at offset
deserializeText :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeText arr offset = do
  -- Glyph count (4 bytes)
  glyphCount <- readU32 arr offset
  
  -- Glyphs (variable)
  glyphsResult <- deserializeGlyphs arr (offset + 4) glyphCount
  let glyphsEnd = offset + 4 + glyphsResult.bytesRead
  
  -- Opacity (4 bytes)
  opacity <- deserializeOpacity arr glyphsEnd
  
  let spec =
        { glyphs: glyphsResult.value
        , opacity: opacity
        }
  
  Just { value: Text spec, bytesRead: glyphsEnd + 4 - offset }

-- | Deserialize array of GlyphSpec
deserializeGlyphs :: Array Int -> Int -> Int -> Maybe (DeserializeResult (Array GlyphSpec))
deserializeGlyphs arr offset count =
  deserializeGlyphsLoop arr offset count []

-- | Helper loop for glyph deserialization
deserializeGlyphsLoop 
  :: Array Int 
  -> Int 
  -> Int 
  -> Array GlyphSpec 
  -> Maybe (DeserializeResult (Array GlyphSpec))
deserializeGlyphsLoop arr offset remaining acc =
  if remaining == 0
    then Just { value: acc, bytesRead: 0 }
    else do
      glyphResult <- deserializeGlyph arr offset
      let newOffset = offset + glyphResult.bytesRead
      restResult <- deserializeGlyphsLoop arr newOffset (remaining - 1) (Array.snoc acc glyphResult.value)
      pure { value: restResult.value, bytesRead: glyphResult.bytesRead + restResult.bytesRead }

-- | Deserialize single GlyphSpec
deserializeGlyph :: Array Int -> Int -> Maybe (DeserializeResult GlyphSpec)
deserializeGlyph arr offset = do
  -- GlyphPath (variable)
  glyphPathResult <- deserializeGlyphPath arr offset
  let glyphPathEnd = offset + glyphPathResult.bytesRead
  
  -- Transform2D (36 bytes)
  transform <- deserializeTransform2D arr glyphPathEnd
  let transformEnd = glyphPathEnd + 36
  
  -- Fill (variable)
  fillResult <- deserializeFillAt arr transformEnd
  let fillEnd = transformEnd + fillResult.bytesRead
  
  -- Maybe Stroke (variable)
  strokeResult <- deserializeMaybeStroke arr fillEnd
  let strokeEnd = fillEnd + strokeResult.bytesRead
  
  -- Opacity (4 bytes)
  opacity <- deserializeOpacity arr strokeEnd
  let opacityEnd = strokeEnd + 4
  
  -- Progress (4 bytes)
  progressVal <- readF32 arr opacityEnd
  
  let spec =
        { glyph: glyphPathResult.value
        , transform: transform
        , fill: fillResult.value
        , stroke: strokeResult.value
        , opacity: opacity
        , progress: Progress.progress progressVal
        }
  
  Just { value: spec, bytesRead: opacityEnd + 4 - offset }

-- | Deserialize GlyphPath
deserializeGlyphPath :: Array Int -> Int -> Maybe (DeserializeResult Glyph.GlyphPath)
deserializeGlyphPath arr offset = do
  -- Contour count (4 bytes)
  contourCount <- readU32 arr offset
  
  -- Contours (variable)
  contoursResult <- deserializeContours arr (offset + 4) contourCount
  let contoursEnd = offset + 4 + contoursResult.bytesRead
  
  -- Bounds (24 bytes)
  bounds <- deserializeGlyphBounds arr contoursEnd
  let boundsEnd = contoursEnd + 24
  
  -- Advance width (4 bytes)
  advanceWidth <- readF32 arr boundsEnd
  
  -- Left side bearing (4 bytes)
  leftSideBearing <- readF32 arr (boundsEnd + 4)
  
  let gp =
        { contours: contoursResult.value
        , bounds: bounds
        , advanceWidth: Device.Pixel advanceWidth
        , leftSideBearing: Device.Pixel leftSideBearing
        }
  
  Just { value: gp, bytesRead: boundsEnd + 8 - offset }

-- | Deserialize array of Contours
deserializeContours :: Array Int -> Int -> Int -> Maybe (DeserializeResult (Array Glyph.Contour))
deserializeContours arr offset count =
  deserializeContoursLoop arr offset count []

-- | Helper loop for contour deserialization
deserializeContoursLoop 
  :: Array Int 
  -> Int 
  -> Int 
  -> Array Glyph.Contour 
  -> Maybe (DeserializeResult (Array Glyph.Contour))
deserializeContoursLoop arr offset remaining acc =
  if remaining == 0
    then Just { value: acc, bytesRead: 0 }
    else do
      contourResult <- deserializeContour arr offset
      let newOffset = offset + contourResult.bytesRead
      restResult <- deserializeContoursLoop arr newOffset (remaining - 1) (Array.snoc acc contourResult.value)
      pure { value: restResult.value, bytesRead: contourResult.bytesRead + restResult.bytesRead }

-- | Deserialize single Contour
deserializeContour :: Array Int -> Int -> Maybe (DeserializeResult Glyph.Contour)
deserializeContour arr offset = do
  -- Winding (1 byte)
  windingByte <- readU8 arr offset
  let winding = if windingByte == 0 
        then Glyph.WindingClockwise 
        else Glyph.WindingCounterClockwise
  
  -- Command count (4 bytes)
  commandCount <- readU32 arr (offset + 1)
  
  -- Commands (variable)
  commandsResult <- deserializePathCommands3D arr (offset + 5) commandCount
  
  let c = { commands: commandsResult.value, winding: winding }
  
  Just { value: c, bytesRead: 5 + commandsResult.bytesRead }

-- | Deserialize array of 3D path commands
deserializePathCommands3D :: Array Int -> Int -> Int -> Maybe (DeserializeResult (Array Glyph.PathCommand3D))
deserializePathCommands3D arr offset count =
  deserializePathCommands3DLoop arr offset count []

-- | Helper loop for 3D path command deserialization
deserializePathCommands3DLoop 
  :: Array Int 
  -> Int 
  -> Int 
  -> Array Glyph.PathCommand3D 
  -> Maybe (DeserializeResult (Array Glyph.PathCommand3D))
deserializePathCommands3DLoop arr offset remaining acc =
  if remaining == 0
    then Just { value: acc, bytesRead: 0 }
    else do
      cmdResult <- deserializePathCommand3D arr offset
      let newOffset = offset + cmdResult.bytesRead
      restResult <- deserializePathCommands3DLoop arr newOffset (remaining - 1) (Array.snoc acc cmdResult.value)
      pure { value: restResult.value, bytesRead: cmdResult.bytesRead + restResult.bytesRead }

-- | Deserialize single 3D path command
deserializePathCommand3D :: Array Int -> Int -> Maybe (DeserializeResult Glyph.PathCommand3D)
deserializePathCommand3D arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> do  -- MoveTo3D
      pt <- deserializeControlPoint3D arr (offset + 1)
      pure { value: Glyph.MoveTo3D pt, bytesRead: 13 }
    1 -> do  -- LineTo3D
      pt <- deserializeControlPoint3D arr (offset + 1)
      pure { value: Glyph.LineTo3D pt, bytesRead: 13 }
    2 -> do  -- QuadraticTo3D
      c1 <- deserializeControlPoint3D arr (offset + 1)
      end <- deserializeControlPoint3D arr (offset + 13)
      pure { value: Glyph.QuadraticTo3D c1 end, bytesRead: 25 }
    3 -> do  -- CubicTo3D
      c1 <- deserializeControlPoint3D arr (offset + 1)
      c2 <- deserializeControlPoint3D arr (offset + 13)
      end <- deserializeControlPoint3D arr (offset + 25)
      pure { value: Glyph.CubicTo3D c1 c2 end, bytesRead: 37 }
    4 ->     -- ClosePath3D
      pure { value: Glyph.ClosePath3D, bytesRead: 1 }
    _ -> Nothing

-- | Deserialize ControlPoint3D (12 bytes)
deserializeControlPoint3D :: Array Int -> Int -> Maybe Glyph.ControlPoint3D
deserializeControlPoint3D arr offset = do
  x <- readF32 arr offset
  y <- readF32 arr (offset + 4)
  z <- readF32 arr (offset + 8)
  pure (Glyph.controlPoint3D (Device.Pixel x) (Device.Pixel y) (Device.Pixel z))

-- | Deserialize GlyphBounds (24 bytes)
deserializeGlyphBounds :: Array Int -> Int -> Maybe Glyph.GlyphBounds
deserializeGlyphBounds arr offset = do
  minX <- readF32 arr offset
  maxX <- readF32 arr (offset + 4)
  minY <- readF32 arr (offset + 8)
  maxY <- readF32 arr (offset + 12)
  minZ <- readF32 arr (offset + 16)
  maxZ <- readF32 arr (offset + 20)
  pure (Glyph.glyphBounds 
    (Device.Pixel minX) (Device.Pixel maxX)
    (Device.Pixel minY) (Device.Pixel maxY)
    (Device.Pixel minZ) (Device.Pixel maxZ))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // group deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Group at offset
deserializeGroup :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeGroup arr offset = do
  -- Child count (4 bytes)
  count <- readU32 arr offset
  
  -- Children (variable)
  childrenResult <- deserializeElements arr (offset + 4) count
  let childrenEnd = offset + 4 + childrenResult.bytesRead
  
  -- Opacity (4 bytes)
  opacity <- deserializeOpacity arr childrenEnd
  
  let spec = 
        { children: childrenResult.value
        , opacity: opacity
        }
  
  Just { value: Group spec, bytesRead: childrenEnd + 4 - offset }

-- | Deserialize array of Elements
deserializeElements :: Array Int -> Int -> Int -> Maybe (DeserializeResult (Array Element))
deserializeElements arr offset count =
  deserializeElementsLoop arr offset count []

-- | Helper for deserializing elements
deserializeElementsLoop 
  :: Array Int 
  -> Int 
  -> Int 
  -> Array Element 
  -> Maybe (DeserializeResult (Array Element))
deserializeElementsLoop arr offset remaining acc =
  if remaining == 0
    then Just { value: acc, bytesRead: 0 }
    else do
      elemResult <- deserializeElementAt arr offset
      restResult <- deserializeElementsLoop arr (offset + elemResult.bytesRead) (remaining - 1) (acc <> [elemResult.value])
      Just { value: restResult.value, bytesRead: elemResult.bytesRead + restResult.bytesRead }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // transform deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Transform at offset
deserializeTransformElem :: Array Int -> Int -> Maybe (DeserializeResult Element)
deserializeTransformElem arr offset = do
  -- Transform2D (36 bytes)
  transform <- deserializeTransform2D arr offset
  
  -- Child element (variable)
  childResult <- deserializeElementAt arr (offset + 36)
  
  let spec = 
        { transform: transform
        , child: childResult.value
        }
  
  Just { value: Transform spec, bytesRead: 36 + childResult.bytesRead }

-- | Deserialize Transform2D (36 bytes)
deserializeTransform2D :: Array Int -> Int -> Maybe Transform.Transform2D
deserializeTransform2D arr offset = do
  tx <- readF32 arr offset
  ty <- readF32 arr (offset + 4)
  sx <- readF32 arr (offset + 8)
  sy <- readF32 arr (offset + 12)
  rot <- readF32 arr (offset + 16)
  skx <- readF32 arr (offset + 20)
  sky <- readF32 arr (offset + 24)
  ox <- readF32 arr (offset + 28)
  oy <- readF32 arr (offset + 32)
  
  -- Reconstruct Transform2D from components
  let translate = if tx == 0.0 && ty == 0.0 
        then Nothing 
        else Just (Transform.Translate { x: tx, y: ty })
      
      scale = if sx == 1.0 && sy == 1.0 
        then Nothing 
        else Just (Transform.Scale { x: sx, y: sy })
      
      rotate = if rot == 0.0 
        then Nothing 
        else Just (Transform.Rotate { angle: degrees rot })
      
      skew = if skx == 0.0 && sky == 0.0 
        then Nothing 
        else Just (Transform.Skew { x: skx, y: sky })
      
      origin = Transform.Origin { x: ox, y: oy }
  
  Just (Transform.Transform2D { translate, rotate, scale, skew, origin })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // fill deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Fill at offset
deserializeFillAt :: Array Int -> Int -> Maybe (DeserializeResult Fill.Fill)
deserializeFillAt arr offset = do
  tag <- readU8 arr offset
  case tag of
    0 -> -- FillNone
      Just { value: Fill.FillNone, bytesRead: 1 }
    1 -> do -- FillSolid (RGB = 3 bytes)
      color <- deserializeRGB arr (offset + 1)
      Just { value: Fill.FillSolid color, bytesRead: 4 }
    2 -> -- FillGradient (not fully serialized yet)
      Just { value: Fill.FillNone, bytesRead: 1 }
    3 -> -- FillPattern (not fully serialized yet)
      Just { value: Fill.FillNone, bytesRead: 1 }
    4 -> -- FillNoise (not fully serialized yet)
      Just { value: Fill.FillNone, bytesRead: 1 }
    _ -> Nothing

-- | Deserialize RGB color (3 bytes)
deserializeRGB :: Array Int -> Int -> Maybe RGB.RGB
deserializeRGB arr offset = do
  r <- readU8 arr offset
  g <- readU8 arr (offset + 1)
  b <- readU8 arr (offset + 2)
  Just (RGB.rgb r g b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // stroke deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize Maybe StrokeSpec
deserializeMaybeStroke :: Array Int -> Int -> Maybe (DeserializeResult (Maybe StrokeSpec))
deserializeMaybeStroke arr offset = do
  hasStroke <- readU8 arr offset
  if hasStroke == 0
    then Just { value: Nothing, bytesRead: 1 }
    else do
      strokeResult <- deserializeStrokeSpec arr (offset + 1)
      Just { value: Just strokeResult.value, bytesRead: 1 + strokeResult.bytesRead }

-- | Deserialize StrokeSpec
deserializeStrokeSpec :: Array Int -> Int -> Maybe (DeserializeResult StrokeSpec)
deserializeStrokeSpec arr offset = do
  -- width (4)
  width <- readF32 arr offset
  
  -- fill (variable)
  fillResult <- deserializeFillAt arr (offset + 4)
  let afterFill = offset + 4 + fillResult.bytesRead
  
  -- cap (1)
  capByte <- readU8 arr afterFill
  let cap = case capByte of
        1 -> GeomStroke.CapRound
        2 -> GeomStroke.CapSquare
        _ -> GeomStroke.CapButt
  
  -- join (1)
  joinByte <- readU8 arr (afterFill + 1)
  let join = case joinByte of
        1 -> GeomStroke.JoinRound
        2 -> GeomStroke.JoinBevel
        _ -> GeomStroke.JoinMiter
  
  -- miterLimit (4)
  miterLimit <- readF32 arr (afterFill + 2)
  
  -- dashPattern (variable)
  dashResult <- deserializeDashPattern arr (afterFill + 6)
  let afterDash = afterFill + 6 + dashResult.bytesRead
  
  -- opacity (4)
  opacityVal <- readF32 arr afterDash
  
  let spec = 
        { width: Stroke.strokeWidth width
        , fill: fillResult.value
        , cap: cap
        , join: join
        , miterLimit: GeomStroke.miterLimit miterLimit
        , dashPattern: dashResult.value
        , opacity: Opacity.opacity (floor opacityVal)
        }
  
  Just { value: spec, bytesRead: afterDash + 4 - offset }

-- | Deserialize DashPattern
deserializeDashPattern :: Array Int -> Int -> Maybe (DeserializeResult Stroke.DashPattern)
deserializeDashPattern arr offset = do
  count <- readU32 arr offset
  segments <- deserializeDashSegments arr (offset + 4) count
  -- Convert raw Numbers (alternating dash/gap) to DashPattern
  let pairs = segmentsToPairs segments
      pattern = Stroke.dashPattern pairs
  Just { value: pattern, bytesRead: 4 + count * 4 }

-- | Convert flat array of segments [d1, g1, d2, g2, ...] to pairs
segmentsToPairs :: Array Number -> Array { dash :: Number, gap :: Number }
segmentsToPairs segments = segmentsToPairsLoop segments []

segmentsToPairsLoop :: Array Number -> Array { dash :: Number, gap :: Number } -> Array { dash :: Number, gap :: Number }
segmentsToPairsLoop segments acc =
  case Array.uncons segments of
    Nothing -> acc
    Just { head: dash, tail: rest1 } ->
      case Array.uncons rest1 of
        Nothing -> acc <> [{ dash: dash, gap: 0.0 }]  -- Odd element, default gap to 0
        Just { head: gap, tail: rest2 } ->
          segmentsToPairsLoop rest2 (acc <> [{ dash: dash, gap: gap }])

-- | Helper to deserialize dash segments
deserializeDashSegments :: Array Int -> Int -> Int -> Maybe (Array Number)
deserializeDashSegments arr offset count =
  deserializeDashLoop arr offset count []

deserializeDashLoop :: Array Int -> Int -> Int -> Array Number -> Maybe (Array Number)
deserializeDashLoop arr offset remaining acc =
  if remaining == 0
    then Just acc
    else do
      val <- readF32 arr offset
      deserializeDashLoop arr (offset + 4) (remaining - 1) (acc <> [val])

-- | Deserialize Opacity (4 bytes)
deserializeOpacity :: Array Int -> Int -> Maybe Opacity.Opacity
deserializeOpacity arr offset = do
  val <- readF32 arr offset
  Just (Opacity.opacity (floor val))
