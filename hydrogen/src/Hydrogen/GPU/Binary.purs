-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // gpu // binary
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Binary Serialization Format for GPU Commands
-- |
-- | This module defines the binary wire format for DrawCommands. Any GPU
-- | runtime that consumes Hydrogen output reads this format.
-- |
-- | ## Design Principles
-- |
-- | 1. **Fixed-size records**: Every command type has a known byte size.
-- |    No variable-length encoding on the hot path.
-- |
-- | 2. **Little-endian**: Matches WebGPU/native GPU expectations.
-- |
-- | 3. **Aligned**: All fields are naturally aligned (f32 on 4-byte, etc.)
-- |
-- | 4. **Deterministic**: Same DrawCommand produces identical bytes.
-- |    Enables caching, hashing, deduplication.
-- |
-- | 5. **Schema atoms map to GPU types**:
-- |    - Pixel → f32
-- |    - RGB channels → u8 (packed) or f32 (unpacked)
-- |    - PickId → u32
-- |    - Radius → f32
-- |
-- | ## Wire Format Overview
-- |
-- | ```
-- | CommandBuffer := Header + Array Command
-- |
-- | Header (16 bytes):
-- |   magic     : u32 = 0x48594447 ("HYDG")
-- |   version   : u32 = 1
-- |   count     : u32 = number of commands
-- |   flags     : u32 = reserved
-- |
-- | Command := CommandType (u8) + Padding (alignment) + Payload
-- |
-- | CommandType:
-- |   0x01 = DrawRect
-- |   0x02 = DrawQuad
-- |   0x03 = DrawGlyph
-- |   0x04 = DrawPath (variable size - stored separately)
-- |   0x05 = DrawParticle
-- |   0x10 = PushClip
-- |   0x11 = PopClip
-- |   0x00 = Noop
-- | ```
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.GPU.Binary as Binary
-- | import Hydrogen.GPU.DrawCommand as DC
-- |
-- | -- Serialize a command buffer
-- | bytes :: Binary.Bytes
-- | bytes = Binary.serialize commands
-- |
-- | -- Get raw byte array for transmission
-- | raw :: Array Int
-- | raw = Binary.toByteArray bytes
-- | ```

module Hydrogen.GPU.Binary
  ( -- * Types
    Bytes
  , Header
  , CommandType
      ( CmdNoop
      , CmdDrawRect
      , CmdDrawQuad
      , CmdDrawGlyph
      , CmdDrawPath
      , CmdDrawParticle
      , CmdPushClip
      , CmdPopClip
      , CmdDrawGlyphPath
      , CmdDrawGlyphInstance
      , CmdDrawWord
      , CmdDefinePathData
      , CmdUpdateAnimationState
      )
  
  -- * Constants
  , magic
  , version
  , headerSize
  , rectPayloadSize
  , quadPayloadSize
  , glyphPayloadSize
  , particlePayloadSize
  -- v2 payload sizes
  , glyphPathHeaderSize
  , glyphInstancePayloadSize
  , wordHeaderSize
  , pathDataHeaderSize
  , animationStateHeaderSize
  
  -- * Serialization
  , serialize
  , serializeHeader
  , serializeCommand
  , serializeRect
  , serializeQuad
  , serializeGlyph
  , serializePath
  , serializeClipRegion
  , serializeParticle
  -- v2 serializers
  , serializeGlyphPath
  , serializeGlyphInstance
  , serializeWord
  , serializePathData
  , serializeAnimationState
  
  -- * Deserialization
  , deserialize
  , deserializeHeader
  , deserializeCommand
  
  -- * Low-level
  , toByteArray
  , fromByteArray
  , writeF32
  , writeU32
  , writeU16
  , writeU8
  , writeI8
  , readF32
  , readU32
  , readU8
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Unit
  , bind
  , mod
  , otherwise
  , pure
  , show
  , (&&)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<>)
  , (==)
  , (>)
  , (>=)
  , (*)
  )

import Data.Array as Array
import Data.Int (floor, toNumber)
import Data.Int.Bits (shl, shr, (.&.), (.|.))
import Data.Maybe (Maybe(Just, Nothing))
import Data.Tuple (Tuple(Tuple))
import Hydrogen.GPU.DrawCommand as DC
import Hydrogen.Animation.Types as AnimTypes
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Raw bytes as array of integers (0-255).
-- | This is the pure representation — actual TypedArray created at boundary.
newtype Bytes = Bytes (Array Int)

derive instance eqBytes :: Eq Bytes

instance showBytes :: Show Bytes where
  show (Bytes arr) = "Bytes[" <> show (Array.length arr) <> "]"

-- | Buffer header.
type Header =
  { magic :: Int      -- 0x48594447 "HYDG"
  , version :: Int    -- Format version
  , count :: Int      -- Number of commands
  , flags :: Int      -- Reserved
  }

-- | Command type discriminant.
data CommandType
  = CmdNoop
  | CmdDrawRect
  | CmdDrawQuad
  | CmdDrawGlyph
  | CmdDrawPath
  | CmdDrawParticle
  | CmdPushClip
  | CmdPopClip
  -- v2 Typography as Geometry
  | CmdDrawGlyphPath
  | CmdDrawGlyphInstance
  | CmdDrawWord
  | CmdDefinePathData
  | CmdUpdateAnimationState

derive instance eqCommandType :: Eq CommandType
derive instance ordCommandType :: Ord CommandType

instance showCommandType :: Show CommandType where
  show CmdNoop = "Noop"
  show CmdDrawRect = "DrawRect"
  show CmdDrawQuad = "DrawQuad"
  show CmdDrawGlyph = "DrawGlyph"
  show CmdDrawPath = "DrawPath"
  show CmdDrawParticle = "DrawParticle"
  show CmdPushClip = "PushClip"
  show CmdPopClip = "PopClip"
  show CmdDrawGlyphPath = "DrawGlyphPath"
  show CmdDrawGlyphInstance = "DrawGlyphInstance"
  show CmdDrawWord = "DrawWord"
  show CmdDefinePathData = "DefinePathData"
  show CmdUpdateAnimationState = "UpdateAnimationState"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Magic number: "HYDG" in little-endian ASCII
magic :: Int
magic = 0x48594447

-- | Current format version
version :: Int
version = 1

-- | Header size in bytes
headerSize :: Int
headerSize = 16

-- | DrawRect payload size (excluding 4-byte command header)
-- | x, y, width, height: 4 × f32 = 16
-- | r, g, b, a: 4 × f32 = 16 (unpacked for GPU)
-- | cornerRadius (4 corners): 4 × f32 = 16
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 56 bytes payload (60 bytes with header)
rectPayloadSize :: Int
rectPayloadSize = 56

-- | DrawQuad payload size
-- | 4 vertices × 2 coords × f32 = 32
-- | color: 4 × f32 = 16
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 56 bytes
quadPayloadSize :: Int
quadPayloadSize = 56

-- | DrawGlyph payload size
-- | x, y: 2 × f32 = 8
-- | glyphIndex: u32 = 4
-- | fontId: u32 = 4
-- | fontSize: f32 = 4
-- | color: 4 × f32 = 16
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 44 bytes
glyphPayloadSize :: Int
glyphPayloadSize = 44

-- | DrawParticle payload size
-- | x, y, z: 3 × f32 = 12
-- | size: f32 = 4
-- | color: 4 × f32 = 16
-- | pickId: u32 = 4
-- | Total: 36 bytes
particlePayloadSize :: Int
particlePayloadSize = 36

-- ─────────────────────────────────────────────────────────────────────────────────
--                                                  // v2 payload size constants
-- ─────────────────────────────────────────────────────────────────────────────────

-- | DrawGlyphPath payload size (VARIABLE - this is the header portion)
-- | glyphId: u32 = 4
-- | fontId: u32 = 4 (upgraded for billion-agent scale)
-- | contourCount: u16 = 2
-- | padding: u16 = 2
-- | bounds: 6 × f32 = 24 (minX, minY, minZ, maxX, maxY, maxZ)
-- | advanceWidth: f32 = 4
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Header: 48 bytes + variable contour data
glyphPathHeaderSize :: Int
glyphPathHeaderSize = 48

-- | DrawGlyphInstance payload size (FIXED: 52 bytes)
-- | pathDataId: u32 = 4
-- | position: 3 × f32 = 12 (x, y, z)
-- | rotation: 3 × f32 = 12 (x, y, z euler)
-- | scale: 3 × f32 = 12 (x, y, z)
-- | color: 4 × u8 = 4 (RGBA packed)
-- | animationPhase: f32 = 4
-- | springState: 5 × f32 = 20 (velocity, displacement, tension, damping, mass)
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Total: 76 bytes (68 + 8 for damping/mass)
glyphInstancePayloadSize :: Int
glyphInstancePayloadSize = 76

-- | DrawWord payload size (VARIABLE - this is the header portion)
-- | wordId: u32 = 4
-- | glyphCount: u16 = 2
-- | staggerDirection: u8 = 1
-- | easing: u8 = 1
-- | origin: 3 × f32 = 12 (x, y, z)
-- | staggerDelayMs: f32 = 4
-- | staggerSeed: u32 = 4 (for StaggerRandom, 0 otherwise)
-- | color: 4 × u8 = 4
-- | depth: f32 = 4
-- | pickId: u32 = 4
-- | Header: 40 bytes + variable glyph references
wordHeaderSize :: Int
wordHeaderSize = 40

-- | PathData payload size (VARIABLE - this is the header portion)
-- | pathDataId: u32 = 4
-- | commandCount: u32 = 4
-- | bounds: 6 × f32 = 24
-- | Header: 32 bytes + variable command data
pathDataHeaderSize :: Int
pathDataHeaderSize = 32

-- | AnimationState payload size (VARIABLE - this is the header portion)
-- | targetCount: u16 = 2
-- | mode: u8 = 1
-- | padding: u8 = 1
-- | frameTime: f32 = 4
-- | blendFactor: f32 = 4 (for AnimationBlend, 0.0 otherwise)
-- | Header: 12 bytes + variable target data
animationStateHeaderSize :: Int
animationStateHeaderSize = 12

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // low level ops
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Bytes to raw byte array.
toByteArray :: Bytes -> Array Int
toByteArray (Bytes arr) = arr

-- | Create Bytes from raw byte array.
fromByteArray :: Array Int -> Bytes
fromByteArray = Bytes

-- | Write a 32-bit float as 4 bytes (little-endian).
-- | IEEE 754 single precision.
writeF32 :: Number -> Array Int
writeF32 n =
  let
    -- Convert float to IEEE 754 bits
    bits = floatToBits n
  in
    [ bits .&. 0xFF
    , (shr bits 8) .&. 0xFF
    , (shr bits 16) .&. 0xFF
    , (shr bits 24) .&. 0xFF
    ]

-- | Write a 32-bit unsigned integer as 4 bytes (little-endian).
writeU32 :: Int -> Array Int
writeU32 n =
  [ n .&. 0xFF
  , (shr n 8) .&. 0xFF
  , (shr n 16) .&. 0xFF
  , (shr n 24) .&. 0xFF
  ]

-- | Write an 8-bit unsigned integer.
writeU8 :: Int -> Array Int
writeU8 n = [n .&. 0xFF]

-- | Write a 16-bit unsigned integer as 2 bytes (little-endian).
writeU16 :: Int -> Array Int
writeU16 n =
  [ n .&. 0xFF
  , (shr n 8) .&. 0xFF
  ]

-- | Write a signed 8-bit integer (stored as unsigned).
-- | Values -128 to 127 are stored as 0-255.
writeI8 :: Int -> Array Int
writeI8 n = 
  let unsigned = if n < 0 then 256 + n else n
  in [unsigned .&. 0xFF]

-- | Read a 32-bit float from bytes at offset.
readF32 :: Array Int -> Int -> Maybe Number
readF32 arr offset =
  case Array.index arr offset
     , Array.index arr (offset + 1)
     , Array.index arr (offset + 2)
     , Array.index arr (offset + 3) of
    Just b0, Just b1, Just b2, Just b3 ->
      let bits = b0 .|. (shl b1 8) .|. (shl b2 16) .|. (shl b3 24)
      in Just (bitsToFloat bits)
    _, _, _, _ -> Nothing

-- | Read a 32-bit unsigned integer from bytes at offset.
readU32 :: Array Int -> Int -> Maybe Int
readU32 arr offset =
  case Array.index arr offset
     , Array.index arr (offset + 1)
     , Array.index arr (offset + 2)
     , Array.index arr (offset + 3) of
    Just b0, Just b1, Just b2, Just b3 ->
      Just (b0 .|. (shl b1 8) .|. (shl b2 16) .|. (shl b3 24))
    _, _, _, _ -> Nothing

-- | Read an 8-bit unsigned integer from bytes at offset.
readU8 :: Array Int -> Int -> Maybe Int
readU8 arr offset = Array.index arr offset

-- | Convert float to IEEE 754 bits.
-- | Pure implementation without FFI.
floatToBits :: Number -> Int
floatToBits n
  | n == 0.0 = 0
  | otherwise =
      let
        sign = if n < 0.0 then 1 else 0
        absN = if n < 0.0 then negate n else n
        
        -- Find exponent and mantissa
        -- This is a simplified implementation
        -- For production, would need proper IEEE 754 handling
        logResult = log2Approx absN
        exp = floor logResult + 127
        mantissa = floor ((absN / pow2 (exp - 127) - 1.0) * 8388608.0)
      in
        (shl sign 31) .|. (shl (exp .&. 0xFF) 23) .|. (mantissa .&. 0x7FFFFF)
  where
    negate x = 0.0 - x

-- | Convert IEEE 754 bits to float.
bitsToFloat :: Int -> Number
bitsToFloat bits =
  let
    sign = shr bits 31
    exp = (shr bits 23) .&. 0xFF
    mantissa = bits .&. 0x7FFFFF
    
    signMult = if sign == 0 then 1.0 else (0.0 - 1.0)
  in
    if exp == 0 && mantissa == 0 then 0.0
    else signMult * pow2 (exp - 127) * (1.0 + toNumber mantissa / 8388608.0)

-- | Approximate log base 2.
log2Approx :: Number -> Number
log2Approx n = log n / log 2.0
  where
    log x = nativeLog x

-- | Power of 2.
pow2 :: Int -> Number
pow2 e = 
  if e >= 0 
    then pow2Positive e 1.0
    else 1.0 / pow2Positive (0 - e) 1.0
  where
    pow2Positive :: Int -> Number -> Number
    pow2Positive 0 acc = acc
    pow2Positive n acc = pow2Positive (n - 1) (acc * 2.0)

-- | Native log function (using series expansion for purity).
-- | For production, this would use a more efficient method.
nativeLog :: Number -> Number
nativeLog x = 
  if x == 1.0 
    then 0.0
  else if x > 0.0 && x < 2.0 
    then logSeries (x - 1.0) 1 0.0
  else if x >= 2.0 
    then log2Const + nativeLog (x / 2.0)
  else 0.0  -- Invalid input, return 0
  where
    log2Const :: Number
    log2Const = 0.6931471805599453
    
    logSeries :: Number -> Int -> Number -> Number
    logSeries _ 100 acc = acc  -- Limit iterations
    logSeries y n acc =
      let term = (if mod n 2 == 0 then (0.0 - 1.0) else 1.0) * powNum y n / toNumber n
      in logSeries y (n + 1) (acc + term)
    
    powNum :: Number -> Int -> Number
    powNum _ 0 = 1.0
    powNum base pexp = base * powNum base (pexp - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // serialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Serialize a command buffer to bytes.
serialize :: forall msg. DC.CommandBuffer msg -> Bytes
serialize commands =
  let
    header = serializeHeader
      { magic: magic
      , version: version
      , count: Array.length commands
      , flags: 0
      }
    body = Array.concatMap serializeCommand commands
  in
    Bytes (header <> body)

-- | Serialize header.
serializeHeader :: Header -> Array Int
serializeHeader h =
  writeU32 h.magic
  <> writeU32 h.version
  <> writeU32 h.count
  <> writeU32 h.flags

-- | Serialize a single command.
serializeCommand :: forall msg. DC.DrawCommand msg -> Array Int
serializeCommand = case _ of
  DC.Noop -> writeU8 0x00
  
  DC.DrawRect params -> writeU8 0x01 <> pad 3 <> serializeRect params
  
  DC.DrawQuad params -> writeU8 0x02 <> pad 3 <> serializeQuad params
  
  DC.DrawGlyph params -> writeU8 0x03 <> pad 3 <> serializeGlyph params
  
  DC.DrawPath params -> writeU8 0x04 <> pad 3 <> serializePath params
  
  DC.DrawParticle params -> writeU8 0x05 <> pad 3 <> serializeParticle params
  
  DC.PushClip region -> writeU8 0x10 <> pad 3 <> serializeClipRegion region
  
  DC.PopClip -> writeU8 0x11 <> pad 3
  
  -- v2 Typography as Geometry (opcodes 0x20-0x24)
  DC.DrawGlyphPath params -> writeU8 0x20 <> pad 3 <> serializeGlyphPath params
  
  DC.DrawGlyphInstance params -> writeU8 0x21 <> pad 3 <> serializeGlyphInstance params
  
  DC.DrawWord params -> writeU8 0x22 <> pad 3 <> serializeWord params
  
  DC.DefinePathData params -> writeU8 0x23 <> pad 3 <> serializePathData params
  
  DC.UpdateAnimationState params -> writeU8 0x24 <> pad 3 <> serializeAnimationState params

-- | Padding bytes for alignment.
pad :: Int -> Array Int
pad n = Array.replicate n 0

-- | Serialize DrawRect payload.
serializeRect :: forall msg. DC.RectParams msg -> Array Int
serializeRect p =
  let
    rgb = RGB.fromRGBA p.fill
  in
    -- Position and size
    writeF32 (unwrapPixel p.x)
    <> writeF32 (unwrapPixel p.y)
    <> writeF32 (unwrapPixel p.width)
    <> writeF32 (unwrapPixel p.height)
    -- Color (unpacked to f32 for GPU, unit interval 0.0-1.0)
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.fill))
    -- Corner radii
    <> writeF32 (radiusToNumber p.cornerRadius.topLeft)
    <> writeF32 (radiusToNumber p.cornerRadius.topRight)
    <> writeF32 (radiusToNumber p.cornerRadius.bottomRight)
    <> writeF32 (radiusToNumber p.cornerRadius.bottomLeft)
    -- Depth
    <> writeF32 p.depth
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawQuad payload.
serializeQuad :: forall msg. DC.QuadParams msg -> Array Int
serializeQuad p =
  let
    rgb = RGB.fromRGBA p.fill
  in
    -- 4 vertices
    writeF32 (unwrapPixel p.v0.x) <> writeF32 (unwrapPixel p.v0.y)
    <> writeF32 (unwrapPixel p.v1.x) <> writeF32 (unwrapPixel p.v1.y)
    <> writeF32 (unwrapPixel p.v2.x) <> writeF32 (unwrapPixel p.v2.y)
    <> writeF32 (unwrapPixel p.v3.x) <> writeF32 (unwrapPixel p.v3.y)
    -- Color
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.fill))
    -- Depth
    <> writeF32 p.depth
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawGlyph payload.
serializeGlyph :: forall msg. DC.GlyphParams msg -> Array Int
serializeGlyph p =
  let
    rgb = RGB.fromRGBA p.color
  in
    writeF32 (unwrapPixel p.x)
    <> writeF32 (unwrapPixel p.y)
    <> writeU32 p.glyphIndex
    <> writeU32 p.fontId
    <> writeF32 (unwrapPixel p.fontSize)
    -- Color
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.color))
    -- Depth
    <> writeF32 p.depth
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawParticle payload.
serializeParticle :: forall msg. DC.ParticleParams msg -> Array Int
serializeParticle p =
  let
    rgb = RGB.fromRGBA p.color
  in
    writeF32 (unwrapPixel p.x)
    <> writeF32 (unwrapPixel p.y)
    <> writeF32 p.z
    <> writeF32 (unwrapPixel p.size)
    -- Color
    <> writeF32 (Channel.toUnitInterval (RGB.red rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
    <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
    <> writeF32 (Opacity.toUnitInterval (RGB.alpha p.color))
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawPath payload (variable length).
-- |
-- | Wire format:
-- | - segmentCount: u32 (number of path segments)
-- | - fillPresent: u8 (1 = has fill, 0 = no fill)
-- | - strokePresent: u8 (1 = has stroke, 0 = no stroke)
-- | - padding: u16 (alignment)
-- | - [fill color if present]: 4 × f32
-- | - [stroke color if present]: 4 × f32
-- | - strokeWidth: f32
-- | - depth: f32
-- | - pickId: u32
-- | - [segments]: variable path segment data
serializePath :: forall msg. DC.PathParams msg -> Array Int
serializePath p =
  let
    segmentCount = Array.length p.segments
    fillPresent = case p.fill of
      Just _ -> 1
      Nothing -> 0
    strokePresent = case p.stroke of
      Just _ -> 1
      Nothing -> 0
  in
    -- Header
    writeU32 segmentCount
    <> writeU8 fillPresent
    <> writeU8 strokePresent
    <> writeU16 0  -- padding for alignment
    -- Fill color (if present)
    <> serializeMaybeColor p.fill
    -- Stroke color (if present)
    <> serializeMaybeColor p.stroke
    -- Stroke width
    <> writeF32 (unwrapPixel p.strokeWidth)
    -- Depth
    <> writeF32 p.depth
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)
    -- Path segments
    <> Array.concatMap serializePathSegment p.segments

-- | Serialize an optional color (RGBA as 4 × f32, or nothing).
serializeMaybeColor :: Maybe RGB.RGBA -> Array Int
serializeMaybeColor = case _ of
  Nothing -> []
  Just rgba ->
    let rgb = RGB.fromRGBA rgba
    in writeF32 (Channel.toUnitInterval (RGB.red rgb))
       <> writeF32 (Channel.toUnitInterval (RGB.green rgb))
       <> writeF32 (Channel.toUnitInterval (RGB.blue rgb))
       <> writeF32 (Opacity.toUnitInterval (RGB.alpha rgba))

-- | Serialize ClipRegion payload.
-- |
-- | Wire format for ClipRect:
-- | - subtype: u8 = 0x00 (rectangle)
-- | - padding: u8[3]
-- | - x, y, width, height: 4 × f32
-- | - cornerRadii: 4 × f32 (topLeft, topRight, bottomRight, bottomLeft)
-- |
-- | Wire format for ClipPath:
-- | - subtype: u8 = 0x01 (path)
-- | - padding: u8[3]
-- | - segmentCount: u32
-- | - [segments]: variable path segment data
serializeClipRegion :: DC.ClipRegion -> Array Int
serializeClipRegion = case _ of
  DC.ClipRect rect ->
    writeU8 0x00  -- subtype: rectangle
    <> pad 3      -- alignment padding
    -- Position and size
    <> writeF32 (unwrapPixel rect.x)
    <> writeF32 (unwrapPixel rect.y)
    <> writeF32 (unwrapPixel rect.width)
    <> writeF32 (unwrapPixel rect.height)
    -- Corner radii
    <> writeF32 (radiusToNumber rect.cornerRadius.topLeft)
    <> writeF32 (radiusToNumber rect.cornerRadius.topRight)
    <> writeF32 (radiusToNumber rect.cornerRadius.bottomRight)
    <> writeF32 (radiusToNumber rect.cornerRadius.bottomLeft)
  
  DC.ClipPath segments ->
    let segmentCount = Array.length segments
    in writeU8 0x01  -- subtype: path
       <> pad 3       -- alignment padding
       <> writeU32 segmentCount
       <> Array.concatMap serializePathSegment segments

-- ─────────────────────────────────────────────────────────────────────────────────
--                                                // v2 typography serialization
-- ─────────────────────────────────────────────────────────────────────────────────

-- | Serialize DrawGlyphPath payload (variable length).
-- |
-- | Wire format:
-- | - glyphId: u32
-- | - fontId: u16
-- | - contourCount: u16
-- | - bounds: 6 × f32
-- | - advanceWidth: f32
-- | - depth: f32
-- | - pickId: u32
-- | - [contours]: variable, per-contour command arrays
serializeGlyphPath :: forall msg. DC.GlyphPathParams msg -> Array Int
serializeGlyphPath p =
  let
    contourCount = Array.length p.contours
  in
    -- Header
    writeU32 p.glyphId
    <> writeU32 p.fontId         -- u32 for billion-agent scale (was u16)
    <> writeU16 contourCount
    <> writeU16 0                -- padding for alignment
    -- Bounds
    <> writeF32 (unwrapPixel p.bounds.minX)
    <> writeF32 (unwrapPixel p.bounds.minY)
    <> writeF32 (unwrapPixel p.bounds.minZ)
    <> writeF32 (unwrapPixel p.bounds.maxX)
    <> writeF32 (unwrapPixel p.bounds.maxY)
    <> writeF32 (unwrapPixel p.bounds.maxZ)
    -- Advance and depth
    <> writeF32 (unwrapPixel p.advanceWidth)
    <> writeF32 p.depth
    -- Pick ID
    <> writeU32 (pickIdToInt p.pickId)
    -- Contours (variable)
    <> Array.concatMap serializeContour p.contours

-- | Serialize a single contour.
serializeContour :: DC.ContourData -> Array Int
serializeContour c =
  let
    cmdCount = Array.length c.commands
    outerFlag = if c.isOuter then 1 else 0
  in
    writeU16 cmdCount
    <> writeU8 outerFlag
    <> writeU8 0  -- padding for alignment
    <> Array.concatMap serializePathSegment c.commands

-- | Serialize a path segment.
serializePathSegment :: DC.PathSegment -> Array Int
serializePathSegment = case _ of
  DC.MoveTo pt -> 
    writeU8 0x01 <> pad 3
    <> writeF32 (unwrapPixel pt.x)
    <> writeF32 (unwrapPixel pt.y)
  
  DC.LineTo pt ->
    writeU8 0x02 <> pad 3
    <> writeF32 (unwrapPixel pt.x)
    <> writeF32 (unwrapPixel pt.y)
  
  DC.QuadraticTo ctrl end ->
    writeU8 0x03 <> pad 3
    <> writeF32 (unwrapPixel ctrl.x)
    <> writeF32 (unwrapPixel ctrl.y)
    <> writeF32 (unwrapPixel end.x)
    <> writeF32 (unwrapPixel end.y)
  
  DC.CubicTo c1 c2 end ->
    writeU8 0x04 <> pad 3
    <> writeF32 (unwrapPixel c1.x)
    <> writeF32 (unwrapPixel c1.y)
    <> writeF32 (unwrapPixel c2.x)
    <> writeF32 (unwrapPixel c2.y)
    <> writeF32 (unwrapPixel end.x)
    <> writeF32 (unwrapPixel end.y)
  
  DC.ClosePath ->
    writeU8 0x05 <> pad 3

-- | Serialize DrawGlyphInstance payload (fixed 68 bytes).
serializeGlyphInstance :: forall msg. DC.GlyphInstanceParams msg -> Array Int
serializeGlyphInstance p =
  let
    rgb = RGB.fromRGBA p.color
  in
    -- Path reference
    writeU32 p.pathDataId
    -- Position (3D)
    <> writeF32 (unwrapPixel p.position.x)
    <> writeF32 (unwrapPixel p.position.y)
    <> writeF32 (unwrapPixel p.position.z)
    -- Rotation (euler)
    <> writeF32 p.rotation.x
    <> writeF32 p.rotation.y
    <> writeF32 p.rotation.z
    -- Scale
    <> writeF32 p.scale.x
    <> writeF32 p.scale.y
    <> writeF32 p.scale.z
    -- Color (packed RGBA)
    <> writeU8 (Channel.unwrap (RGB.red rgb))
    <> writeU8 (Channel.unwrap (RGB.green rgb))
    <> writeU8 (Channel.unwrap (RGB.blue rgb))
    <> writeU8 (Opacity.unwrap (RGB.alpha p.color))
    -- Animation state
    <> writeF32 p.animationPhase
    <> writeF32 p.spring.velocity
    <> writeF32 p.spring.displacement
    <> writeF32 p.spring.tension
    <> writeF32 p.spring.damping
    <> writeF32 p.spring.mass
    -- Depth and pick
    <> writeF32 p.depth
    <> writeU32 (pickIdToInt p.pickId)

-- | Serialize DrawWord payload (variable length).
serializeWord :: forall msg. DC.WordParams msg -> Array Int
serializeWord p =
  let
    glyphCount = Array.length p.glyphInstances
    rgb = RGB.fromRGBA p.color
    staggerSeed = getStaggerSeed p.stagger.direction
  in
    -- Header
    writeU32 p.wordId
    <> writeU16 glyphCount
    <> writeU8 (staggerDirToInt p.stagger.direction)
    <> writeU8 (easingToInt p.stagger.easing)
    -- Origin
    <> writeF32 (unwrapPixel p.origin.x)
    <> writeF32 (unwrapPixel p.origin.y)
    <> writeF32 (unwrapPixel p.origin.z)
    -- Stagger delay and seed
    <> writeF32 p.stagger.delayMs
    <> writeU32 staggerSeed  -- Seed for StaggerRandom, 0 otherwise
    -- Color (packed)
    <> writeU8 (Channel.unwrap (RGB.red rgb))
    <> writeU8 (Channel.unwrap (RGB.green rgb))
    <> writeU8 (Channel.unwrap (RGB.blue rgb))
    <> writeU8 (Opacity.unwrap (RGB.alpha p.color))
    -- Depth and pick
    <> writeF32 p.depth
    <> writeU32 (pickIdToInt p.pickId)
    -- Glyph references (variable)
    <> Array.concatMap writeU32 p.glyphInstances
    -- Positions (variable)
    <> Array.concatMap serializePoint3D p.positions

-- | Extract seed from StaggerDirection (0 for non-random).
getStaggerSeed :: DC.StaggerDirection -> Int
getStaggerSeed = case _ of
  AnimTypes.StaggerRandom seed -> seed
  _ -> 0

-- | Serialize a 3D point.
serializePoint3D :: DC.Point3D -> Array Int
serializePoint3D p =
  writeF32 (unwrapPixel p.x)
  <> writeF32 (unwrapPixel p.y)
  <> writeF32 (unwrapPixel p.z)

-- | Serialize PathData payload (variable length).
serializePathData :: DC.PathDataParams -> Array Int
serializePathData p =
  let
    cmdCount = Array.length p.commands
  in
    writeU32 p.pathDataId
    <> writeU32 cmdCount
    -- Bounds
    <> writeF32 (unwrapPixel p.bounds.minX)
    <> writeF32 (unwrapPixel p.bounds.minY)
    <> writeF32 (unwrapPixel p.bounds.minZ)
    <> writeF32 (unwrapPixel p.bounds.maxX)
    <> writeF32 (unwrapPixel p.bounds.maxY)
    <> writeF32 (unwrapPixel p.bounds.maxZ)
    -- Commands (variable)
    <> Array.concatMap serializePathSegment p.commands

-- | Serialize AnimationState payload (variable length).
serializeAnimationState :: DC.AnimationStateParams -> Array Int
serializeAnimationState p =
  let
    targetCount = Array.length p.targets
    blendFactor = getBlendFactor p.mode
  in
    writeU16 targetCount
    <> writeU8 (animModeToInt p.mode)
    <> writeU8 0  -- padding
    <> writeF32 p.frameTime
    <> writeF32 blendFactor  -- Blend factor (0.0 if not AnimationBlend)
    -- Targets (variable)
    <> Array.concatMap serializeAnimTarget p.targets

-- | Extract blend factor from AnimationUpdateMode (0.0 for non-blend).
getBlendFactor :: DC.AnimationUpdateMode -> Number
getBlendFactor = case _ of
  DC.AnimationBlend factor -> factor
  _ -> 0.0

-- | Serialize a single animation target.
serializeAnimTarget :: DC.AnimationTarget -> Array Int
serializeAnimTarget t =
  writeU32 t.targetId
  <> writeU8 (targetTypeToInt t.targetType)
  <> pad 3  -- alignment
  -- Delta position
  <> writeF32 (unwrapPixel t.deltaPosition.x)
  <> writeF32 (unwrapPixel t.deltaPosition.y)
  <> writeF32 (unwrapPixel t.deltaPosition.z)
  -- Delta rotation
  <> writeF32 t.deltaRotation.x
  <> writeF32 t.deltaRotation.y
  <> writeF32 t.deltaRotation.z
  -- Delta scale
  <> writeF32 t.deltaScale.x
  <> writeF32 t.deltaScale.y
  <> writeF32 t.deltaScale.z
  -- Delta color (signed, but stored as unsigned)
  <> writeI8 t.deltaColor.r
  <> writeI8 t.deltaColor.g
  <> writeI8 t.deltaColor.b
  <> writeI8 t.deltaColor.a
  -- Phase advance
  <> writeF32 t.phaseAdvance

-- ─────────────────────────────────────────────────────────────────────────────────
--                                                           // v2 enum encoders
-- ─────────────────────────────────────────────────────────────────────────────────

-- | Encode StaggerDirection to u8.
staggerDirToInt :: DC.StaggerDirection -> Int
staggerDirToInt = case _ of
  AnimTypes.StaggerLeftToRight -> 0
  AnimTypes.StaggerRightToLeft -> 1
  AnimTypes.StaggerCenterOut -> 2
  AnimTypes.StaggerEdgesIn -> 3
  AnimTypes.StaggerTopToBottom -> 4
  AnimTypes.StaggerBottomToTop -> 5
  AnimTypes.StaggerRandom _ -> 6  -- Seed stored separately if needed

-- | Encode EasingFunction to u8.
easingToInt :: DC.EasingFunction -> Int
easingToInt = case _ of
  AnimTypes.EasingIdLinear -> 0
  AnimTypes.EasingIdInQuad -> 1
  AnimTypes.EasingIdOutQuad -> 2
  AnimTypes.EasingIdInOutQuad -> 3
  AnimTypes.EasingIdInCubic -> 4
  AnimTypes.EasingIdOutCubic -> 5
  AnimTypes.EasingIdInOutCubic -> 6
  AnimTypes.EasingIdInElastic -> 7
  AnimTypes.EasingIdOutElastic -> 8
  AnimTypes.EasingIdInOutElastic -> 9
  AnimTypes.EasingIdInBounce -> 10
  AnimTypes.EasingIdOutBounce -> 11
  AnimTypes.EasingIdSpring -> 12

-- | Encode AnimationUpdateMode to u8.
animModeToInt :: DC.AnimationUpdateMode -> Int
animModeToInt = case _ of
  DC.AnimationReplace -> 0
  DC.AnimationAdditive -> 1
  DC.AnimationBlend _ -> 2  -- Factor stored separately if needed

-- | Encode TargetType to u8.
targetTypeToInt :: DC.TargetType -> Int
targetTypeToInt = case _ of
  DC.TargetGlyphInstance -> 0
  DC.TargetWord -> 1
  DC.TargetPathData -> 2
  DC.TargetControlPoint -> 3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // deserialization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Deserialize bytes to command buffer.
-- | Returns Nothing if invalid format.
deserialize :: Bytes -> Maybe (Tuple Header (Array (DC.DrawCommand Unit)))
deserialize (Bytes arr) = do
  header <- deserializeHeader arr
  -- For now, return header only - full deserialization needs more work
  pure (Tuple header [])

-- | Deserialize header.
deserializeHeader :: Array Int -> Maybe Header
deserializeHeader arr = do
  m <- readU32 arr 0
  v <- readU32 arr 4
  c <- readU32 arr 8
  f <- readU32 arr 12
  if m == magic
    then Just { magic: m, version: v, count: c, flags: f }
    else Nothing

-- | Deserialize a single command at offset.
-- | Returns the command and new offset.
deserializeCommand :: Array Int -> Int -> Maybe (Tuple (DC.DrawCommand Unit) Int)
deserializeCommand arr offset = do
  cmdType <- readU8 arr offset
  case cmdType of
    0x00 -> Just (Tuple DC.Noop (offset + 1))
    0x01 -> Just (Tuple DC.Noop (offset + 4 + rectPayloadSize))  -- Placeholder
    _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unwrap Pixel to Number.
unwrapPixel :: Device.Pixel -> Number
unwrapPixel (Device.Pixel n) = n

-- | Convert Radius to Number (pixels).
radiusToNumber :: Radius.Radius -> Number
radiusToNumber = case _ of
  Radius.RadiusPx n -> n
  Radius.RadiusPercent n -> n  -- Runtime resolves to pixels
  Radius.RadiusRem n -> n * 16.0  -- Assume 16px base
  Radius.RadiusFull -> 9999.0
  Radius.RadiusNone -> 0.0

-- | Convert Maybe PickId to Int (0 = no hit).
pickIdToInt :: Maybe DC.PickId -> Int
pickIdToInt = case _ of
  Nothing -> 0
  Just pid -> DC.unwrapPickId pid
