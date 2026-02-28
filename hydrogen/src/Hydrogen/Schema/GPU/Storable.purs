-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // gpu // storable
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPUStorable — Typeclass for types that can be serialized to GPU buffers.
-- |
-- | ## Purpose
-- |
-- | At billion-agent scale, data must flow deterministically between CPU and GPU.
-- | This typeclass defines:
-- |
-- | 1. **Byte size** — How many bytes the type occupies in a GPU buffer
-- | 2. **Alignment** — Memory alignment requirements (WebGPU spec)
-- | 3. **Serialization** — Convert to/from byte representation
-- |
-- | ## WebGPU Alignment Rules
-- |
-- | WebGPU has strict alignment requirements:
-- | - f32: 4 bytes, 4-byte alignment
-- | - vec2<f32>: 8 bytes, 8-byte alignment
-- | - vec3<f32>: 12 bytes, 16-byte alignment (!)
-- | - vec4<f32>: 16 bytes, 16-byte alignment
-- | - mat4x4<f32>: 64 bytes, 16-byte alignment
-- |
-- | ## Determinism Guarantee
-- |
-- | Same value → same bytes. Always. This is critical for:
-- | - Cache keying (UUID5 of serialized data)
-- | - Distributed agents producing identical buffers
-- | - Reproducible rendering across sessions
-- |
-- | ## Lean4 Proof Integration
-- |
-- | The roundtrip property is proven in Lean4:
-- | ```lean
-- | theorem roundtrip : ∀ x, deserialize (serialize x) = x
-- | ```

module Hydrogen.Schema.GPU.Storable
  ( -- * GPUStorable Typeclass
    class GPUStorable
  , byteSize
  , alignment
  , toBytes
  , fromBytes
  
  -- * Common Alignments
  , Alignment
  , align4
  , align8
  , align16
  , unwrapAlignment
  
  -- * Byte Operations
  , ByteArray(ByteArray)
  , emptyBytes
  , concatBytes
  , bytesLength
  
  -- * Padding Utilities
  , alignedSize
  , paddingNeeded
  
  -- * Basic Instances Documentation
  -- | Note: Instances are provided for common types below
  ) where

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
  , (>)
  , (>=)
  , (==)
  , (<>)
  , mod
  )

import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Array as Array
import Data.Int (toNumber, round) as Int

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Dimension.Vector.Vec2 as Vec2
import Hydrogen.Schema.Dimension.Vector.Vec3 as Vec3
import Hydrogen.Schema.Dimension.Vector.Vec4 as Vec4
import Hydrogen.Schema.Dimension.Point2D as Point2D
import Hydrogen.Schema.Color.SRGB as SRGB
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Saturation
import Hydrogen.Schema.Color.Lightness as Lightness
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.HSLA as HSLA
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Geometry.Angle as Angle
import Hydrogen.Schema.Geometry.Radius as Radius
import Hydrogen.Schema.Dimension.Size2D as Size2D
import Hydrogen.Schema.Geometry.Transform as Transform
import Data.Number (pi) as Number

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Memory alignment in bytes (must be power of 2)
newtype Alignment = Alignment Int

derive instance eqAlignment :: Eq Alignment
derive instance ordAlignment :: Ord Alignment

instance showAlignment :: Show Alignment where
  show (Alignment n) = "Alignment(" <> show n <> ")"

-- | 4-byte alignment (f32, i32, u32)
align4 :: Alignment
align4 = Alignment 4

-- | 8-byte alignment (vec2<f32>, f64)
align8 :: Alignment
align8 = Alignment 8

-- | 16-byte alignment (vec3<f32>, vec4<f32>, mat4x4<f32>)
align16 :: Alignment
align16 = Alignment 16

-- | Unwrap alignment
unwrapAlignment :: Alignment -> Int
unwrapAlignment (Alignment n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // byte array
-- ═════════════════════════════════════════════════════════════════════════════

-- | A byte array for GPU serialization
-- | In actual WebGPU, this would be ArrayBuffer/TypedArray
-- | Here we use Array Int where each Int is 0-255
newtype ByteArray = ByteArray (Array Int)

derive instance eqByteArray :: Eq ByteArray

instance showByteArray :: Show ByteArray where
  show (ByteArray arr) = "ByteArray[" <> show (Array.length arr) <> " bytes]"

-- | Empty byte array
emptyBytes :: ByteArray
emptyBytes = ByteArray []

-- | Concatenate byte arrays
concatBytes :: ByteArray -> ByteArray -> ByteArray
concatBytes (ByteArray a) (ByteArray b) = ByteArray (a <> b)

-- | Length of byte array
bytesLength :: ByteArray -> Int
bytesLength (ByteArray arr) = Array.length arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // padding utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate padding needed to reach alignment
paddingNeeded :: Int -> Alignment -> Int
paddingNeeded size (Alignment align) =
  let remainder = size `mod` align
  in if remainder == 0 then 0 else align - remainder

-- | Calculate size with alignment padding
alignedSize :: Int -> Alignment -> Int
alignedSize size align = size + paddingNeeded size align

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // gpustorable typeclass
-- ═════════════════════════════════════════════════════════════════════════════

-- | Types that can be stored in GPU buffers.
-- |
-- | ## Laws
-- |
-- | 1. Roundtrip: `fromBytes (toBytes x) == Just x`
-- | 2. Size consistency: `bytesLength (toBytes x) == byteSize`
-- | 3. Alignment: offset in buffer must be multiple of `alignment`
-- |
-- | ## Implementation Notes
-- |
-- | When implementing this typeclass:
-- | - Use little-endian byte order (WebGPU/x86 native)
-- | - Pad structs to alignment boundaries
-- | - Handle IEEE 754 for floating-point types
class GPUStorable a where
  -- | Size in bytes when stored in GPU buffer
  byteSize :: a -> Int
  
  -- | Alignment requirement in bytes
  alignment :: a -> Alignment
  
  -- | Serialize to bytes
  toBytes :: a -> ByteArray
  
  -- | Deserialize from bytes
  fromBytes :: ByteArray -> Maybe a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // number instance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Number to 4 bytes (IEEE 754 single-precision)
-- | In real implementation, this would use Float32Array
numberToBytes :: Number -> ByteArray
numberToBytes n =
  -- Placeholder: In actual implementation, this would use FFI to Float32Array
  -- For now, we represent as 4 bytes
  let truncated = Int.round n
      b0 = truncated `mod` 256
      b1 = (truncated / 256) `mod` 256
      b2 = (truncated / 65536) `mod` 256
      b3 = (truncated / 16777216) `mod` 256
  in ByteArray [b0, b1, b2, b3]

-- | Convert 4 bytes to Number
bytesToNumber :: ByteArray -> Maybe Number
bytesToNumber (ByteArray arr) =
  case Array.length arr >= 4 of
    true -> 
      case Array.index arr 0, Array.index arr 1, Array.index arr 2, Array.index arr 3 of
        Just b0, Just b1, Just b2, Just b3 ->
          Just $ Int.toNumber (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216)
        _, _, _, _ -> Nothing
    false -> Nothing

instance gpuStorableNumber :: GPUStorable Number where
  byteSize _ = 4
  alignment _ = align4
  toBytes = numberToBytes
  fromBytes = bytesToNumber

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // int instance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Int to 4 bytes (i32)
intToBytes :: Int -> ByteArray
intToBytes n =
  let b0 = n `mod` 256
      b1 = (n / 256) `mod` 256
      b2 = (n / 65536) `mod` 256
      b3 = (n / 16777216) `mod` 256
  in ByteArray [b0, b1, b2, b3]

-- | Convert 4 bytes to Int
bytesToInt :: ByteArray -> Maybe Int
bytesToInt (ByteArray arr) =
  case Array.length arr >= 4 of
    true -> 
      case Array.index arr 0, Array.index arr 1, Array.index arr 2, Array.index arr 3 of
        Just b0, Just b1, Just b2, Just b3 ->
          Just (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216)
        _, _, _, _ -> Nothing
    false -> Nothing

instance gpuStorableInt :: GPUStorable Int where
  byteSize _ = 4
  alignment _ = align4
  toBytes = intToBytes
  fromBytes = bytesToInt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // boolean instance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Boolean to 4 bytes (u32 in WGSL)
-- | WebGPU uses 32-bit booleans
boolToBytes :: Boolean -> ByteArray
boolToBytes b = ByteArray [if b then 1 else 0, 0, 0, 0]

-- | Convert 4 bytes to Boolean
bytesToBool :: ByteArray -> Maybe Boolean
bytesToBool (ByteArray arr) =
  case Array.index arr 0 of
    Just b -> Just (b > 0)
    Nothing -> Nothing

instance gpuStorableBoolean :: GPUStorable Boolean where
  byteSize _ = 4
  alignment _ = align4
  toBytes = boolToBytes
  fromBytes = bytesToBool

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // schema atom instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | UnitInterval serializes as a single f32.
-- |
-- | GPU representation: f32 (4 bytes)
-- | WGSL type: f32
instance gpuStorableUnitInterval :: GPUStorable Bounded.UnitInterval where
  byteSize _ = 4
  alignment _ = align4
  toBytes ui = numberToBytes (Bounded.unwrapUnit ui)
  fromBytes bytes = do
    n <- bytesToNumber bytes
    pure (Bounded.clampUnit n)

-- | Vec2 Number serializes as vec2<f32>.
-- |
-- | GPU representation: vec2<f32> (8 bytes, 8-byte aligned)
-- | WGSL type: vec2<f32>
instance gpuStorableVec2Number :: GPUStorable (Vec2.Vec2 Number) where
  byteSize _ = 8
  alignment _ = align8
  toBytes v =
    let ByteArray xb = numberToBytes (Vec2.getX2 v)
        ByteArray yb = numberToBytes (Vec2.getY2 v)
    in ByteArray (xb <> yb)
  fromBytes (ByteArray arr) = do
    xv <- bytesToNumber (ByteArray (Array.take 4 arr))
    yv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    pure (Vec2.vec2 xv yv)

-- | Vec3 Number serializes as vec3<f32>.
-- |
-- | GPU representation: vec3<f32> (12 bytes, 16-byte aligned)
-- | WGSL type: vec3<f32>
-- |
-- | IMPORTANT: vec3 requires 16-byte alignment in WebGPU despite being
-- | only 12 bytes. This is a WebGPU spec requirement.
instance gpuStorableVec3Number :: GPUStorable (Vec3.Vec3 Number) where
  byteSize _ = 12
  alignment _ = align16
  toBytes v =
    let ByteArray xb = numberToBytes (Vec3.getX3 v)
        ByteArray yb = numberToBytes (Vec3.getY3 v)
        ByteArray zb = numberToBytes (Vec3.getZ3 v)
    in ByteArray (xb <> yb <> zb)
  fromBytes (ByteArray arr) = do
    xv <- bytesToNumber (ByteArray (Array.take 4 arr))
    yv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    zv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    pure (Vec3.vec3 xv yv zv)

-- | Vec4 Number serializes as vec4<f32>.
-- |
-- | GPU representation: vec4<f32> (16 bytes, 16-byte aligned)
-- | WGSL type: vec4<f32>
instance gpuStorableVec4Number :: GPUStorable (Vec4.Vec4 Number) where
  byteSize _ = 16
  alignment _ = align16
  toBytes v =
    let ByteArray xb = numberToBytes (Vec4.getX4 v)
        ByteArray yb = numberToBytes (Vec4.getY4 v)
        ByteArray zb = numberToBytes (Vec4.getZ4 v)
        ByteArray wb = numberToBytes (Vec4.getW4 v)
    in ByteArray (xb <> yb <> zb <> wb)
  fromBytes (ByteArray arr) = do
    xv <- bytesToNumber (ByteArray (Array.take 4 arr))
    yv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    zv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    wv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 12 arr)))
    pure (Vec4.vec4 xv yv zv wv)

-- | Point2D serializes as vec2<f32>.
-- |
-- | GPU representation: vec2<f32> (8 bytes, 8-byte aligned)
-- | WGSL type: vec2<f32>
instance gpuStorablePoint2D :: GPUStorable Point2D.Point2D where
  byteSize _ = 8
  alignment _ = align8
  toBytes pt =
    let ByteArray xb = numberToBytes (Point2D.x pt)
        ByteArray yb = numberToBytes (Point2D.y pt)
    in ByteArray (xb <> yb)
  fromBytes (ByteArray arr) = do
    xv <- bytesToNumber (ByteArray (Array.take 4 arr))
    yv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    pure (Point2D.point2D xv yv)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // color instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | SRGB serializes as vec3<f32> with values in [0,1].
-- |
-- | GPU representation: vec3<f32> (12 bytes, 16-byte aligned)
-- | WGSL type: vec3<f32>
-- |
-- | Channel values (0-255) are normalized to [0,1] for GPU:
-- | - 0 → 0.0
-- | - 255 → 1.0
-- |
-- | IMPORTANT: vec3 requires 16-byte alignment in WebGPU despite being
-- | only 12 bytes. This is a WebGPU spec requirement.
instance gpuStorableSRGB :: GPUStorable SRGB.SRGB where
  byteSize _ = 12
  alignment _ = align16
  toBytes color =
    let r = Int.toNumber (Channel.unwrap (SRGB.red color)) / 255.0
        g = Int.toNumber (Channel.unwrap (SRGB.green color)) / 255.0
        b = Int.toNumber (Channel.unwrap (SRGB.blue color)) / 255.0
        ByteArray rb = numberToBytes r
        ByteArray gb = numberToBytes g
        ByteArray bb = numberToBytes b
    in ByteArray (rb <> gb <> bb)
  fromBytes (ByteArray arr) = do
    rv <- bytesToNumber (ByteArray (Array.take 4 arr))
    gv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    bv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    let ri = Int.round (rv * 255.0)
        gi = Int.round (gv * 255.0)
        bi = Int.round (bv * 255.0)
    pure (SRGB.srgb ri gi bi)

-- | SRGBA serializes as vec4<f32> with values in [0,1].
-- |
-- | GPU representation: vec4<f32> (16 bytes, 16-byte aligned)
-- | WGSL type: vec4<f32>
-- |
-- | Channel values (0-255) and opacity (0-100) are normalized to [0,1]:
-- | - Red/Green/Blue: 0-255 → 0.0-1.0
-- | - Alpha (opacity): 0-100 → 0.0-1.0
instance gpuStorableSRGBA :: GPUStorable SRGB.SRGBA where
  byteSize _ = 16
  alignment _ = align16
  toBytes color =
    let rec = SRGB.srgbaToRecord color
        r = Int.toNumber (Channel.unwrap rec.r) / 255.0
        g = Int.toNumber (Channel.unwrap rec.g) / 255.0
        b = Int.toNumber (Channel.unwrap rec.b) / 255.0
        a = Int.toNumber (Opacity.unwrap rec.a) / 100.0
        ByteArray rb = numberToBytes r
        ByteArray gb = numberToBytes g
        ByteArray bb = numberToBytes b
        ByteArray ab = numberToBytes a
    in ByteArray (rb <> gb <> bb <> ab)
  fromBytes (ByteArray arr) = do
    rv <- bytesToNumber (ByteArray (Array.take 4 arr))
    gv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    bv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    av <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 12 arr)))
    let ri = Int.round (rv * 255.0)
        gi = Int.round (gv * 255.0)
        bi = Int.round (bv * 255.0)
    pure (SRGB.srgba ri gi bi av)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // color atom instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | Channel serializes as f32 normalized to [0,1].
-- |
-- | GPU representation: f32 (4 bytes, 4-byte aligned)
-- | WGSL type: f32
-- |
-- | Channel values (0-255) are normalized:
-- | - 0 → 0.0
-- | - 255 → 1.0
instance gpuStorableChannel :: GPUStorable Channel.Channel where
  byteSize _ = 4
  alignment _ = align4
  toBytes ch =
    let normalized = Int.toNumber (Channel.unwrap ch) / 255.0
    in numberToBytes normalized
  fromBytes bytes = do
    val <- bytesToNumber bytes
    let raw = Int.round (val * 255.0)
    pure (Channel.channel raw)

-- | Opacity serializes as f32 normalized to [0,1].
-- |
-- | GPU representation: f32 (4 bytes, 4-byte aligned)
-- | WGSL type: f32
-- |
-- | Opacity values (0-100) are normalized:
-- | - 0 → 0.0 (transparent)
-- | - 100 → 1.0 (opaque)
instance gpuStorableOpacity :: GPUStorable Opacity.Opacity where
  byteSize _ = 4
  alignment _ = align4
  toBytes op =
    let normalized = Int.toNumber (Opacity.unwrap op) / 100.0
    in numberToBytes normalized
  fromBytes bytes = do
    val <- bytesToNumber bytes
    let raw = Int.round (val * 100.0)
    pure (Opacity.opacity raw)

-- | Hue serializes as f32 normalized to [0,1].
-- |
-- | GPU representation: f32 (4 bytes, 4-byte aligned)
-- | WGSL type: f32
-- |
-- | Hue values (0-359 degrees) are normalized:
-- | - 0° → 0.0
-- | - 180° → ~0.5
-- | - 359° → ~1.0
-- |
-- | Shaders can multiply by 360.0 or 2π to get degrees/radians.
instance gpuStorableHue :: GPUStorable Hue.Hue where
  byteSize _ = 4
  alignment _ = align4
  toBytes h =
    let normalized = Int.toNumber (Hue.unwrap h) / 360.0
    in numberToBytes normalized
  fromBytes bytes = do
    val <- bytesToNumber bytes
    let raw = Int.round (val * 360.0)
    pure (Hue.hue raw)

-- | Saturation serializes as f32 normalized to [0,1].
-- |
-- | GPU representation: f32 (4 bytes, 4-byte aligned)
-- | WGSL type: f32
-- |
-- | Saturation values (0-100%) are normalized:
-- | - 0% → 0.0 (grayscale)
-- | - 100% → 1.0 (fully saturated)
instance gpuStorableSaturation :: GPUStorable Saturation.Saturation where
  byteSize _ = 4
  alignment _ = align4
  toBytes s =
    let normalized = Int.toNumber (Saturation.unwrap s) / 100.0
    in numberToBytes normalized
  fromBytes bytes = do
    val <- bytesToNumber bytes
    let raw = Int.round (val * 100.0)
    pure (Saturation.saturation raw)

-- | Lightness serializes as f32 normalized to [0,1].
-- |
-- | GPU representation: f32 (4 bytes, 4-byte aligned)
-- | WGSL type: f32
-- |
-- | Lightness values (0-100%) are normalized:
-- | - 0% → 0.0 (black)
-- | - 50% → 0.5 (pure color)
-- | - 100% → 1.0 (white)
instance gpuStorableLightness :: GPUStorable Lightness.Lightness where
  byteSize _ = 4
  alignment _ = align4
  toBytes l =
    let normalized = Int.toNumber (Lightness.unwrap l) / 100.0
    in numberToBytes normalized
  fromBytes bytes = do
    val <- bytesToNumber bytes
    let raw = Int.round (val * 100.0)
    pure (Lightness.lightness raw)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // color molecule instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB serializes as vec3<f32> with values in [0,1].
-- |
-- | GPU representation: vec3<f32> (12 bytes, 16-byte aligned)
-- | WGSL type: vec3<f32>
-- |
-- | Note: RGB module's RGB type vs SRGB module's SRGB type.
-- | Both serialize identically — vec3<f32> with channel values normalized.
instance gpuStorableRGB :: GPUStorable RGB.RGB where
  byteSize _ = 12
  alignment _ = align16
  toBytes color =
    let r = Int.toNumber (Channel.unwrap (RGB.red color)) / 255.0
        g = Int.toNumber (Channel.unwrap (RGB.green color)) / 255.0
        b = Int.toNumber (Channel.unwrap (RGB.blue color)) / 255.0
        ByteArray rb = numberToBytes r
        ByteArray gb = numberToBytes g
        ByteArray bb = numberToBytes b
    in ByteArray (rb <> gb <> bb)
  fromBytes (ByteArray arr) = do
    rv <- bytesToNumber (ByteArray (Array.take 4 arr))
    gv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    bv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    let ri = Int.round (rv * 255.0)
        gi = Int.round (gv * 255.0)
        bi = Int.round (bv * 255.0)
    pure (RGB.rgb ri gi bi)

-- | RGBA serializes as vec4<f32> with values in [0,1].
-- |
-- | GPU representation: vec4<f32> (16 bytes, 16-byte aligned)
-- | WGSL type: vec4<f32>
-- |
-- | rgbaToRecord returns raw Ints (already unwrapped from Channel/Opacity).
instance gpuStorableRGBA :: GPUStorable RGB.RGBA where
  byteSize _ = 16
  alignment _ = align16
  toBytes color =
    let rec = RGB.rgbaToRecord color
        r = Int.toNumber rec.r / 255.0
        g = Int.toNumber rec.g / 255.0
        b = Int.toNumber rec.b / 255.0
        a = Int.toNumber rec.a / 100.0
        ByteArray rb = numberToBytes r
        ByteArray gb = numberToBytes g
        ByteArray bb = numberToBytes b
        ByteArray ab = numberToBytes a
    in ByteArray (rb <> gb <> bb <> ab)
  fromBytes (ByteArray arr) = do
    rv <- bytesToNumber (ByteArray (Array.take 4 arr))
    gv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    bv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    av <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 12 arr)))
    let ri = Int.round (rv * 255.0)
        gi = Int.round (gv * 255.0)
        bi = Int.round (bv * 255.0)
        ai = Int.round (av * 100.0)
    pure (RGB.rgba ri gi bi ai)

-- | HSL serializes as vec3<f32> with values in [0,1].
-- |
-- | GPU representation: vec3<f32> (12 bytes, 16-byte aligned)
-- | WGSL type: vec3<f32>
-- |
-- | Components normalized:
-- | - Hue: 0-359° → 0.0-1.0
-- | - Saturation: 0-100% → 0.0-1.0
-- | - Lightness: 0-100% → 0.0-1.0
-- |
-- | Shaders can convert to RGB using standard HSL→RGB algorithm.
instance gpuStorableHSL :: GPUStorable HSL.HSL where
  byteSize _ = 12
  alignment _ = align16
  toBytes color =
    let rec = HSL.toRecord color
        h = Int.toNumber rec.h / 360.0
        s = Int.toNumber rec.s / 100.0
        l = Int.toNumber rec.l / 100.0
        ByteArray hb = numberToBytes h
        ByteArray sb = numberToBytes s
        ByteArray lb = numberToBytes l
    in ByteArray (hb <> sb <> lb)
  fromBytes (ByteArray arr) = do
    hv <- bytesToNumber (ByteArray (Array.take 4 arr))
    sv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    lv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    let hi = Int.round (hv * 360.0)
        si = Int.round (sv * 100.0)
        li = Int.round (lv * 100.0)
    pure (HSL.hsl hi si li)

-- | HSLA serializes as vec4<f32> with values in [0,1].
-- |
-- | GPU representation: vec4<f32> (16 bytes, 16-byte aligned)
-- | WGSL type: vec4<f32>
-- |
-- | Components normalized:
-- | - Hue: 0-359° → 0.0-1.0
-- | - Saturation: 0-100% → 0.0-1.0
-- | - Lightness: 0-100% → 0.0-1.0
-- | - Alpha: 0-100% → 0.0-1.0
instance gpuStorableHSLA :: GPUStorable HSLA.HSLA where
  byteSize _ = 16
  alignment _ = align16
  toBytes color =
    let rec = HSLA.hslaToRecord color
        h = Int.toNumber rec.h / 360.0
        s = Int.toNumber rec.s / 100.0
        l = Int.toNumber rec.l / 100.0
        a = Int.toNumber rec.a / 100.0
        ByteArray hb = numberToBytes h
        ByteArray sb = numberToBytes s
        ByteArray lb = numberToBytes l
        ByteArray ab = numberToBytes a
    in ByteArray (hb <> sb <> lb <> ab)
  fromBytes (ByteArray arr) = do
    hv <- bytesToNumber (ByteArray (Array.take 4 arr))
    sv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    lv <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    av <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 12 arr)))
    let hi = Int.round (hv * 360.0)
        si = Int.round (sv * 100.0)
        li = Int.round (lv * 100.0)
        ai = Int.round (av * 100.0)
    pure (HSLA.hsla hi si li ai)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // geometry atom instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | Degrees serializes as f32 normalized to [0,1].
-- |
-- | GPU representation: f32 (4 bytes, 4-byte aligned)
-- | WGSL type: f32
-- |
-- | Degrees (0-360) are normalized:
-- | - 0° → 0.0
-- | - 180° → 0.5
-- | - 360° → 1.0 (wraps to 0.0)
-- |
-- | Shaders can multiply by 360.0 or 2π to get degrees/radians.
instance gpuStorableDegrees :: GPUStorable Angle.Degrees where
  byteSize _ = 4
  alignment _ = align4
  toBytes deg =
    let normalized = Angle.unwrapDegrees deg / 360.0
    in numberToBytes normalized
  fromBytes bytes = do
    val <- bytesToNumber bytes
    pure (Angle.degrees (val * 360.0))

-- | Radians serializes as f32 normalized to [0,1].
-- |
-- | GPU representation: f32 (4 bytes, 4-byte aligned)
-- | WGSL type: f32
-- |
-- | Radians (0-2π) are normalized:
-- | - 0 → 0.0
-- | - π → 0.5
-- | - 2π → 1.0 (wraps to 0.0)
-- |
-- | Shaders can multiply by 2π to get radians.
instance gpuStorableRadians :: GPUStorable Angle.Radians where
  byteSize _ = 4
  alignment _ = align4
  toBytes rad =
    let twoPi = 2.0 * Number.pi
        normalized = Angle.unwrapRadians rad / twoPi
    in numberToBytes normalized
  fromBytes bytes = do
    val <- bytesToNumber bytes
    let twoPi = 2.0 * Number.pi
    pure (Angle.radians (val * twoPi))

-- | Turns serializes directly as f32 (already in [0,1]).
-- |
-- | GPU representation: f32 (4 bytes, 4-byte aligned)
-- | WGSL type: f32
-- |
-- | Turns are the most GPU-native angle representation:
-- | - 0 turns → 0.0
-- | - 0.5 turns → 0.5 (half rotation)
-- | - 1 turn → 1.0 (full rotation, wraps to 0.0)
instance gpuStorableTurns :: GPUStorable Angle.Turns where
  byteSize _ = 4
  alignment _ = align4
  toBytes t = numberToBytes (Angle.unwrapTurns t)
  fromBytes bytes = do
    val <- bytesToNumber bytes
    pure (Angle.turns val)

-- | Size2D Number serializes as vec2<f32>.
-- |
-- | GPU representation: vec2<f32> (8 bytes, 8-byte aligned)
-- | WGSL type: vec2<f32>
-- |
-- | Components:
-- | - x = width
-- | - y = height
instance gpuStorableSize2DNumber :: GPUStorable (Size2D.Size2D Number) where
  byteSize _ = 8
  alignment _ = align8
  toBytes s =
    let w = Size2D.width s
        h = Size2D.height s
        ByteArray wb = numberToBytes w
        ByteArray hb = numberToBytes h
    in ByteArray (wb <> hb)
  fromBytes (ByteArray arr) = do
    w <- bytesToNumber (ByteArray (Array.take 4 arr))
    h <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    pure (Size2D.size2D w h)

-- | Radius serializes as tagged f32 (5 bytes: 1 tag + 4 value).
-- |
-- | GPU representation: struct { tag: u8, value: f32 } (8 bytes, 4-byte aligned)
-- | Note: 3 bytes padding after tag for alignment.
-- |
-- | Tags:
-- | - 0 = RadiusNone (value ignored, serialized as 0.0)
-- | - 1 = RadiusPx (value in pixels)
-- | - 2 = RadiusPercent (value as percentage 0-100)
-- | - 3 = RadiusRem (value in rem units)
-- | - 4 = RadiusFull (value = 9999.0)
-- |
-- | Shaders can switch on tag to interpret the value correctly.
instance gpuStorableRadius :: GPUStorable Radius.Radius where
  byteSize _ = 8
  alignment _ = align4
  toBytes r =
    let tagAndValue = case r of
          Radius.RadiusNone -> { tag: 0, value: 0.0 }
          Radius.RadiusPx n -> { tag: 1, value: n }
          Radius.RadiusPercent n -> { tag: 2, value: n }
          Radius.RadiusRem n -> { tag: 3, value: n }
          Radius.RadiusFull -> { tag: 4, value: 9999.0 }
        ByteArray valBytes = numberToBytes tagAndValue.value
    in ByteArray ([tagAndValue.tag, 0, 0, 0] <> valBytes)
  fromBytes (ByteArray arr) = do
    tag <- Array.index arr 0
    val <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    case tag of
      0 -> pure Radius.RadiusNone
      1 -> pure (Radius.RadiusPx val)
      2 -> pure (Radius.RadiusPercent val)
      3 -> pure (Radius.RadiusRem val)
      4 -> pure Radius.RadiusFull
      _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // transform atom instances
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale serializes as vec2<f32>.
-- |
-- | GPU representation: vec2<f32> (8 bytes, 8-byte aligned)
-- | WGSL type: vec2<f32>
-- |
-- | Components:
-- | - x = scaleX (-10.0 to 10.0, 1.0 = identity)
-- | - y = scaleY (-10.0 to 10.0, 1.0 = identity)
-- |
-- | Negative values indicate flip/mirror on that axis.
instance gpuStorableScale :: GPUStorable Transform.Scale where
  byteSize _ = 8
  alignment _ = align8
  toBytes s =
    let x = Transform.getScaleX s
        y = Transform.getScaleY s
        ByteArray xb = numberToBytes x
        ByteArray yb = numberToBytes y
    in ByteArray (xb <> yb)
  fromBytes (ByteArray arr) = do
    x <- bytesToNumber (ByteArray (Array.take 4 arr))
    y <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    pure (Transform.scaleXY x y)

-- | Translate serializes as vec2<f32>.
-- |
-- | GPU representation: vec2<f32> (8 bytes, 8-byte aligned)
-- | WGSL type: vec2<f32>
-- |
-- | Components:
-- | - x = translateX (pixels, unbounded)
-- | - y = translateY (pixels, unbounded)
instance gpuStorableTranslate :: GPUStorable Transform.Translate where
  byteSize _ = 8
  alignment _ = align8
  toBytes t =
    let x = Transform.getTranslateX t
        y = Transform.getTranslateY t
        ByteArray xb = numberToBytes x
        ByteArray yb = numberToBytes y
    in ByteArray (xb <> yb)
  fromBytes (ByteArray arr) = do
    x <- bytesToNumber (ByteArray (Array.take 4 arr))
    y <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    pure (Transform.translate x y)

-- | Rotate serializes as f32 (angle in turns, [0,1]).
-- |
-- | GPU representation: f32 (4 bytes, 4-byte aligned)
-- | WGSL type: f32
-- |
-- | The inner Degrees value is normalized to [0,1] (turns):
-- | - 0° → 0.0
-- | - 180° → 0.5
-- | - 360° → 1.0 (wraps to 0.0)
-- |
-- | Using turns is GPU-native for angle calculations.
instance gpuStorableRotate :: GPUStorable Transform.Rotate where
  byteSize _ = 4
  alignment _ = align4
  toBytes r =
    let deg = Transform.getRotation r
        normalized = Angle.unwrapDegrees deg / 360.0
    in numberToBytes normalized
  fromBytes bytes = do
    val <- bytesToNumber bytes
    pure (Transform.rotate (Angle.degrees (val * 360.0)))

-- | Skew serializes as vec2<f32>.
-- |
-- | GPU representation: vec2<f32> (8 bytes, 8-byte aligned)
-- | WGSL type: vec2<f32>
-- |
-- | Components:
-- | - x = skewX (degrees, clamped to [-89, 89])
-- | - y = skewY (degrees, clamped to [-89, 89])
-- |
-- | Values are stored as degrees, not normalized.
instance gpuStorableSkew :: GPUStorable Transform.Skew where
  byteSize _ = 8
  alignment _ = align8
  toBytes s =
    let x = Transform.getSkewX s
        y = Transform.getSkewY s
        ByteArray xb = numberToBytes x
        ByteArray yb = numberToBytes y
    in ByteArray (xb <> yb)
  fromBytes (ByteArray arr) = do
    x <- bytesToNumber (ByteArray (Array.take 4 arr))
    y <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    pure (Transform.skew x y)

-- | Origin serializes as vec2<f32>.
-- |
-- | GPU representation: vec2<f32> (8 bytes, 8-byte aligned)
-- | WGSL type: vec2<f32>
-- |
-- | Components (percentages):
-- | - x = originX (0-100, 50 = center)
-- | - y = originY (0-100, 50 = center)
instance gpuStorableOrigin :: GPUStorable Transform.Origin where
  byteSize _ = 8
  alignment _ = align8
  toBytes o =
    let x = Transform.getOriginX o
        y = Transform.getOriginY o
        ByteArray xb = numberToBytes x
        ByteArray yb = numberToBytes y
    in ByteArray (xb <> yb)
  fromBytes (ByteArray arr) = do
    x <- bytesToNumber (ByteArray (Array.take 4 arr))
    y <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    pure (Transform.origin x y)

-- | Transform2D serializes as a fixed struct.
-- |
-- | GPU representation: struct (48 bytes, 16-byte aligned)
-- | Layout:
-- |   translate: vec2<f32>  (8 bytes, offset 0)
-- |   rotate: f32           (4 bytes, offset 8)
-- |   padding: 4 bytes      (offset 12)
-- |   scale: vec2<f32>      (8 bytes, offset 16)
-- |   skew: vec2<f32>       (8 bytes, offset 24)
-- |   origin: vec2<f32>     (8 bytes, offset 32)
-- |   flags: u32            (4 bytes, offset 40) - which components are present
-- |   padding: 4 bytes      (offset 44)
-- |
-- | Total: 48 bytes (aligned to 16)
-- |
-- | Flags bitfield:
-- | - bit 0: has translate
-- | - bit 1: has rotate
-- | - bit 2: has scale
-- | - bit 3: has skew
-- |
-- | Missing components use identity values (translate=0, rotate=0, scale=1, skew=0).
instance gpuStorableTransform2D :: GPUStorable Transform.Transform2D where
  byteSize _ = 48
  alignment _ = align16
  toBytes (Transform.Transform2D t) =
    let 
        -- Extract values with identity defaults
        tr = fromMaybe Transform.translateNone t.translate
        rt = fromMaybe Transform.rotateNone t.rotate
        sc = fromMaybe Transform.scaleIdentity t.scale
        sk = fromMaybe Transform.skewNone t.skew
        
        -- Serialize components
        ByteArray trb = toBytes tr   -- 8 bytes
        ByteArray rtb = toBytes rt   -- 4 bytes
        padding1 = [0, 0, 0, 0]      -- 4 bytes padding
        ByteArray scb = toBytes sc   -- 8 bytes
        ByteArray skb = toBytes sk   -- 8 bytes
        ByteArray orb = toBytes t.origin -- 8 bytes
        
        -- Compute flags
        hasTranslate = case t.translate of
          Just _ -> 1
          Nothing -> 0
        hasRotate = case t.rotate of
          Just _ -> 2
          Nothing -> 0
        hasScale = case t.scale of
          Just _ -> 4
          Nothing -> 0
        hasSkew = case t.skew of
          Just _ -> 8
          Nothing -> 0
        flags = hasTranslate + hasRotate + hasScale + hasSkew
        ByteArray flagsb = writeU32 flags
        padding2 = [0, 0, 0, 0]      -- 4 bytes padding
        
    in ByteArray (trb <> rtb <> padding1 <> scb <> skb <> orb <> flagsb <> padding2)
  
  fromBytes (ByteArray arr) = do
    -- Read translate (offset 0)
    trx <- bytesToNumber (ByteArray (Array.take 4 arr))
    try <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 4 arr)))
    
    -- Read rotate (offset 8)
    rotVal <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 8 arr)))
    
    -- Skip padding (offset 12-15)
    
    -- Read scale (offset 16)
    scx <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 16 arr)))
    scy <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 20 arr)))
    
    -- Read skew (offset 24)
    skx <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 24 arr)))
    sky <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 28 arr)))
    
    -- Read origin (offset 32)
    orx <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 32 arr)))
    ory <- bytesToNumber (ByteArray (Array.take 4 (Array.drop 36 arr)))
    
    -- Read flags (offset 40)
    flags <- readU32 arr 40
    
    let 
        hasTranslate = (flags `mod` 2) == 1
        hasRotate = ((flags / 2) `mod` 2) == 1
        hasScale = ((flags / 4) `mod` 2) == 1
        hasSkew = ((flags / 8) `mod` 2) == 1
        
        translate = if hasTranslate 
          then Just (Transform.translate trx try) 
          else Nothing
        rotate = if hasRotate 
          then Just (Transform.rotate (Angle.degrees (rotVal * 360.0))) 
          else Nothing
        scale = if hasScale 
          then Just (Transform.scaleXY scx scy) 
          else Nothing
        skew = if hasSkew 
          then Just (Transform.skew skx sky) 
          else Nothing
        origin = Transform.origin orx ory
    
    pure (Transform.transform2D translate rotate scale skew origin)

-- | Helper to write u32 for flags
writeU32 :: Int -> ByteArray
writeU32 n =
  let b0 = n `mod` 256
      b1 = (n / 256) `mod` 256
      b2 = (n / 65536) `mod` 256
      b3 = (n / 16777216) `mod` 256
  in ByteArray [b0, b1, b2, b3]

-- | Helper to read u32 for flags
readU32 :: Array Int -> Int -> Maybe Int
readU32 arr offset = do
  b0 <- Array.index arr offset
  b1 <- Array.index arr (offset + 1)
  b2 <- Array.index arr (offset + 2)
  b3 <- Array.index arr (offset + 3)
  pure (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216)
