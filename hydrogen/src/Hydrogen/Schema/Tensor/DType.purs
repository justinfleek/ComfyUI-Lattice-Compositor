-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // tensor // dtype
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DType — Tensor element data types for ML inference.
-- |
-- | ## Design Philosophy
-- |
-- | Tensor data types define how individual elements are stored and computed.
-- | This module provides bounded atoms for all common ML precision formats,
-- | including cutting-edge quantization formats from NVIDIA TensorRT-LLM.
-- |
-- | ## Format Categories
-- |
-- | **Standard IEEE Formats**:
-- | - Float32 (FP32): Full precision, 32 bits
-- | - Float16 (FP16): Half precision, 16 bits
-- | - BFloat16 (BF16): Brain float, 16 bits (8 exp, 7 mantissa)
-- |
-- | **NVIDIA 8-bit Formats**:
-- | - FP8_E4M3: 8 bits (4 exp, 3 mantissa) — higher precision
-- | - FP8_E5M2: 8 bits (5 exp, 2 mantissa) — wider range
-- |
-- | **NVIDIA 4-bit Formats** (TensorRT-LLM):
-- | - NVFP4 (FP4_E2M1): 4 bits (2 exp, 1 mantissa, no inf/NaN)
-- | - MXFP4: Microscaling FP4 with block-level scaling factors
-- | - INT4: 4-bit integer quantization
-- |
-- | **Integer Quantization**:
-- | - INT8: 8-bit integer (signed or unsigned)
-- | - INT4: 4-bit integer (weight-only quantization)
-- |
-- | ## Quantization Modes
-- |
-- | From TensorRT-LLM quantization.mode:
-- | - W8A8: Weights and activations both INT8
-- | - W4A16: Weights INT4, activations FP16
-- | - W4A8_NVFP4_FP8: Weights NVFP4, activations FP8
-- | - W4A8_MXFP4_FP8: Weights MXFP4, activations FP8
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show)

module Hydrogen.Schema.Tensor.DType
  ( -- * Core Data Types
    DType(..)
  , FloatFormat(..)
  , IntFormat(..)
  , QuantFormat(..)
  
  -- * Constructors
  , float32
  , float16
  , bfloat16
  , fp8e4m3
  , fp8e5m2
  , nvfp4
  , mxfp4
  , int8
  , uint8
  , int4
  , int32
  , int64
  , bool
  
  -- * Quantization Types
  , QuantMode(..)
  , quantW8A8
  , quantW4A16
  , quantW4A8NVFP4
  , quantW4A8MXFP4
  , quantFP8
  , quantNone
  
  -- * Properties
  , bitWidth
  , byteWidth
  , isFloatingPoint
  , isInteger
  , isQuantized
  , isSigned
  , hasInfNaN
  , exponentBits
  , mantissaBits
  
  -- * Precision Comparison
  , higherPrecision
  , lowerPrecision
  , canCastTo
  , commonType
  
  -- * Memory Calculation
  , elementsPerByte
  , bytesForElements
  
  -- * String Representation
  , dtypeToString
  , quantModeToString
  
  -- * Validation
  , isCompatiblePair
  , isNumeric
  , requiresScaling
  , supportedQuantModes
  , weightDType
  , activationDType
  
  -- * Transformation
  , promoteTo
  , mapBaseType
  , describeType
  , bitWidths
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , pure
  , bind
  , map
  , (==)
  , (/=)
  , (<>)
  , (>)
  , (>=)
  , (<)
  , (<=)
  , (&&)
  , (||)
  , ($)
  , (/)
  , (*)
  , (+)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // float format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Floating point format specification.
-- |
-- | Defines the bit layout: sign, exponent, mantissa, and special value handling.
data FloatFormat
  = IEEE_FP32      -- ^ 1 sign, 8 exp, 23 mantissa (standard float)
  | IEEE_FP16      -- ^ 1 sign, 5 exp, 10 mantissa (half precision)
  | BF16           -- ^ 1 sign, 8 exp, 7 mantissa (brain float)
  | FP8_E4M3       -- ^ 1 sign, 4 exp, 3 mantissa (NVIDIA FP8)
  | FP8_E5M2       -- ^ 1 sign, 5 exp, 2 mantissa (NVIDIA FP8)
  | FP4_E2M1       -- ^ 1 sign, 2 exp, 1 mantissa (NVFP4, no inf/NaN)
  | MXFP4_E2M1     -- ^ FP4 with microscaling (block scale factors)

derive instance eqFloatFormat :: Eq FloatFormat
derive instance ordFloatFormat :: Ord FloatFormat

instance showFloatFormat :: Show FloatFormat where
  show IEEE_FP32 = "FP32"
  show IEEE_FP16 = "FP16"
  show BF16 = "BF16"
  show FP8_E4M3 = "FP8_E4M3"
  show FP8_E5M2 = "FP8_E5M2"
  show FP4_E2M1 = "NVFP4"
  show MXFP4_E2M1 = "MXFP4"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // int format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Integer format specification.
data IntFormat
  = Int4Signed     -- ^ 4-bit signed integer (-8 to 7)
  | Int4Unsigned   -- ^ 4-bit unsigned integer (0 to 15)
  | Int8Signed     -- ^ 8-bit signed integer (-128 to 127)
  | Int8Unsigned   -- ^ 8-bit unsigned integer (0 to 255)
  | Int16Signed    -- ^ 16-bit signed integer
  | Int32Signed    -- ^ 32-bit signed integer
  | Int64Signed    -- ^ 64-bit signed integer
  | Bool           -- ^ Boolean (1 bit logical, typically 8 bits storage)

derive instance eqIntFormat :: Eq IntFormat
derive instance ordIntFormat :: Ord IntFormat

instance showIntFormat :: Show IntFormat where
  show Int4Signed = "INT4"
  show Int4Unsigned = "UINT4"
  show Int8Signed = "INT8"
  show Int8Unsigned = "UINT8"
  show Int16Signed = "INT16"
  show Int32Signed = "INT32"
  show Int64Signed = "INT64"
  show Bool = "BOOL"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // quant format
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quantization format specification.
-- |
-- | Quantized formats require scale factors and sometimes zero points.
data QuantFormat
  = PerTensor      -- ^ Single scale for entire tensor
  | PerChannel     -- ^ Scale per output channel
  | PerGroup       -- ^ Scale per group of elements (e.g., 128 elements)
      { groupSize :: Int }
  | PerBlock       -- ^ Microscaling: scale per block (MXFP4)
      { blockSize :: Int }

derive instance eqQuantFormat :: Eq QuantFormat
derive instance ordQuantFormat :: Ord QuantFormat

instance showQuantFormat :: Show QuantFormat where
  show PerTensor = "PerTensor"
  show PerChannel = "PerChannel"
  show (PerGroup g) = "PerGroup(" <> show g.groupSize <> ")"
  show (PerBlock b) = "PerBlock(" <> show b.blockSize <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // dtype
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tensor element data type.
-- |
-- | Encompasses all supported numeric formats for tensor elements.
data DType
  = FloatType FloatFormat
  | IntType IntFormat
  | QuantizedType
      { baseType :: DType       -- ^ Underlying storage type
      , quantFormat :: QuantFormat  -- ^ How scales are applied
      }

derive instance eqDType :: Eq DType

instance showDType :: Show DType where
  show = dtypeToString

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | 32-bit IEEE floating point
float32 :: DType
float32 = FloatType IEEE_FP32

-- | 16-bit IEEE floating point (half precision)
float16 :: DType
float16 = FloatType IEEE_FP16

-- | 16-bit Brain Float (wider range than FP16)
bfloat16 :: DType
bfloat16 = FloatType BF16

-- | 8-bit float with 4 exponent, 3 mantissa bits
-- |
-- | Higher precision variant of FP8. Preferred for inference.
fp8e4m3 :: DType
fp8e4m3 = FloatType FP8_E4M3

-- | 8-bit float with 5 exponent, 2 mantissa bits
-- |
-- | Wider dynamic range variant of FP8. Preferred for training gradients.
fp8e5m2 :: DType
fp8e5m2 = FloatType FP8_E5M2

-- | NVIDIA 4-bit float (FP4_E2M1)
-- |
-- | 4 bits total: 1 sign, 2 exponent, 1 mantissa.
-- | No infinity or NaN representations (all bit patterns are finite).
-- | Used in TensorRT-LLM for weight quantization.
nvfp4 :: DType
nvfp4 = FloatType FP4_E2M1

-- | Microscaling FP4 (MXFP4)
-- |
-- | Like NVFP4 but with block-level scaling factors for better accuracy.
-- | Each block of values shares a common scale factor.
mxfp4 :: DType
mxfp4 = FloatType MXFP4_E2M1

-- | 8-bit signed integer
int8 :: DType
int8 = IntType Int8Signed

-- | 8-bit unsigned integer
uint8 :: DType
uint8 = IntType Int8Unsigned

-- | 4-bit signed integer (for weight quantization)
int4 :: DType
int4 = IntType Int4Signed

-- | 32-bit signed integer
int32 :: DType
int32 = IntType Int32Signed

-- | 64-bit signed integer
int64 :: DType
int64 = IntType Int64Signed

-- | Boolean type
bool :: DType
bool = IntType Bool

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // quantization modes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quantization mode for model weights and activations.
-- |
-- | Nomenclature: W{bits}A{bits} means weights at {bits} and activations at {bits}.
-- | From TensorRT-LLM quantization.mode.QuantAlgo.
data QuantMode
  = NoQuant                    -- ^ No quantization (full precision)
  | W8A8_SQ                    -- ^ SmoothQuant: INT8 weights, INT8 activations
  | W8A16                      -- ^ INT8 weights, FP16 activations
  | W4A16                      -- ^ INT4 weights, FP16 activations (AWQ/GPTQ style)
  | W4A16_AWQ                  -- ^ Activation-aware Weight Quantization
  | W4A16_GPTQ                 -- ^ GPTQ quantization
  | FP8_Linear                 -- ^ FP8 for linear layers only
  | FP8_Full                   -- ^ FP8 for all operations
  | W4A8_NVFP4_FP8             -- ^ NVFP4 weights, FP8 activations
  | W4A8_MXFP4_FP8             -- ^ MXFP4 weights, FP8 activations
  | W8A8_FP8                   -- ^ FP8 weights, FP8 activations

derive instance eqQuantMode :: Eq QuantMode
derive instance ordQuantMode :: Ord QuantMode

instance showQuantMode :: Show QuantMode where
  show = quantModeToString

-- | No quantization
quantNone :: QuantMode
quantNone = NoQuant

-- | INT8 weights and activations (SmoothQuant)
quantW8A8 :: QuantMode
quantW8A8 = W8A8_SQ

-- | INT4 weights, FP16 activations
quantW4A16 :: QuantMode
quantW4A16 = W4A16

-- | NVFP4 weights, FP8 activations
-- |
-- | State-of-the-art quantization from NVIDIA Blackwell architecture.
quantW4A8NVFP4 :: QuantMode
quantW4A8NVFP4 = W4A8_NVFP4_FP8

-- | MXFP4 weights, FP8 activations
-- |
-- | Microscaling variant for higher accuracy.
quantW4A8MXFP4 :: QuantMode
quantW4A8MXFP4 = W4A8_MXFP4_FP8

-- | FP8 quantization
quantFP8 :: QuantMode
quantFP8 = FP8_Full

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get bit width of data type
bitWidth :: DType -> Int
bitWidth (FloatType fmt) = floatBitWidth fmt
bitWidth (IntType fmt) = intBitWidth fmt
bitWidth (QuantizedType q) = bitWidth q.baseType

-- | Get byte width (rounded up for sub-byte types)
byteWidth :: DType -> Int
byteWidth dtype = 
  let bits = bitWidth dtype
  in if bits < 8 then 1 else bits / 8

-- | Is this a floating point type?
isFloatingPoint :: DType -> Boolean
isFloatingPoint (FloatType _) = true
isFloatingPoint (IntType _) = false
isFloatingPoint (QuantizedType q) = isFloatingPoint q.baseType

-- | Is this an integer type?
isInteger :: DType -> Boolean
isInteger (FloatType _) = false
isInteger (IntType _) = true
isInteger (QuantizedType q) = isInteger q.baseType

-- | Is this a quantized type?
isQuantized :: DType -> Boolean
isQuantized (QuantizedType _) = true
isQuantized _ = false

-- | Is this type signed?
isSigned :: DType -> Boolean
isSigned (FloatType _) = true  -- All floats are signed
isSigned (IntType Int4Unsigned) = false
isSigned (IntType Int8Unsigned) = false
isSigned (IntType Bool) = false
isSigned (IntType _) = true
isSigned (QuantizedType q) = isSigned q.baseType

-- | Does this type support Inf/NaN?
hasInfNaN :: DType -> Boolean
hasInfNaN (FloatType IEEE_FP32) = true
hasInfNaN (FloatType IEEE_FP16) = true
hasInfNaN (FloatType BF16) = true
hasInfNaN (FloatType FP8_E4M3) = true  -- Has NaN only (no Inf)
hasInfNaN (FloatType FP8_E5M2) = true
hasInfNaN (FloatType FP4_E2M1) = false  -- NVFP4 is "FN" (Finite)
hasInfNaN (FloatType MXFP4_E2M1) = false
hasInfNaN (IntType _) = false
hasInfNaN (QuantizedType q) = hasInfNaN q.baseType

-- | Get exponent bits (0 for integers)
exponentBits :: DType -> Int
exponentBits (FloatType IEEE_FP32) = 8
exponentBits (FloatType IEEE_FP16) = 5
exponentBits (FloatType BF16) = 8
exponentBits (FloatType FP8_E4M3) = 4
exponentBits (FloatType FP8_E5M2) = 5
exponentBits (FloatType FP4_E2M1) = 2
exponentBits (FloatType MXFP4_E2M1) = 2
exponentBits (IntType _) = 0
exponentBits (QuantizedType q) = exponentBits q.baseType

-- | Get mantissa bits (0 for integers)
mantissaBits :: DType -> Int
mantissaBits (FloatType IEEE_FP32) = 23
mantissaBits (FloatType IEEE_FP16) = 10
mantissaBits (FloatType BF16) = 7
mantissaBits (FloatType FP8_E4M3) = 3
mantissaBits (FloatType FP8_E5M2) = 2
mantissaBits (FloatType FP4_E2M1) = 1
mantissaBits (FloatType MXFP4_E2M1) = 1
mantissaBits (IntType _) = 0
mantissaBits (QuantizedType q) = mantissaBits q.baseType

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // precision comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Does first type have higher precision than second?
higherPrecision :: DType -> DType -> Boolean
higherPrecision a b = bitWidth a > bitWidth b

-- | Does first type have lower precision than second?
lowerPrecision :: DType -> DType -> Boolean
lowerPrecision a b = bitWidth a < bitWidth b

-- | Can first type be safely cast to second without data loss?
canCastTo :: DType -> DType -> Boolean
canCastTo from to
  -- Same type: always safe
  | from == to = true
  -- Float to larger float: safe
  | isFloatingPoint from && isFloatingPoint to && bitWidth from <= bitWidth to = true
  -- Int to larger int: safe
  | isInteger from && isInteger to && bitWidth from <= bitWidth to = true
  -- Int to float (if float has enough precision): generally safe for small ints
  | isInteger from && isFloatingPoint to && bitWidth from <= 24 && bitWidth to >= 32 = true
  -- Everything else: potentially lossy
  | true = false

-- | Find common type that can represent both (for broadcasting)
commonType :: DType -> DType -> Maybe DType
commonType a b
  | a == b = Just a
  | isFloatingPoint a && isFloatingPoint b = 
      if bitWidth a >= bitWidth b then Just a else Just b
  | isInteger a && isInteger b =
      if bitWidth a >= bitWidth b then Just a else Just b
  | isFloatingPoint a && isInteger b = Just a
  | isInteger a && isFloatingPoint b = Just b
  | true = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // memory calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Number of elements that fit in one byte
-- |
-- | For sub-byte types (INT4, FP4), multiple elements pack into one byte.
elementsPerByte :: DType -> Int
elementsPerByte dtype =
  let bits = bitWidth dtype
  in if bits >= 8 then 1 else 8 / bits

-- | Bytes needed to store N elements
-- |
-- | Rounds up for sub-byte types.
bytesForElements :: DType -> Int -> Int
bytesForElements dtype count =
  let 
    bits = bitWidth dtype
    totalBits = bits * count
    -- Ceiling division: (a + b - 1) / b
  in (totalBits + 7) / 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // string representation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert dtype to string representation
dtypeToString :: DType -> String
dtypeToString (FloatType fmt) = show fmt
dtypeToString (IntType fmt) = show fmt
dtypeToString (QuantizedType q) = 
  "Quantized(" <> dtypeToString q.baseType <> ", " <> show q.quantFormat <> ")"

-- | Convert quantization mode to string
quantModeToString :: QuantMode -> String
quantModeToString NoQuant = "None"
quantModeToString W8A8_SQ = "W8A8_SQ"
quantModeToString W8A16 = "W8A16"
quantModeToString W4A16 = "W4A16"
quantModeToString W4A16_AWQ = "W4A16_AWQ"
quantModeToString W4A16_GPTQ = "W4A16_GPTQ"
quantModeToString FP8_Linear = "FP8_Linear"
quantModeToString FP8_Full = "FP8"
quantModeToString W4A8_NVFP4_FP8 = "W4A8_NVFP4_FP8"
quantModeToString W4A8_MXFP4_FP8 = "W4A8_MXFP4_FP8"
quantModeToString W8A8_FP8 = "W8A8_FP8"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bit width for float formats
floatBitWidth :: FloatFormat -> Int
floatBitWidth IEEE_FP32 = 32
floatBitWidth IEEE_FP16 = 16
floatBitWidth BF16 = 16
floatBitWidth FP8_E4M3 = 8
floatBitWidth FP8_E5M2 = 8
floatBitWidth FP4_E2M1 = 4
floatBitWidth MXFP4_E2M1 = 4

-- | Bit width for int formats
intBitWidth :: IntFormat -> Int
intBitWidth Int4Signed = 4
intBitWidth Int4Unsigned = 4
intBitWidth Int8Signed = 8
intBitWidth Int8Unsigned = 8
intBitWidth Int16Signed = 16
intBitWidth Int32Signed = 32
intBitWidth Int64Signed = 64
intBitWidth Bool = 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two dtypes are compatible for operations.
-- |
-- | Types are compatible if they can be operated together (possibly with casting).
isCompatiblePair :: DType -> DType -> Boolean
isCompatiblePair a b =
  a == b || canCastTo a b || canCastTo b a || 
  (isFloatingPoint a && isFloatingPoint b) ||
  (isInteger a && isInteger b)

-- | Check if dtype is NOT a boolean type.
-- |
-- | Used to validate numeric operations.
isNumeric :: DType -> Boolean
isNumeric dtype = dtype /= bool

-- | Promote dtype to at least the given bit width.
-- |
-- | Returns Nothing if promotion is not possible.
promoteTo :: Int -> DType -> Maybe DType
promoteTo targetBits dtype = do
  -- Early exit if already sufficient
  _ <- if bitWidth dtype < targetBits then Just true else Nothing
  -- Find appropriate promoted type
  case dtype of
    FloatType _ -> 
      if targetBits <= 16 then pure float16
      else pure float32
    IntType _ ->
      if targetBits <= 8 then pure int8
      else if targetBits <= 32 then pure int32
      else pure int64
    QuantizedType q -> do
      promoted <- promoteTo targetBits q.baseType
      pure $ QuantizedType { baseType: promoted, quantFormat: q.quantFormat }

-- | Map a function over the base type of a quantized dtype.
-- |
-- | For non-quantized types, applies function directly.
mapBaseType :: (DType -> DType) -> DType -> DType
mapBaseType f (QuantizedType q) = 
  QuantizedType { baseType: f q.baseType, quantFormat: q.quantFormat }
mapBaseType f dtype = f dtype

-- | Get a description of the dtype for diagnostics.
describeType :: DType -> String
describeType dtype = 
  let 
    bits = show $ bitWidth dtype
    kind = if isFloatingPoint dtype then "float" else "integer"
    signed = if isSigned dtype then "signed" else "unsigned"
  in bits <> "-bit " <> signed <> " " <> kind

-- | Get bit widths for an array of dtypes.
-- |
-- | Useful for computing total memory footprint.
bitWidths :: Array DType -> Array Int
bitWidths = map bitWidth

-- | Does this quantization mode require scaling factors?
-- |
-- | Most quantization modes require per-tensor or per-channel scales.
requiresScaling :: QuantMode -> Boolean
requiresScaling NoQuant = false
requiresScaling _ = true

-- | Get the weight dtype for a quantization mode
weightDType :: QuantMode -> DType
weightDType NoQuant = float16
weightDType W8A8_SQ = int8
weightDType W8A16 = int8
weightDType W4A16 = int4
weightDType W4A16_AWQ = int4
weightDType W4A16_GPTQ = int4
weightDType FP8_Linear = fp8e4m3
weightDType FP8_Full = fp8e4m3
weightDType W4A8_NVFP4_FP8 = nvfp4
weightDType W4A8_MXFP4_FP8 = mxfp4
weightDType W8A8_FP8 = fp8e4m3

-- | Get the activation dtype for a quantization mode
activationDType :: QuantMode -> DType
activationDType NoQuant = float16
activationDType W8A8_SQ = int8
activationDType W8A16 = float16
activationDType W4A16 = float16
activationDType W4A16_AWQ = float16
activationDType W4A16_GPTQ = float16
activationDType FP8_Linear = fp8e4m3
activationDType FP8_Full = fp8e4m3
activationDType W4A8_NVFP4_FP8 = fp8e4m3
activationDType W4A8_MXFP4_FP8 = fp8e4m3
activationDType W8A8_FP8 = fp8e4m3

-- | List all supported quantization modes for a target hardware.
-- |
-- | Blackwell supports all modes including NVFP4.
-- | Hopper supports FP8 but not NVFP4.
-- | Older hardware only supports INT8.
supportedQuantModes :: String -> Array QuantMode
supportedQuantModes hardware = case hardware of
  "blackwell" -> allModes
  "hopper" -> hopperModes
  "ampere" -> ampereModes
  _ -> baseModes
  where
    allModes :: Array QuantMode
    allModes = 
      [ NoQuant
      , W8A8_SQ
      , W8A16
      , W4A16
      , W4A16_AWQ
      , W4A16_GPTQ
      , FP8_Linear
      , FP8_Full
      , W4A8_NVFP4_FP8
      , W4A8_MXFP4_FP8
      , W8A8_FP8
      ]
    
    -- Hopper: no NVFP4/MXFP4
    hopperModes :: Array QuantMode
    hopperModes =
      [ NoQuant
      , W8A8_SQ
      , W8A16
      , W4A16
      , W4A16_AWQ
      , W4A16_GPTQ
      , FP8_Linear
      , FP8_Full
      , W8A8_FP8
      ]
    
    -- Ampere: no FP8, no NVFP4
    ampereModes :: Array QuantMode
    ampereModes =
      [ NoQuant
      , W8A8_SQ
      , W8A16
      , W4A16
      , W4A16_AWQ
      , W4A16_GPTQ
      ]
    
    -- Base modes for older hardware
    baseModes :: Array QuantMode
    baseModes = [NoQuant, W8A8_SQ, W8A16, W4A16]
