-- |
-- Module      : Lattice.Schema.Primitives
-- Description : Primitive type definitions and validation constants
--
-- Migrated from ui/src/schemas/layers/primitives-schema.ts
-- Defines foundational types: numbers, vectors, colors, geometry, IDs, enums

-- ============================================================================
-- Numeric Validation Rules
-- ============================================================================

-- | Finite number validation (rejects NaN/Infinity)
-- In Haskell: validateFinite :: Double -> Bool
let FiniteNumber = Double

-- | Positive finite number validation
-- In Haskell: validatePositive :: Double -> Bool
let PositiveFinite = Double

-- | Non-negative finite number validation
-- In Haskell: validateNonNegative :: Double -> Bool
let NonNegativeFinite = Double

-- | Normalized value [0, 1] validation
-- In Haskell: validateNormalized01 :: Double -> Bool
let Normalized01 = Double

-- | Normalized value [-1, 1] validation
-- In Haskell: validateNormalizedNeg1To1 :: Double -> Bool
let NormalizedNeg1To1 = Double

-- | Positive integer validation
-- In Haskell: validatePositiveInt :: Int -> Bool
let PositiveInt = Natural

-- | Non-negative integer validation
-- In Haskell: validateNonNegativeInt :: Int -> Bool
let NonNegativeInt = Natural

-- | Frame number validation (non-negative integer)
-- In Haskell: validateFrameNumber :: Int -> Bool
let FrameNumber = Natural

-- ============================================================================
-- Vector Types
-- ============================================================================

let Vec2 = { x : FiniteNumber, y : FiniteNumber }

let Vec3 = { x : FiniteNumber, y : FiniteNumber, z : FiniteNumber }

let Position2DOr3D = { x : FiniteNumber, y : FiniteNumber, z : Optional FiniteNumber }

-- ============================================================================
-- Color Types
-- ============================================================================

let RGBAColor = { r : Normalized01, g : Normalized01, b : Normalized01, a : Normalized01 }

let RGBA255Color = { r : Natural, g : Natural, b : Natural, a : Natural }

-- | Hex color string (with or without #)
-- Format: #?[0-9a-fA-F]{3,8}
let HexColor = Text

-- | Color value (hex string or RGBA object)
let ColorValue = < Hex : HexColor | RGBA : RGBAColor >

-- ============================================================================
-- Geometry Types
-- ============================================================================

let Rect = { x : FiniteNumber, y : FiniteNumber, width : NonNegativeFinite, height : NonNegativeFinite }

-- ============================================================================
-- ID Types
-- ============================================================================

-- | Entity ID (non-empty string)
let EntityId = Text

-- | Nullable entity ID
let NullableEntityId = Optional EntityId

-- ============================================================================
-- Enum Types
-- ============================================================================

let BlendMode =
      < Normal
      | Multiply
      | Screen
      | Overlay
      | Darken
      | Lighten
      | ColorDodge
      | ColorBurn
      | HardLight
      | SoftLight
      | Difference
      | Exclusion
      | Hue
      | Saturation
      | Color
      | Luminosity
      | Add
      | Subtract
      | Divide
      | ClassicColorDodge
      | ClassicColorBurn
      | StencilAlpha
      | StencilLuma
      | SilhouetteAlpha
      | SilhouetteLuma
      | Behind
      | AlphaAdd
      | Dissolve
      >

let QualityMode = < Draft | Best >

-- ============================================================================
-- Export
-- ============================================================================

in  { FiniteNumber
    , PositiveFinite
    , NonNegativeFinite
    , Normalized01
    , NormalizedNeg1To1
    , PositiveInt
    , NonNegativeInt
    , FrameNumber
    , Vec2
    , Vec3
    , Position2DOr3D
    , RGBAColor
    , RGBA255Color
    , HexColor
    , ColorValue
    , Rect
    , EntityId
    , NullableEntityId
    , BlendMode
    , QualityMode
    }
