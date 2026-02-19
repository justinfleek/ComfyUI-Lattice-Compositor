-- | Lattice.Primitives - Core primitive types with invariant proofs
-- |
-- | Single source of truth for all primitive types.
-- | Uses refined newtypes to encode invariants at the type level.
-- |
-- | This is Layer 0 - no imports from other Lattice modules.
-- | All other Lattice modules depend on this.

module Lattice.Primitives
  ( -- * String Primitives
    NonEmptyString(..)
  , mkNonEmptyString
  , unNonEmptyString
    -- * Integer Primitives
  , PositiveInt
  , mkPositiveInt
  , unPositiveInt
    -- * Float Primitives
  , FiniteFloat(..)
  , mkFiniteFloat
  , unFiniteFloat
  , PositiveFloat(..)
  , mkPositiveFloat
  , unPositiveFloat
  , NonNegativeFloat(..)
  , mkNonNegativeFloat
  , unNonNegativeFloat
  , Percentage(..)
  , mkPercentage
  , unPercentage
  , UnitFloat(..)
  , mkUnitFloat
  , unUnitFloat
    -- * Frame Number
  , FrameNumber(..)
    -- * Vector Primitives
  , Vec2
  , Vec3
  , Vec4
    -- * Matrix Primitives
  , Matrix3x3
  , Matrix4x4
    -- * Color Primitives
  , RGB
  , RGBA
  , HexColor(..)
  , mkHexColor
  , unHexColor
    -- * Constants
  , minFrameNumber
  , maxFrameNumber
  , fps24, fps25, fps30, fps60
  , res720pWidth, res720pHeight
  , res1080pWidth, res1080pHeight
  , res4kWidth, res4kHeight
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.String (length, null) as String
import Data.String.CodeUnits (charAt, toCharArray)
import Data.Array (all, elem)
import Data.Array as Array
import Global (isNaN, isFinite)

--------------------------------------------------------------------------------
-- String Primitives
--------------------------------------------------------------------------------

-- | Non-empty string (length > 0)
newtype NonEmptyString = NonEmptyString String

derive instance Eq NonEmptyString
derive instance Ord NonEmptyString

instance Show NonEmptyString where
  show (NonEmptyString s) = "(NonEmptyString " <> show s <> ")"

-- | Smart constructor for NonEmptyString
mkNonEmptyString :: String -> Maybe NonEmptyString
mkNonEmptyString s
  | String.null s = Nothing
  | otherwise     = Just (NonEmptyString s)

-- | Extract the underlying String
unNonEmptyString :: NonEmptyString -> String
unNonEmptyString (NonEmptyString s) = s

--------------------------------------------------------------------------------
-- Integer Primitives
--------------------------------------------------------------------------------

-- | Positive integer (value > 0)
newtype PositiveInt = PositiveInt Int

derive instance Eq PositiveInt
derive instance Ord PositiveInt

instance Show PositiveInt where
  show (PositiveInt n) = "(PositiveInt " <> show n <> ")"

-- | Smart constructor for PositiveInt
mkPositiveInt :: Int -> Maybe PositiveInt
mkPositiveInt n
  | n > 0     = Just (PositiveInt n)
  | otherwise = Nothing

-- | Extract the underlying Int
unPositiveInt :: PositiveInt -> Int
unPositiveInt (PositiveInt n) = n

--------------------------------------------------------------------------------
-- Float Primitives
--------------------------------------------------------------------------------

-- | Finite float (not NaN, not Infinity)
newtype FiniteFloat = FiniteFloat Number

derive instance Eq FiniteFloat
derive instance Ord FiniteFloat
derive newtype instance Semiring FiniteFloat
derive newtype instance Ring FiniteFloat
derive newtype instance CommutativeRing FiniteFloat
derive newtype instance EuclideanRing FiniteFloat
derive newtype instance DivisionRing FiniteFloat

instance Show FiniteFloat where
  show (FiniteFloat f) = "(FiniteFloat " <> show f <> ")"

-- | Smart constructor for FiniteFloat
mkFiniteFloat :: Number -> Maybe FiniteFloat
mkFiniteFloat f
  | isNaN f || not (isFinite f) = Nothing
  | otherwise                   = Just (FiniteFloat f)

-- | Extract the underlying Number
unFiniteFloat :: FiniteFloat -> Number
unFiniteFloat (FiniteFloat f) = f

-- | Positive float (value > 0 and finite)
newtype PositiveFloat = PositiveFloat Number

derive instance Eq PositiveFloat
derive instance Ord PositiveFloat
derive newtype instance Semiring PositiveFloat
derive newtype instance Ring PositiveFloat
derive newtype instance CommutativeRing PositiveFloat
derive newtype instance EuclideanRing PositiveFloat
derive newtype instance DivisionRing PositiveFloat

instance Show PositiveFloat where
  show (PositiveFloat f) = "(PositiveFloat " <> show f <> ")"

-- | Smart constructor for PositiveFloat
mkPositiveFloat :: Number -> Maybe PositiveFloat
mkPositiveFloat f
  | f > 0.0 && not (isNaN f) && isFinite f = Just (PositiveFloat f)
  | otherwise = Nothing

-- | Extract the underlying Number
unPositiveFloat :: PositiveFloat -> Number
unPositiveFloat (PositiveFloat f) = f

-- | Non-negative float (value >= 0 and finite)
newtype NonNegativeFloat = NonNegativeFloat Number

derive instance Eq NonNegativeFloat
derive instance Ord NonNegativeFloat
derive newtype instance Semiring NonNegativeFloat
derive newtype instance Ring NonNegativeFloat
derive newtype instance CommutativeRing NonNegativeFloat
derive newtype instance EuclideanRing NonNegativeFloat
derive newtype instance DivisionRing NonNegativeFloat

instance Show NonNegativeFloat where
  show (NonNegativeFloat f) = "(NonNegativeFloat " <> show f <> ")"

-- | Smart constructor for NonNegativeFloat
mkNonNegativeFloat :: Number -> Maybe NonNegativeFloat
mkNonNegativeFloat f
  | f >= 0.0 && not (isNaN f) && isFinite f = Just (NonNegativeFloat f)
  | otherwise = Nothing

-- | Extract the underlying Number
unNonNegativeFloat :: NonNegativeFloat -> Number
unNonNegativeFloat (NonNegativeFloat f) = f

-- | Percentage (0 <= value <= 100 and finite)
newtype Percentage = Percentage Number

derive instance Eq Percentage
derive instance Ord Percentage
derive newtype instance Semiring Percentage
derive newtype instance Ring Percentage
derive newtype instance CommutativeRing Percentage
derive newtype instance EuclideanRing Percentage
derive newtype instance DivisionRing Percentage

instance Show Percentage where
  show (Percentage p) = "(Percentage " <> show p <> ")"

-- | Smart constructor for Percentage
mkPercentage :: Number -> Maybe Percentage
mkPercentage f
  | f >= 0.0 && f <= 100.0 && not (isNaN f) && isFinite f = Just (Percentage f)
  | otherwise = Nothing

-- | Extract the underlying Number
unPercentage :: Percentage -> Number
unPercentage (Percentage f) = f

-- | Unit float / normalized value (0 <= value <= 1 and finite)
newtype UnitFloat = UnitFloat Number

derive instance Eq UnitFloat
derive instance Ord UnitFloat
derive newtype instance Semiring UnitFloat
derive newtype instance Ring UnitFloat
derive newtype instance CommutativeRing UnitFloat
derive newtype instance EuclideanRing UnitFloat
derive newtype instance DivisionRing UnitFloat

instance Show UnitFloat where
  show (UnitFloat f) = "(UnitFloat " <> show f <> ")"

-- | Smart constructor for UnitFloat
mkUnitFloat :: Number -> Maybe UnitFloat
mkUnitFloat f
  | f >= 0.0 && f <= 1.0 && not (isNaN f) && isFinite f = Just (UnitFloat f)
  | otherwise = Nothing

-- | Extract the underlying Number
unUnitFloat :: UnitFloat -> Number
unUnitFloat (UnitFloat f) = f

--------------------------------------------------------------------------------
-- Frame Number
--------------------------------------------------------------------------------

-- | Frame number (always >= 0)
newtype FrameNumber = FrameNumber Int

derive instance Eq FrameNumber
derive instance Ord FrameNumber

instance Show FrameNumber where
  show (FrameNumber n) = "(FrameNumber " <> show n <> ")"

--------------------------------------------------------------------------------
-- Vector Primitives
--------------------------------------------------------------------------------

-- | 2D vector with finite components
type Vec2 =
  { x :: FiniteFloat
  , y :: FiniteFloat
  }

-- | 3D vector with finite components
type Vec3 =
  { x :: FiniteFloat
  , y :: FiniteFloat
  , z :: FiniteFloat
  }

-- | 4D vector with finite components
type Vec4 =
  { x :: FiniteFloat
  , y :: FiniteFloat
  , z :: FiniteFloat
  , w :: FiniteFloat
  }

--------------------------------------------------------------------------------
-- Matrix Primitives
--------------------------------------------------------------------------------

-- | 3x3 matrix with finite entries (row-major)
type Matrix3x3 =
  { m00 :: Number, m01 :: Number, m02 :: Number
  , m10 :: Number, m11 :: Number, m12 :: Number
  , m20 :: Number, m21 :: Number, m22 :: Number
  }

-- | 4x4 matrix with finite entries (row-major)
type Matrix4x4 =
  { m00 :: Number, m01 :: Number, m02 :: Number, m03 :: Number
  , m10 :: Number, m11 :: Number, m12 :: Number, m13 :: Number
  , m20 :: Number, m21 :: Number, m22 :: Number, m23 :: Number
  , m30 :: Number, m31 :: Number, m32 :: Number, m33 :: Number
  }

--------------------------------------------------------------------------------
-- Color Primitives
--------------------------------------------------------------------------------

-- | RGB color with values in [0, 1]
type RGB =
  { r :: UnitFloat
  , g :: UnitFloat
  , b :: UnitFloat
  }

-- | RGBA color with values in [0, 1]
type RGBA =
  { r :: UnitFloat
  , g :: UnitFloat
  , b :: UnitFloat
  , a :: UnitFloat
  }

-- | Hex color string (e.g., "#ff0000" or "#ff0000ff")
newtype HexColor = HexColor String

derive instance Eq HexColor
derive instance Ord HexColor

instance Show HexColor where
  show (HexColor s) = "(HexColor " <> show s <> ")"

-- | Smart constructor for HexColor
mkHexColor :: String -> Maybe HexColor
mkHexColor s =
  let isValidHex str =
        let len = String.length str
            firstChar = charAt 0 str
            hexChars = ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
                        'a', 'b', 'c', 'd', 'e', 'f',
                        'A', 'B', 'C', 'D', 'E', 'F']
            rest = toCharArray str
            restWithoutFirst = case Array.uncons rest of
              Nothing -> []
              Just { head: _, tail: xs } -> xs
        in (len == 7 || len == 9) &&
           firstChar == Just '#' &&
           all (\c -> elem c hexChars) restWithoutFirst
  in if isValidHex s then Just (HexColor s)
     else Nothing

-- | Extract the underlying String
unHexColor :: HexColor -> String
unHexColor (HexColor s) = s

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Minimum frame number (always 0)
minFrameNumber :: FrameNumber
minFrameNumber = FrameNumber 0

-- | Maximum frame number (practical limit: 2^31 - 1)
maxFrameNumber :: FrameNumber
maxFrameNumber = FrameNumber 2147483647

-- | Standard FPS: 24
fps24 :: PositiveInt
fps24 = PositiveInt 24

-- | Standard FPS: 25
fps25 :: PositiveInt
fps25 = PositiveInt 25

-- | Standard FPS: 30
fps30 :: PositiveInt
fps30 = PositiveInt 30

-- | Standard FPS: 60
fps60 :: PositiveInt
fps60 = PositiveInt 60

-- | 720p width
res720pWidth :: PositiveInt
res720pWidth = PositiveInt 1280

-- | 720p height
res720pHeight :: PositiveInt
res720pHeight = PositiveInt 720

-- | 1080p width
res1080pWidth :: PositiveInt
res1080pWidth = PositiveInt 1920

-- | 1080p height
res1080pHeight :: PositiveInt
res1080pHeight = PositiveInt 1080

-- | 4K width
res4kWidth :: PositiveInt
res4kWidth = PositiveInt 3840

-- | 4K height
res4kHeight :: PositiveInt
res4kHeight = PositiveInt 2160
