-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // lab
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | LAB - CIE L*a*b* perceptually uniform color space.
-- |
-- | **PERCEPTUAL UNIFORMITY:**
-- | Unlike HSL, LAB is designed so that equal distances in the color space
-- | correspond to equal perceptual differences. This means:
-- | - "10% lighter" actually LOOKS 10% lighter
-- | - Color math matches human vision
-- | - Gradients appear smooth and natural
-- |
-- | **Components:**
-- | - **L*** (Lightness): 0 (black) to 100 (white)
-- | - **a***: Green (negative) to Red (positive), typically -128 to +127
-- | - **b***: Blue (negative) to Yellow (positive), typically -128 to +127
-- |
-- | **Use cases:**
-- | - Accurate "lighter/darker" operations
-- | - Perceptually uniform gradients
-- | - Color difference calculations (ΔE)
-- | - Professional color grading
-- | - Autonomous palette generation
-- |
-- | **Conversion note:**
-- | LAB uses D65 white point (standard for sRGB displays).
-- | Conversion path: RGB → XYZ → LAB

module Hydrogen.Schema.Color.LAB
  ( -- * Types
    LAB
  , LabL
  , LabA
  , LabB
  
  -- * Constructors
  , lab
  , labFromRecord
  
  -- * Accessors
  , labL
  , labA
  , labB
  , labToRecord
  , toRecord
  
  -- * Operations (perceptually uniform)
  , increaseLuminance
  , decreaseLuminance
  , deltaE
  ) where

import Prelude (class Eq, class Ord, class Show, show, otherwise, negate, (<>), (<), (>), (+), (-), (*))

import Data.Number (sqrt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | L* component (Lightness): 0-100
newtype LabL = LabL Number

derive instance eqLabL :: Eq LabL
derive instance ordLabL :: Ord LabL

instance showLabL :: Show LabL where
  show (LabL n) = "LabL " <> show n

-- | Create L* value (clamped 0-100)
labLValue :: Number -> LabL
labLValue n
  | n < 0.0 = LabL 0.0
  | n > 100.0 = LabL 100.0
  | otherwise = LabL n

unwrapLabL :: LabL -> Number
unwrapLabL (LabL n) = n

-- | a* component (Green-Red axis): unbounded, typically -128 to +127
newtype LabA = LabA Number

derive instance eqLabA :: Eq LabA
derive instance ordLabA :: Ord LabA

instance showLabA :: Show LabA where
  show (LabA n) = "LabA " <> show n

-- | Create a* value (unbounded, but clamped for practical range)
labAValue :: Number -> LabA
labAValue n
  | n < (-128.0) = LabA (-128.0)
  | n > 127.0 = LabA 127.0
  | otherwise = LabA n

unwrapLabA :: LabA -> Number
unwrapLabA (LabA n) = n

-- | b* component (Blue-Yellow axis): unbounded, typically -128 to +127
newtype LabB = LabB Number

derive instance eqLabB :: Eq LabB
derive instance ordLabB :: Ord LabB

instance showLabB :: Show LabB where
  show (LabB n) = "LabB " <> show n

-- | Create b* value (unbounded, but clamped for practical range)
labBValue :: Number -> LabB
labBValue n
  | n < (-128.0) = LabB (-128.0)
  | n > 127.0 = LabB 127.0
  | otherwise = LabB n

unwrapLabB :: LabB -> Number
unwrapLabB (LabB n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | LAB color - perceptually uniform color space
type LAB =
  { l :: LabL  -- ^ Lightness (0-100)
  , a :: LabA  -- ^ Green-Red axis
  , b :: LabB  -- ^ Blue-Yellow axis
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create LAB color from components
-- |
-- | ```purescript
-- | lab 50.0 0.0 0.0      -- Mid gray
-- | lab 100.0 0.0 0.0     -- White
-- | lab 50.0 80.0 67.0    -- Red-ish
-- | ```
lab :: Number -> Number -> Number -> LAB
lab l a b =
  { l: labLValue l
  , a: labAValue a
  , b: labBValue b
  }

-- | Create from record
labFromRecord :: { l :: Number, a :: Number, b :: Number } -> LAB
labFromRecord { l, a, b: bVal } = lab l a bVal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get L* (lightness) component
labL :: LAB -> LabL
labL c = c.l

-- | Get a* (green-red) component
labA :: LAB -> LabA
labA c = c.a

-- | Get b* (blue-yellow) component  
labB :: LAB -> LabB
labB c = c.b

-- | Convert to record - explicitly named for backend persistence
labToRecord :: LAB -> { l :: Number, a :: Number, b :: Number }
labToRecord c =
  { l: unwrapLabL c.l
  , a: unwrapLabA c.a
  , b: unwrapLabB c.b
  }

-- | Generic alias for labToRecord
toRecord :: LAB -> { l :: Number, a :: Number, b :: Number }
toRecord = labToRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lighten by percentage (perceptually accurate)
-- |
-- ═════════════════════════════════════════════════════════════════════════════
--                                      // operations // perceptually // uniform
-- ═════════════════════════════════════════════════════════════════════════════

-- | Increase LAB L* (luminance) by percentage - PERCEPTUALLY UNIFORM.
-- |
-- | Unlike HSL.increaseLightness, this produces consistent perceived brightness changes.
-- | Adding 10 to L* actually looks 10% lighter to the human eye.
-- |
-- | **Semantically explicit:** `increaseLuminance` makes clear this operates on L* (luminance),
-- | not HSL lightness. Critical for billion-agent disambiguation.
-- |
-- | ```purescript
-- | increaseLuminance 10.0 color  -- Actually looks 10% lighter (perceptual)
-- | ```
increaseLuminance :: Number -> LAB -> LAB
increaseLuminance percent color =
  let l = unwrapLabL color.l
      l' = l + percent
  in color { l = labLValue l' }

-- | Decrease LAB L* (luminance) by percentage - PERCEPTUALLY UNIFORM.
-- |
-- | Unlike HSL.decreaseLightness, this produces consistent perceived brightness changes.
-- | Subtracting 10 from L* actually looks 10% darker to the human eye.
-- |
-- | ```purescript
-- | decreaseLuminance 10.0 color  -- Actually looks 10% darker (perceptual)
-- | ```
decreaseLuminance :: Number -> LAB -> LAB
decreaseLuminance percent color =
  let l = unwrapLabL color.l
      l' = l - percent
  in color { l = labLValue l' }



-- | Calculate color difference (ΔE - Delta E)
-- |
-- | Returns perceptual distance between two colors:
-- | - 0: Identical colors
-- | - < 1: Imperceptible difference
-- | - 1-2: Just noticeable difference
-- | - 2-10: Perceptible at a glance
-- | - 11-49: Colors are more similar than opposite
-- | - 100: Maximum difference (black to white)
-- |
-- | Uses CIE76 formula: ΔE = √[(L2-L1)² + (a2-a1)² + (b2-b1)²]
-- |
-- | ```purescript
-- | deltaE color1 color2  -- How different are these colors?
-- | ```
deltaE :: LAB -> LAB -> Number
deltaE c1 c2 =
  let l1 = unwrapLabL c1.l
      a1 = unwrapLabA c1.a
      b1 = unwrapLabB c1.b
      l2 = unwrapLabL c2.l
      a2 = unwrapLabA c2.a
      b2 = unwrapLabB c2.b
      
      dL = l2 - l1
      dA = a2 - a1
      dB = b2 - b1
  in
    sqrt (dL * dL + dA * dA + dB * dB)
