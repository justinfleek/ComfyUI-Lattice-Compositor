-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // color // oklab
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OKLAB - Modern perceptually uniform color space.
-- |
-- | **BETTER THAN LAB:**
-- | OKLAB (2020, Björn Ottosson) improves on CIE LAB with:
-- | - More uniform hue perception
-- | - Better behavior for blue colors
-- | - Simpler math (no cube roots)
-- | - Faster computation
-- | - Better for gradient interpolation
-- |
-- | **Components:**
-- | - **L**: Lightness, 0.0 (black) to 1.0 (white)
-- | - **a**: Green-Red axis, typically -0.4 to +0.4
-- | - **b**: Blue-Yellow axis, typically -0.4 to +0.4
-- |
-- | **Use cases:**
-- | - Smooth color gradients (better than HSL or LAB)
-- | - Perceptually uniform color palettes
-- | - Color difference calculations
-- | - Modern CSS (oklch() function support)
-- |
-- | **Reference:**
-- | https://bottosson.github.io/posts/oklab/

module Hydrogen.Schema.Color.OKLAB
  ( -- * Types
    OKLAB
  , OkL
  , OkA
  , OkB
  
  -- * Constructors
  , oklab
  , oklabFromRecord
  , okLValue
  , okAValue
  , okBValue
  
  -- * Accessors
  , okL
  , okA
  , okB
  , unwrapOkL
  , unwrapOkA
  , unwrapOkB
  , oklabToRecord
  , toRecord
  
  -- * Operations (perceptually uniform)
  , increaseLightness
  , decreaseLightness
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , negate
  , show
  , (+)
  , (-)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // atoms
-- ═════════════════════════════════════════════════════════════════════════════

-- | L component (Lightness): 0.0-1.0
newtype OkL = OkL Number

derive instance eqOkL :: Eq OkL
derive instance ordOkL :: Ord OkL

instance showOkL :: Show OkL where
  show (OkL n) = "OkL " <> show n

-- | Create L value (clamped 0.0-1.0)
okLValue :: Number -> OkL
okLValue n = OkL (Bounded.clampNumber 0.0 1.0 n)

unwrapOkL :: OkL -> Number
unwrapOkL (OkL n) = n

-- | a component (Green-Red axis): typically -0.4 to +0.4
newtype OkA = OkA Number

derive instance eqOkA :: Eq OkA
derive instance ordOkA :: Ord OkA

instance showOkA :: Show OkA where
  show (OkA n) = "OkA " <> show n

-- | Create a value (clamped for practical range)
okAValue :: Number -> OkA
okAValue n = OkA (Bounded.clampNumber (-0.4) 0.4 n)

unwrapOkA :: OkA -> Number
unwrapOkA (OkA n) = n

-- | b component (Blue-Yellow axis): typically -0.4 to +0.4
newtype OkB = OkB Number

derive instance eqOkB :: Eq OkB
derive instance ordOkB :: Ord OkB

instance showOkB :: Show OkB where
  show (OkB n) = "OkB " <> show n

-- | Create b value (clamped for practical range)
okBValue :: Number -> OkB
okBValue n = OkB (Bounded.clampNumber (-0.4) 0.4 n)

unwrapOkB :: OkB -> Number
unwrapOkB (OkB n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | OKLAB color - composition of OkL, OkA, OkB atoms
newtype OKLAB = OKLAB
  { l :: OkL
  , a :: OkA
  , b :: OkB
  }

derive instance eqOKLAB :: Eq OKLAB
derive instance ordOKLAB :: Ord OKLAB

instance showOKLAB :: Show OKLAB where
  show (OKLAB c) = "oklab(" <> show (unwrapOkL c.l) <> ", " <> show (unwrapOkA c.a) <> ", " <> show (unwrapOkB c.b) <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create OKLAB color from raw values
oklab :: Number -> Number -> Number -> OKLAB
oklab l a b = OKLAB
  { l: okLValue l
  , a: okAValue a
  , b: okBValue b
  }

-- | Create from record
oklabFromRecord :: { l :: Number, a :: Number, b :: Number } -> OKLAB
oklabFromRecord { l, a, b } = oklab l a b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract L component
okL :: OKLAB -> OkL
okL (OKLAB c) = c.l

-- | Extract a component
okA :: OKLAB -> OkA
okA (OKLAB c) = c.a

-- | Extract b component
okB :: OKLAB -> OkB
okB (OKLAB c) = c.b

-- | Convert to record
oklabToRecord :: OKLAB -> { l :: Number, a :: Number, b :: Number }
oklabToRecord (OKLAB c) =
  { l: unwrapOkL c.l
  , a: unwrapOkA c.a
  , b: unwrapOkB c.b
  }

-- | Alias for oklabToRecord
toRecord :: OKLAB -> { l :: Number, a :: Number, b :: Number }
toRecord = oklabToRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Increase lightness (perceptually uniform)
increaseLightness :: Number -> OKLAB -> OKLAB
increaseLightness amount (OKLAB c) = OKLAB c { l = okLValue (unwrapOkL c.l + amount) }

-- | Decrease lightness (perceptually uniform)
decreaseLightness :: Number -> OKLAB -> OKLAB
decreaseLightness amount (OKLAB c) = OKLAB c { l = okLValue (unwrapOkL c.l - amount) }
