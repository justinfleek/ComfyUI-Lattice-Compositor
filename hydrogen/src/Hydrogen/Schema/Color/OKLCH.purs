-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // color // oklch
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | OKLCH - Cylindrical version of OKLAB (hue-based).
-- |
-- | **BEST FOR UI DESIGN:**
-- | OKLCH is OKLAB in cylindrical coordinates, making it perfect for:
-- | - Color pickers (hue wheel + chroma/lightness)
-- | - Generating color palettes (rotate hue, adjust chroma)
-- | - CSS (modern browsers support oklch() function)
-- |
-- | **Components:**
-- | - **L**: Lightness, 0.0 (black) to 1.0 (white)
-- | - **C**: Chroma (colorfulness), 0.0 (gray) to ~0.4 (vivid)
-- | - **H**: Hue, 0-360 degrees (color wheel position)
-- |
-- | **Why use OKLCH over HSL?**
-- | - Perceptually uniform (HSL isn't)
-- | - Same lightness = same perceived brightness
-- | - Better for accessibility (contrast calculations)
-- | - Modern CSS standard

module Hydrogen.Schema.Color.OKLCH
  ( -- * Types
    OKLCH
  , OkChroma
  
  -- * Constructors
  , oklch
  , oklchFromRecord
  , okChroma
  
  -- * Accessors
  , oklchL
  , chroma
  , hue
  , unwrapChroma
  , oklchToRecord
  , toRecord
  
  -- * Operations
  , rotateHue
  , increaseChroma
  , decreaseChroma
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Color.Hue (Hue)
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.OKLAB (OkL, okLValue, unwrapOkL)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // atom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chroma component (colorfulness): 0.0-0.4 typical range
newtype OkChroma = OkChroma Number

derive instance eqOkChroma :: Eq OkChroma
derive instance ordOkChroma :: Ord OkChroma

instance showOkChroma :: Show OkChroma where
  show (OkChroma n) = "OkChroma " <> show n

-- | Create chroma value (clamped 0.0-0.4)
okChroma :: Number -> OkChroma
okChroma n = OkChroma (Bounded.clampNumber 0.0 0.4 n)

unwrapChroma :: OkChroma -> Number
unwrapChroma (OkChroma n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | OKLCH color - cylindrical OKLAB
newtype OKLCH = OKLCH
  { l :: OkL
  , c :: OkChroma
  , h :: Hue
  }

derive instance eqOKLCH :: Eq OKLCH
derive instance ordOKLCH :: Ord OKLCH

instance showOKLCH :: Show OKLCH where
  show (OKLCH col) = "oklch(" <> show (unwrapOkL col.l) <> ", " <> show (unwrapChroma col.c) <> ", " <> show (Hue.unwrap col.h) <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create OKLCH color
oklch :: Number -> Number -> Int -> OKLCH
oklch l c h = OKLCH
  { l: okLValue l
  , c: okChroma c
  , h: Hue.hue h
  }

-- | Create from record
oklchFromRecord :: { l :: Number, c :: Number, h :: Int } -> OKLCH
oklchFromRecord { l, c, h } = oklch l c h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract lightness
oklchL :: OKLCH -> OkL
oklchL (OKLCH c) = c.l

-- | Extract chroma
chroma :: OKLCH -> OkChroma
chroma (OKLCH c) = c.c

-- | Extract hue
hue :: OKLCH -> Hue
hue (OKLCH c) = c.h

-- | Convert to record
oklchToRecord :: OKLCH -> { l :: Number, c :: Number, h :: Int }
oklchToRecord (OKLCH c) =
  { l: unwrapOkL c.l
  , c: unwrapChroma c.c
  , h: Hue.unwrap c.h
  }

-- | Alias for oklchToRecord
toRecord :: OKLCH -> { l :: Number, c :: Number, h :: Int }
toRecord = oklchToRecord

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rotate hue by degrees
rotateHue :: Int -> OKLCH -> OKLCH
rotateHue degrees (OKLCH c) = OKLCH c { h = Hue.rotate degrees c.h }

-- | Increase chroma (more vivid)
increaseChroma :: Number -> OKLCH -> OKLCH
increaseChroma amount (OKLCH c) = OKLCH c { c = okChroma (unwrapChroma c.c + amount) }

-- | Decrease chroma (more muted)
decreaseChroma :: Number -> OKLCH -> OKLCH
decreaseChroma amount (OKLCH c) = OKLCH c { c = okChroma (unwrapChroma c.c - amount) }
