-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // typography // grade
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Grade - variable font weight adjustment without changing metrics.
-- |
-- | Unlike FontWeight, Grade adjusts the apparent weight (stroke thickness)
-- | without affecting the font's advance widths or bounding boxes. This allows
-- | weight adjustments that don't cause text reflow.
-- |
-- | ## Use Cases
-- | - Dark mode: Reduce grade to compensate for halation (text appearing bolder)
-- | - Hover states: Increase grade without layout shift
-- | - Print vs screen: Adjust for ink spread vs light emission
-- | - Accessibility: Boost contrast without changing metrics
-- |
-- | ## CSS Mapping
-- | Maps to the 'GRAD' variation axis in OpenType variable fonts.
-- |
-- | ## Range
-- | Typically -200 to +200, where 0 is the default design.
-- | Negative values are lighter, positive values are bolder.

module Hydrogen.Schema.Typography.Grade
  ( -- * Type
    Grade(..)
    
  -- * Constructors
  , grade
  
  -- * Predefined Values
  , normal
  , light
  , lighter
  , bold
  , bolder
  , darkMode
  , lightMode
  
  -- * Accessors
  , unwrap
  , toLegacyCSSValue
  , toVariationValue
  
  -- * Operations
  , clamp
  , invert
  , scale
  , add
  
  -- * Bounds
  , bounds
  ) where

import Prelude

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grade represents weight adjustment without metric changes.
-- | Bounded to [-200, 200] per typical variable font implementations.
newtype Grade = Grade Int

derive instance eqGrade :: Eq Grade
derive instance ordGrade :: Ord Grade

instance showGrade :: Show Grade where
  show (Grade n) = "grade " <> show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constructor
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Grade value (clamped to -200 to 200)
grade :: Int -> Grade
grade n
  | n < (-200) = Grade (-200)
  | n > 200 = Grade 200
  | otherwise = Grade n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predefined
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normal grade (0) - default design
normal :: Grade
normal = Grade 0

-- | Light grade (-50) - subtle reduction
light :: Grade
light = Grade (-50)

-- | Lighter grade (-100) - significant reduction
lighter :: Grade
lighter = Grade (-100)

-- | Bold grade (50) - subtle increase
bold :: Grade
bold = Grade 50

-- | Bolder grade (100) - significant increase
bolder :: Grade
bolder = Grade 100

-- | Dark mode grade (-25) - compensate for halation
-- | On dark backgrounds, light text appears bolder due to light bloom.
-- | This preset compensates for that optical effect.
darkMode :: Grade
darkMode = Grade (-25)

-- | Light mode grade (0) - no compensation needed
lightMode :: Grade
lightMode = Grade 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw integer value
unwrap :: Grade -> Int
unwrap (Grade n) = n

-- NOT an FFI boundary - pure string generation.
-- | Convert to CSS value (for font-variation-settings)
toLegacyCSSValue :: Grade -> String
toLegacyCSSValue (Grade n) = show n

-- | Convert to variation axis value string
toVariationValue :: Grade -> String
toVariationValue (Grade n) = "\"GRAD\" " <> show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp grade to valid range (identity, as constructor already clamps)
clamp :: Grade -> Grade
clamp = identity

-- | Invert grade (positive becomes negative, vice versa)
invert :: Grade -> Grade
invert (Grade n) = Grade (negate n)

-- | Scale grade by a factor
scale :: Number -> Grade -> Grade
scale factor (Grade n) = grade (Int.round (Int.toNumber n * factor))

-- | Add two grades together
add :: Grade -> Grade -> Grade
add (Grade a) (Grade b) = grade (a + b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds documentation for Grade
-- |
-- | Min: -200 (lightest)
-- | Max: 200 (boldest)
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds (-200) 200 "grade" "Variable font grade axis (-200 to 200)"
