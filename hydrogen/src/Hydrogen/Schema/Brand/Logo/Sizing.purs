-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // brand // logo // sizing
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Minimum Sizing (§12): Print and digital size constraints.
-- |
-- | From SMART Brand Ingestion Framework §12:
-- |   - PrintSize: Minimum dimension in inches (0.1-24.0)
-- |   - DigitalSize: Minimum dimension in pixels (1-10000)

module Hydrogen.Schema.Brand.Logo.Sizing
  ( -- * Print Size
    PrintSize
  , mkPrintSize
  , unPrintSize
  
    -- * Digital Size
  , DigitalSize
  , mkDigitalSize
  , unDigitalSize
  
    -- * Size Constraint
  , SizeConstraint
  , mkSizeConstraint
  , printMinimum
  , digitalMinimum
  , showSizeConstraint
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // print size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Print size atom.
-- |
-- | Minimum print dimension in inches.
-- | Bounded: 0.1 to 24.0 inches (reasonable print range).
newtype PrintSize = PrintSize Number

derive instance eqPrintSize :: Eq PrintSize
derive instance ordPrintSize :: Ord PrintSize

instance showPrintSize :: Show PrintSize where
  show (PrintSize s) = "PrintSize(" <> show s <> "in)"

-- | Smart constructor for print size.
mkPrintSize :: Number -> Maybe PrintSize
mkPrintSize n =
  if n >= 0.1 && n <= 24.0
  then Just (PrintSize n)
  else Nothing

-- | Unwrap print size.
unPrintSize :: PrintSize -> Number
unPrintSize (PrintSize s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // digital size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Digital size atom.
-- |
-- | Minimum digital dimension in pixels.
-- | Bounded: 1 to 10000 pixels (reasonable digital range).
newtype DigitalSize = DigitalSize Int

derive instance eqDigitalSize :: Eq DigitalSize
derive instance ordDigitalSize :: Ord DigitalSize

instance showDigitalSize :: Show DigitalSize where
  show (DigitalSize s) = "DigitalSize(" <> show s <> "px)"

-- | Smart constructor for digital size.
mkDigitalSize :: Int -> Maybe DigitalSize
mkDigitalSize n =
  if n >= 1 && n <= 10000
  then Just (DigitalSize n)
  else Nothing

-- | Unwrap digital size.
unDigitalSize :: DigitalSize -> Int
unDigitalSize (DigitalSize s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // size constraint
-- ═════════════════════════════════════════════════════════════════════════════

-- | Size constraint molecule.
-- |
-- | Print and digital minimum dimensions for a lockup.
type SizeConstraint =
  { printMin :: PrintSize
  , digitalMin :: DigitalSize
  }

-- | Create a size constraint.
mkSizeConstraint :: PrintSize -> DigitalSize -> SizeConstraint
mkSizeConstraint p d =
  { printMin: p
  , digitalMin: d
  }

-- | Get print minimum.
printMinimum :: SizeConstraint -> PrintSize
printMinimum sc = sc.printMin

-- | Get digital minimum.
digitalMinimum :: SizeConstraint -> DigitalSize
digitalMinimum sc = sc.digitalMin

-- | Show size constraint (debug format).
showSizeConstraint :: SizeConstraint -> String
showSizeConstraint sc =
  "SizeConstraint { print: " <> 
  show (unPrintSize sc.printMin) <> "in, digital: " <> 
  show (unDigitalSize sc.digitalMin) <> "px }"
