-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // brand // logo // orientation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Logo Orientation: Spatial arrangement of logo elements.
-- |
-- | Horizontal: Icon beside wordmark
-- | Vertical: Icon above wordmark
-- | Square: Compact, equal dimensions

module Hydrogen.Schema.Brand.Logo.Orientation
  ( -- * Orientation
    Orientation(..)
  , allOrientations
  , orientationToString
  , orientationFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , compare
  , show
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String as String

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Orientation atom.
-- |
-- | The spatial arrangement of logo elements.
data Orientation
  = Horizontal  -- Icon beside wordmark
  | Vertical    -- Icon above wordmark
  | Square      -- Compact, equal dimensions

derive instance eqOrientation :: Eq Orientation

instance ordOrientation :: Ord Orientation where
  compare o1 o2 = compare (orientationToInt o1) (orientationToInt o2)
    where
      orientationToInt :: Orientation -> Int
      orientationToInt Horizontal = 0
      orientationToInt Vertical = 1
      orientationToInt Square = 2

instance showOrientation :: Show Orientation where
  show = orientationToString

-- | All orientations for enumeration.
allOrientations :: Array Orientation
allOrientations = [Horizontal, Vertical, Square]

-- | Convert orientation to string.
orientationToString :: Orientation -> String
orientationToString Horizontal = "horizontal"
orientationToString Vertical = "vertical"
orientationToString Square = "square"

-- | Parse orientation from string.
orientationFromString :: String -> Maybe Orientation
orientationFromString s = case String.toLower s of
  "horizontal" -> Just Horizontal
  "vertical" -> Just Vertical
  "square" -> Just Square
  _ -> Nothing
