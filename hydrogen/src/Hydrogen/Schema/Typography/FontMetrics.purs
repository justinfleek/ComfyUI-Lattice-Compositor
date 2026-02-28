-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // typography // font-metrics
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FontMetrics - OpenType font metric values.
-- |
-- | Provides access to the vertical metrics embedded in font files.
-- | These values are essential for precise text layout, baseline alignment,
-- | and vertical rhythm calculations.
-- |
-- | ## Metrics Overview
-- | - **UnitsPerEm**: Design grid size (typically 1000 or 2048)
-- | - **Ascender**: Height above baseline (uppercase + accents)
-- | - **Descender**: Depth below baseline (descending letters)
-- | - **XHeight**: Height of lowercase letters without ascenders
-- | - **CapHeight**: Height of capital letters
-- | - **LineGap**: Recommended additional line spacing
-- |
-- | ## Usage
-- | Font metrics are extracted from font files (via fontkit, opentype.js, etc.)
-- | and used for layout calculations. All values are in font design units.
-- | To convert to pixels: `pixels = designUnits * fontSize / unitsPerEm`

module Hydrogen.Schema.Typography.FontMetrics
  ( -- * Types
    FontMetrics(..)
  , UnitsPerEm(..)
  , Ascender(..)
  , Descender(..)
  , XHeight(..)
  , CapHeight(..)
  , LineGap(..)
  
  -- * Constructors
  , fontMetrics
  , unitsPerEm
  , ascender
  , descender
  , xHeight
  , capHeight
  , lineGap
  
  -- * Accessors
  , getUnitsPerEm
  , getAscender
  , getDescender
  , getXHeight
  , getCapHeight
  , getLineGap
  
  -- * Calculations
  , toPixels
  , ascenderRatio
  , descenderRatio
  , xHeightRatio
  , capHeightRatio
  , totalHeight
  , contentHeight
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Data.Int (toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // atomic types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Units per em - design grid size
-- | Typically 1000 (PostScript) or 2048 (TrueType)
newtype UnitsPerEm = UnitsPerEm Int

derive instance eqUnitsPerEm :: Eq UnitsPerEm
derive instance ordUnitsPerEm :: Ord UnitsPerEm

instance showUnitsPerEm :: Show UnitsPerEm where
  show (UnitsPerEm n) = show n <> " UPM"

-- | Ascender - height above baseline (positive)
newtype Ascender = Ascender Int

derive instance eqAscender :: Eq Ascender
derive instance ordAscender :: Ord Ascender

instance showAscender :: Show Ascender where
  show (Ascender n) = "asc " <> show n

-- | Descender - depth below baseline (typically negative)
newtype Descender = Descender Int

derive instance eqDescender :: Eq Descender
derive instance ordDescender :: Ord Descender

instance showDescender :: Show Descender where
  show (Descender n) = "desc " <> show n

-- | X-height - height of lowercase letters
newtype XHeight = XHeight Int

derive instance eqXHeight :: Eq XHeight
derive instance ordXHeight :: Ord XHeight

instance showXHeight :: Show XHeight where
  show (XHeight n) = "x-height " <> show n

-- | Cap height - height of capital letters
newtype CapHeight = CapHeight Int

derive instance eqCapHeight :: Eq CapHeight
derive instance ordCapHeight :: Ord CapHeight

instance showCapHeight :: Show CapHeight where
  show (CapHeight n) = "cap " <> show n

-- | Line gap - additional recommended spacing
newtype LineGap = LineGap Int

derive instance eqLineGap :: Eq LineGap
derive instance ordLineGap :: Ord LineGap

instance showLineGap :: Show LineGap where
  show (LineGap n) = "gap " <> show n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // molecule type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete font metrics from an OpenType font
type FontMetrics =
  { unitsPerEm :: UnitsPerEm
  , ascender :: Ascender
  , descender :: Descender
  , xHeight :: XHeight
  , capHeight :: CapHeight
  , lineGap :: LineGap
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a FontMetrics record
fontMetrics 
  :: { unitsPerEm :: Int
     , ascender :: Int
     , descender :: Int
     , xHeight :: Int
     , capHeight :: Int
     , lineGap :: Int
     }
  -> FontMetrics
fontMetrics r =
  { unitsPerEm: UnitsPerEm r.unitsPerEm
  , ascender: Ascender r.ascender
  , descender: Descender r.descender
  , xHeight: XHeight r.xHeight
  , capHeight: CapHeight r.capHeight
  , lineGap: LineGap r.lineGap
  }

-- | Create UnitsPerEm
unitsPerEm :: Int -> UnitsPerEm
unitsPerEm = UnitsPerEm

-- | Create Ascender
ascender :: Int -> Ascender
ascender = Ascender

-- | Create Descender
descender :: Int -> Descender
descender = Descender

-- | Create XHeight
xHeight :: Int -> XHeight
xHeight = XHeight

-- | Create CapHeight
capHeight :: Int -> CapHeight
capHeight = CapHeight

-- | Create LineGap
lineGap :: Int -> LineGap
lineGap = LineGap

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract unitsPerEm value
getUnitsPerEm :: FontMetrics -> Int
getUnitsPerEm fm = case fm.unitsPerEm of UnitsPerEm n -> n

-- | Extract ascender value
getAscender :: FontMetrics -> Int
getAscender fm = case fm.ascender of Ascender n -> n

-- | Extract descender value
getDescender :: FontMetrics -> Int
getDescender fm = case fm.descender of Descender n -> n

-- | Extract xHeight value
getXHeight :: FontMetrics -> Int
getXHeight fm = case fm.xHeight of XHeight n -> n

-- | Extract capHeight value
getCapHeight :: FontMetrics -> Int
getCapHeight fm = case fm.capHeight of CapHeight n -> n

-- | Extract lineGap value
getLineGap :: FontMetrics -> Int
getLineGap fm = case fm.lineGap of LineGap n -> n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert design units to pixels at a given font size
toPixels :: FontMetrics -> Number -> Int -> Number
toPixels fm fontSize designUnits =
  Int.toNumber designUnits * fontSize / Int.toNumber (getUnitsPerEm fm)

-- | Ascender as ratio of em (0-1+)
ascenderRatio :: FontMetrics -> Number
ascenderRatio fm =
  Int.toNumber (getAscender fm) / Int.toNumber (getUnitsPerEm fm)

-- | Descender as ratio of em (typically negative)
descenderRatio :: FontMetrics -> Number
descenderRatio fm =
  Int.toNumber (getDescender fm) / Int.toNumber (getUnitsPerEm fm)

-- | X-height as ratio of em (typically 0.4-0.6)
xHeightRatio :: FontMetrics -> Number
xHeightRatio fm =
  Int.toNumber (getXHeight fm) / Int.toNumber (getUnitsPerEm fm)

-- | Cap height as ratio of em (typically 0.65-0.75)
capHeightRatio :: FontMetrics -> Number
capHeightRatio fm =
  Int.toNumber (getCapHeight fm) / Int.toNumber (getUnitsPerEm fm)

-- | Total height (ascender - descender + lineGap) in design units
totalHeight :: FontMetrics -> Int
totalHeight fm =
  getAscender fm - getDescender fm + getLineGap fm

-- | Content height (ascender - descender) in design units
-- | This is the height needed to render all glyphs without clipping
contentHeight :: FontMetrics -> Int
contentHeight fm =
  getAscender fm - getDescender fm
