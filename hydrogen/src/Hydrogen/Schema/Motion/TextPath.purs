-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // motion // text-path
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text on Path — Type text along arbitrary bezier paths.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors AE's "Path Options" for text layers:
-- |
-- | - **Path**: Reference to a mask or shape path
-- | - **Reverse Path**: Flow text in opposite direction
-- | - **Perpendicular To Path**: Characters rotate to follow path tangent
-- | - **Force Alignment**: Justify text to path length
-- | - **First Margin**: Offset from path start
-- | - **Last Margin**: Offset from path end
-- |
-- | ## Architecture
-- |
-- | TextPathOptions composes with TextAnimator. A text layer can have:
-- | - Text content (sourceText)
-- | - Path options (this module)
-- | - Animators (TextAnimator module)
-- |
-- | All properties are animatable.

module Hydrogen.Schema.Motion.TextPath
  ( -- * Path Reference
    TextPathSource(..)
  , textPathSourceToString
  , textPathSourceFromString
  
  -- * Path Options
  , TextPathOptions
  , defaultTextPathOptions
  , textPathOptions
  
  -- * Path Alignment
  , PathAlignment(..)
  , pathAlignmentToString
  , pathAlignmentFromString
  
  -- * Baseline Shift Mode
  , BaselineShiftMode(..)
  , baselineShiftModeToString
  , baselineShiftModeFromString
  
  -- * Path Margin
  , PathMargin
  , pathMargin
  , unwrapPathMargin
  
  -- * Operations
  , setFirstMargin
  , setLastMargin
  , setReversePath
  , setPerpendicularToPath
  , setForceAlignment
  
  -- * Queries
  , hasPathOptions
  , isPathReversed
  , isPerpendicularToPath
  , isForceAligned
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , ($)
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , compare
  , min
  , max
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , show
  , map
  , pure
  )

import Data.Maybe (Maybe(Just, Nothing), isJust)
import Data.Ord (abs)
import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // path // reference
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source of the path for text to follow.
-- |
-- | Text can follow:
-- | - A mask on the text layer itself
-- | - A path from a shape layer
-- | - A custom bezier path
data TextPathSource
  = TPSNone              -- ^ No path (standard text layout)
  | TPSMask Int          -- ^ Mask on layer by index (1-based)
  | TPSMaskNamed String  -- ^ Mask on layer by name
  | TPSShapeLayer String -- ^ Path from another shape layer (by name)
  | TPSCustomPath        -- ^ Custom inline path definition

derive instance eqTextPathSource :: Eq TextPathSource
derive instance ordTextPathSource :: Ord TextPathSource

instance showTextPathSource :: Show TextPathSource where
  show TPSNone = "none"
  show (TPSMask i) = "mask:" <> show i
  show (TPSMaskNamed n) = "mask:" <> n
  show (TPSShapeLayer n) = "shape:" <> n
  show TPSCustomPath = "custom"

-- | Convert to string representation.
textPathSourceToString :: TextPathSource -> String
textPathSourceToString TPSNone = "none"
textPathSourceToString (TPSMask i) = "mask-index:" <> show i
textPathSourceToString (TPSMaskNamed n) = "mask-name:" <> n
textPathSourceToString (TPSShapeLayer n) = "shape-layer:" <> n
textPathSourceToString TPSCustomPath = "custom-path"

-- | Parse from string (basic cases only).
textPathSourceFromString :: String -> Maybe TextPathSource
textPathSourceFromString "none" = Just TPSNone
textPathSourceFromString "custom-path" = Just TPSCustomPath
textPathSourceFromString _ = Nothing  -- Complex cases need structured parsing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // path // alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | How text aligns to the path.
data PathAlignment
  = PALeft       -- ^ Text starts at path beginning
  | PACenter     -- ^ Text centers on path
  | PARight      -- ^ Text ends at path end
  | PAJustify    -- ^ Text stretches to fill path

derive instance eqPathAlignment :: Eq PathAlignment
derive instance ordPathAlignment :: Ord PathAlignment

instance showPathAlignment :: Show PathAlignment where
  show PALeft = "PALeft"
  show PACenter = "PACenter"
  show PARight = "PARight"
  show PAJustify = "PAJustify"

pathAlignmentToString :: PathAlignment -> String
pathAlignmentToString PALeft = "left"
pathAlignmentToString PACenter = "center"
pathAlignmentToString PARight = "right"
pathAlignmentToString PAJustify = "justify"

pathAlignmentFromString :: String -> Maybe PathAlignment
pathAlignmentFromString "left" = Just PALeft
pathAlignmentFromString "center" = Just PACenter
pathAlignmentFromString "right" = Just PARight
pathAlignmentFromString "justify" = Just PAJustify
pathAlignmentFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // baseline // shift // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How baseline shift is calculated relative to path.
data BaselineShiftMode
  = BSMNone        -- ^ No baseline adjustment
  | BSMAutomatic   -- ^ Automatic baseline based on font metrics
  | BSMManual      -- ^ Manual baseline offset value

derive instance eqBaselineShiftMode :: Eq BaselineShiftMode
derive instance ordBaselineShiftMode :: Ord BaselineShiftMode

instance showBaselineShiftMode :: Show BaselineShiftMode where
  show BSMNone = "BSMNone"
  show BSMAutomatic = "BSMAutomatic"
  show BSMManual = "BSMManual"

baselineShiftModeToString :: BaselineShiftMode -> String
baselineShiftModeToString BSMNone = "none"
baselineShiftModeToString BSMAutomatic = "automatic"
baselineShiftModeToString BSMManual = "manual"

baselineShiftModeFromString :: String -> Maybe BaselineShiftMode
baselineShiftModeFromString "none" = Just BSMNone
baselineShiftModeFromString "automatic" = Just BSMAutomatic
baselineShiftModeFromString "manual" = Just BSMManual
baselineShiftModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // path // margin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Margin offset along path (percentage of path length).
-- |
-- | - 0% = at path start/end
-- | - 50% = halfway along path
-- | - Can be negative to extend before path start
newtype PathMargin = PathMargin Number

derive instance eqPathMargin :: Eq PathMargin
derive instance ordPathMargin :: Ord PathMargin

instance showPathMargin :: Show PathMargin where
  show (PathMargin m) = show m <> "%"

-- | Create path margin (clamped to -100% to 100%).
pathMargin :: Number -> PathMargin
pathMargin n = PathMargin (clampNumber (-100.0) 100.0 n)

-- | Extract margin value.
unwrapPathMargin :: PathMargin -> Number
unwrapPathMargin (PathMargin m) = m

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // path // options
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text path options — controls how text flows along a path.
-- |
-- | All properties are animatable.
type TextPathOptions =
  { source :: TextPathSource           -- ^ Path to follow
  , reversePath :: Boolean             -- ^ Flow text in reverse direction
  , perpendicularToPath :: Boolean     -- ^ Characters rotate to path tangent
  , forceAlignment :: Boolean          -- ^ Justify to path length
  , firstMargin :: PathMargin          -- ^ Offset from path start
  , lastMargin :: PathMargin           -- ^ Offset from path end
  , alignment :: PathAlignment         -- ^ Text alignment on path
  , baselineShiftMode :: BaselineShiftMode -- ^ Baseline shift calculation
  , baselineShift :: Number            -- ^ Manual baseline offset (pixels)
  }

-- | Default text path options (no path, standard layout).
defaultTextPathOptions :: TextPathOptions
defaultTextPathOptions =
  { source: TPSNone
  , reversePath: not true
  , perpendicularToPath: true
  , forceAlignment: not true
  , firstMargin: pathMargin 0.0
  , lastMargin: pathMargin 0.0
  , alignment: PALeft
  , baselineShiftMode: BSMAutomatic
  , baselineShift: 0.0
  }

-- | Create text path options with a path source.
textPathOptions :: TextPathSource -> TextPathOptions
textPathOptions src =
  { source: src
  , reversePath: not true
  , perpendicularToPath: true
  , forceAlignment: not true
  , firstMargin: pathMargin 0.0
  , lastMargin: pathMargin 0.0
  , alignment: PALeft
  , baselineShiftMode: BSMAutomatic
  , baselineShift: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set first margin.
setFirstMargin :: Number -> TextPathOptions -> TextPathOptions
setFirstMargin m opts = opts { firstMargin = pathMargin m }

-- | Set last margin.
setLastMargin :: Number -> TextPathOptions -> TextPathOptions
setLastMargin m opts = opts { lastMargin = pathMargin m }

-- | Set reverse path flag.
setReversePath :: Boolean -> TextPathOptions -> TextPathOptions
setReversePath r opts = opts { reversePath = r }

-- | Set perpendicular to path flag.
setPerpendicularToPath :: Boolean -> TextPathOptions -> TextPathOptions
setPerpendicularToPath p opts = opts { perpendicularToPath = p }

-- | Set force alignment flag.
setForceAlignment :: Boolean -> TextPathOptions -> TextPathOptions
setForceAlignment f opts = opts { forceAlignment = f }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if path options are active (source is not None).
hasPathOptions :: TextPathOptions -> Boolean
hasPathOptions opts = case opts.source of
  TPSNone -> not true
  _ -> true

-- | Check if path direction is reversed.
isPathReversed :: TextPathOptions -> Boolean
isPathReversed opts = opts.reversePath

-- | Check if characters are perpendicular to path.
isPerpendicularToPath :: TextPathOptions -> Boolean
isPerpendicularToPath opts = opts.perpendicularToPath

-- | Check if text is force-aligned to path length.
isForceAligned :: TextPathOptions -> Boolean
isForceAligned opts = opts.forceAlignment
