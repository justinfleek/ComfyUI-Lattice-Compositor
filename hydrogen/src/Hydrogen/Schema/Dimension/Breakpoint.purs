-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // dimension // breakpoint
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Breakpoint — Named viewport width thresholds for responsive design.
-- |
-- | **WHY BREAKPOINT?**
-- | Breakpoints define viewport width ranges where layouts change.
-- | They enable responsive design with semantic naming.
-- |
-- | **Standard breakpoints:**
-- | - xs: Extra small (phones, portrait)
-- | - sm: Small (phones, landscape)
-- | - md: Medium (tablets)
-- | - lg: Large (desktops)
-- | - xl: Extra large (large desktops)
-- | - xxl: 2X large (wide screens)
-- |
-- | **Use cases:**
-- | - CSS media queries
-- | - Conditional rendering
-- | - Layout system configuration
-- | - Container queries

module Hydrogen.Schema.Dimension.Breakpoint
  ( -- * Types
    Breakpoint(Breakpoint)
  , BreakpointName(..)
  , BreakpointSet
  
  -- * Constructors
  , breakpoint
  , breakpointFromRecord
  
  -- * Standard Breakpoint Sets
  , tailwindBreakpoints
  , bootstrapBreakpoints
  , materialBreakpoints
  
  -- * Accessors
  , name
  , minWidth
  , maxWidth
  , toRecord
  
  -- * Operations
  , matchesWidth
  , currentBreakpoint
  , isAbove
  , isBelow
  , isAtOrAbove
  , isAtOrBelow
  
  -- * CSS Output
  , toMediaQuery
  , toContainerQuery
  
  -- * Predicates
  , isMobile
  , isTablet
  , isDesktop
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, EQ, GT)
  , show
  , otherwise
  , (&&)
  , (||)
  , (+)
  , (-)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.Array (head, filter, reverse, sortBy)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // break-point
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic breakpoint names.
data BreakpointName
  = XS   -- ^ Extra small (< 576px typically)
  | SM   -- ^ Small (≥ 576px typically)
  | MD   -- ^ Medium (≥ 768px typically)
  | LG   -- ^ Large (≥ 992px typically)
  | XL   -- ^ Extra large (≥ 1200px typically)
  | XXL  -- ^ 2X Extra large (≥ 1400px typically)
  | Custom String  -- ^ Custom named breakpoint

derive instance eqBreakpointName :: Eq BreakpointName
derive instance ordBreakpointName :: Ord BreakpointName

instance showBreakpointName :: Show BreakpointName where
  show XS = "xs"
  show SM = "sm"
  show MD = "md"
  show LG = "lg"
  show XL = "xl"
  show XXL = "xxl"
  show (Custom s) = s

-- | A breakpoint with name and width threshold.
-- |
-- | minWidth is the starting width for this breakpoint.
-- | maxWidth is calculated as (next breakpoint minWidth - 1).
data Breakpoint = Breakpoint
  { name :: BreakpointName
  , minWidth :: Number
  , maxWidth :: Maybe Number  -- Nothing means no upper bound
  }

derive instance eqBreakpoint :: Eq Breakpoint

instance showBreakpoint :: Show Breakpoint where
  show (Breakpoint bp) = 
    "Breakpoint(" <> show bp.name <> ": " <> show bp.minWidth <> "px+)"

-- | A set of breakpoints for a design system.
type BreakpointSet = Array Breakpoint

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a breakpoint.
breakpoint :: BreakpointName -> Number -> Maybe Number -> Breakpoint
breakpoint n minW maxW = Breakpoint { name: n, minWidth: minW, maxWidth: maxW }

-- | Create from a record.
breakpointFromRecord :: { name :: BreakpointName, minWidth :: Number, maxWidth :: Maybe Number } -> Breakpoint
breakpointFromRecord = Breakpoint

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // standard breakpoints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tailwind CSS breakpoints.
-- |
-- | sm: 640px, md: 768px, lg: 1024px, xl: 1280px, 2xl: 1536px
tailwindBreakpoints :: BreakpointSet
tailwindBreakpoints =
  [ Breakpoint { name: XS, minWidth: 0.0, maxWidth: Just 639.0 }
  , Breakpoint { name: SM, minWidth: 640.0, maxWidth: Just 767.0 }
  , Breakpoint { name: MD, minWidth: 768.0, maxWidth: Just 1023.0 }
  , Breakpoint { name: LG, minWidth: 1024.0, maxWidth: Just 1279.0 }
  , Breakpoint { name: XL, minWidth: 1280.0, maxWidth: Just 1535.0 }
  , Breakpoint { name: XXL, minWidth: 1536.0, maxWidth: Nothing }
  ]

-- | Bootstrap 5 breakpoints.
-- |
-- | sm: 576px, md: 768px, lg: 992px, xl: 1200px, xxl: 1400px
bootstrapBreakpoints :: BreakpointSet
bootstrapBreakpoints =
  [ Breakpoint { name: XS, minWidth: 0.0, maxWidth: Just 575.0 }
  , Breakpoint { name: SM, minWidth: 576.0, maxWidth: Just 767.0 }
  , Breakpoint { name: MD, minWidth: 768.0, maxWidth: Just 991.0 }
  , Breakpoint { name: LG, minWidth: 992.0, maxWidth: Just 1199.0 }
  , Breakpoint { name: XL, minWidth: 1200.0, maxWidth: Just 1399.0 }
  , Breakpoint { name: XXL, minWidth: 1400.0, maxWidth: Nothing }
  ]

-- | Material Design breakpoints.
-- |
-- | Compact: 0-599, Medium: 600-839, Expanded: 840+
materialBreakpoints :: BreakpointSet
materialBreakpoints =
  [ Breakpoint { name: XS, minWidth: 0.0, maxWidth: Just 599.0 }
  , Breakpoint { name: MD, minWidth: 600.0, maxWidth: Just 839.0 }
  , Breakpoint { name: LG, minWidth: 840.0, maxWidth: Nothing }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get breakpoint name.
name :: Breakpoint -> BreakpointName
name (Breakpoint bp) = bp.name

-- | Get minimum width threshold.
minWidth :: Breakpoint -> Number
minWidth (Breakpoint bp) = bp.minWidth

-- | Get maximum width threshold (if any).
maxWidth :: Breakpoint -> Maybe Number
maxWidth (Breakpoint bp) = bp.maxWidth

-- | Convert to record.
toRecord :: Breakpoint -> { name :: BreakpointName, minWidth :: Number, maxWidth :: Maybe Number }
toRecord (Breakpoint bp) = bp

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if viewport width falls within this breakpoint.
matchesWidth :: Number -> Breakpoint -> Boolean
matchesWidth w (Breakpoint bp) =
  w >= bp.minWidth && case bp.maxWidth of
    Nothing -> true
    Just maxW -> w <= maxW

-- | Find the current breakpoint for a viewport width.
currentBreakpoint :: Number -> BreakpointSet -> Maybe Breakpoint
currentBreakpoint w bps =
  let sorted = sortBy (\(Breakpoint a) (Breakpoint b) -> compareNum b.minWidth a.minWidth) bps
      matches = filter (\bp -> minWidth bp <= w) sorted
  in head matches

-- | Check if width is above this breakpoint.
isAbove :: Number -> Breakpoint -> Boolean
isAbove w (Breakpoint bp) = w > bp.minWidth

-- | Check if width is below this breakpoint.
isBelow :: Number -> Breakpoint -> Boolean
isBelow w (Breakpoint bp) = w < bp.minWidth

-- | Check if width is at or above this breakpoint.
isAtOrAbove :: Number -> Breakpoint -> Boolean
isAtOrAbove w (Breakpoint bp) = w >= bp.minWidth

-- | Check if width is at or below this breakpoint (within its range).
isAtOrBelow :: Number -> Breakpoint -> Boolean
isAtOrBelow w (Breakpoint bp) = case bp.maxWidth of
  Nothing -> true
  Just maxW -> w <= maxW

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate CSS media query for this breakpoint.
-- |
-- | ```purescript
-- | toMediaQuery (breakpoint SM 576.0 (Just 767.0))
-- | -- "@media (min-width: 576px) and (max-width: 767px)"
-- | ```
toMediaQuery :: Breakpoint -> String
toMediaQuery (Breakpoint bp) =
  let minPart = "@media (min-width: " <> show bp.minWidth <> "px)"
  in case bp.maxWidth of
    Nothing -> minPart
    Just maxW -> minPart <> " and (max-width: " <> show maxW <> "px)"

-- | Generate CSS container query for this breakpoint.
toContainerQuery :: Breakpoint -> String
toContainerQuery (Breakpoint bp) =
  let minPart = "@container (min-width: " <> show bp.minWidth <> "px)"
  in case bp.maxWidth of
    Nothing -> minPart
    Just maxW -> minPart <> " and (max-width: " <> show maxW <> "px)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if breakpoint is in mobile range (xs or sm).
isMobile :: Breakpoint -> Boolean
isMobile (Breakpoint bp) = bp.name == XS || bp.name == SM

-- | Check if breakpoint is in tablet range (md).
isTablet :: Breakpoint -> Boolean
isTablet (Breakpoint bp) = bp.name == MD

-- | Check if breakpoint is in desktop range (lg or larger).
isDesktop :: Breakpoint -> Boolean
isDesktop (Breakpoint bp) = 
  bp.name == LG || bp.name == XL || bp.name == XXL

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare two numbers for sorting
compareNum :: Number -> Number -> Ordering
compareNum a b
  | a < b = LT
  | a > b = GT
  | otherwise = EQ
