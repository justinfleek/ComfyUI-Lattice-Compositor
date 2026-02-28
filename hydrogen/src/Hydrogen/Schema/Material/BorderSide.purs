-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // material // border-side
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BorderSide - single edge border configuration.
-- |
-- | A molecule combining border width, style, and color for one edge.
-- | The fundamental unit of border composition.
-- |
-- | ## Composition
-- |
-- | - BorderWidth: thickness in pixels (0.0 to finite)
-- | - BorderStyle: solid, dashed, dotted, etc.
-- | - Color: any color space (RGB used for interchange)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Solid black border
-- | topBorder = borderSide
-- |   { width: BorderWidth.thin
-- |   , style: Solid
-- |   , color: rgb 0 0 0
-- |   }
-- |
-- | -- Dashed accent border
-- | accentBorder = borderSideDashed (borderWidth 2.0) accentColor
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Material.BorderWidth
-- | - Hydrogen.Schema.Color.RGB

module Hydrogen.Schema.Material.BorderSide
  ( -- * Border Style
    BorderStyle(..)
  
  -- * Types
  , BorderSide(BorderSide)
  , BorderSideConfig
  
  -- * Constructors
  , borderSide
  , borderSideSolid
  , borderSideDashed
  , borderSideDotted
  , borderSideNone
  
  -- * Accessors
  , width
  , style
  , color
  
  -- * Predicates
  , isVisible
  , isNone
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (>)
  , (&&)
  , (||)
  , (/=)
  , not
  , (<>)
  )

import Hydrogen.Schema.Material.BorderWidth (BorderWidth)
import Hydrogen.Schema.Material.BorderWidth (borderWidth, none, hairline, toNumber) as BW
import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.RGB (rgb) as RGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // border style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border line style.
-- |
-- | Determines how the border line is rendered.
data BorderStyle
  = None       -- ^ No border (invisible)
  | Hidden     -- ^ Like none, but affects table border resolution
  | Solid      -- ^ Continuous solid line
  | Dashed     -- ^ Series of dashes
  | Dotted     -- ^ Series of dots
  | Double     -- ^ Two parallel solid lines
  | Groove     -- ^ 3D grooved effect (carved into page)
  | Ridge      -- ^ 3D ridged effect (raised from page)
  | Inset      -- ^ 3D inset effect (sunken into page)
  | Outset     -- ^ 3D outset effect (raised from page)

derive instance eqBorderStyle :: Eq BorderStyle
derive instance ordBorderStyle :: Ord BorderStyle

instance showBorderStyle :: Show BorderStyle where
  show None = "none"
  show Hidden = "hidden"
  show Solid = "solid"
  show Dashed = "dashed"
  show Dotted = "dotted"
  show Double = "double"
  show Groove = "groove"
  show Ridge = "ridge"
  show Inset = "inset"
  show Outset = "outset"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // border-side
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration record for creating BorderSide
type BorderSideConfig =
  { width :: BorderWidth
  , style :: BorderStyle
  , color :: RGB
  }

-- | BorderSide - single edge border molecule.
-- |
-- | Describes the border for one edge (top, right, bottom, or left).
-- | Composed from width, style, and color atoms.
newtype BorderSide = BorderSide
  { width :: BorderWidth     -- ^ Border thickness
  , style :: BorderStyle     -- ^ Line style
  , color :: RGB             -- ^ Border color
  }

derive instance eqBorderSide :: Eq BorderSide

instance showBorderSide :: Show BorderSide where
  show (BorderSide b) = 
    "(BorderSide " <> show b.width 
      <> " " <> show b.style 
      <> " " <> show b.color
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create BorderSide from configuration
borderSide :: BorderSideConfig -> BorderSide
borderSide cfg = BorderSide
  { width: cfg.width
  , style: cfg.style
  , color: cfg.color
  }

-- | Create solid BorderSide
borderSideSolid :: BorderWidth -> RGB -> BorderSide
borderSideSolid w c = BorderSide
  { width: w
  , style: Solid
  , color: c
  }

-- | Create dashed BorderSide
borderSideDashed :: BorderWidth -> RGB -> BorderSide
borderSideDashed w c = BorderSide
  { width: w
  , style: Dashed
  , color: c
  }

-- | Create dotted BorderSide
borderSideDotted :: BorderWidth -> RGB -> BorderSide
borderSideDotted w c = BorderSide
  { width: w
  , style: Dotted
  , color: c
  }

-- | Create invisible border (none)
-- |
-- | Uses black as placeholder color (irrelevant when width is 0).
borderSideNone :: BorderSide
borderSideNone = BorderSide
  { width: BW.none
  , style: None
  , color: RGB.rgb 0 0 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the border width
width :: BorderSide -> BorderWidth
width (BorderSide b) = b.width

-- | Get the border style
style :: BorderSide -> BorderStyle
style (BorderSide b) = b.style

-- | Get the border color
color :: BorderSide -> RGB
color (BorderSide b) = b.color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if border is visible
-- |
-- | A border is visible if width > 0 AND style is not None/Hidden.
isVisible :: BorderSide -> Boolean
isVisible (BorderSide b) = 
  BW.toNumber b.width > 0.0 && b.style /= None && b.style /= Hidden

-- | Check if border is invisible
isNone :: BorderSide -> Boolean
isNone b = not (isVisible b)
