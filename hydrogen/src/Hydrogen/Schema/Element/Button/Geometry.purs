-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // element // button // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ButtonGeometry — spatial atoms for button layout and shape.
-- |
-- | ## Atoms Included
-- |
-- | - Size (width, height, min/max constraints)
-- | - Padding (internal spacing)
-- | - Margin (external spacing)
-- | - Corner radii (per-corner radius)
-- | - Aspect ratio constraints

module Hydrogen.Schema.Element.Button.Geometry
  ( -- * Button Geometry Record
    ButtonGeometry
  , defaultGeometry
  , mkGeometry
    -- * Accessors
  , geoWidth
  , geoHeight
  , geoPadding
  , geoCornerRadii
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.CornerRadii
  ( CornerRadii
  , uniform
  ) as Corner

import Hydrogen.Schema.Geometry.Spacing
  ( Padding
  , padding
  , spacingValue
  ) as Spacing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // button geometry
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Geometry atoms for button layout.
-- |
-- | All spatial properties a button needs for layout calculation.
type ButtonGeometry =
  { -- Dimensions
    width :: Maybe Number           -- ^ Explicit width (Nothing = auto)
  , height :: Maybe Number          -- ^ Explicit height (Nothing = auto)
  , minWidth :: Maybe Number        -- ^ Minimum width constraint
  , maxWidth :: Maybe Number        -- ^ Maximum width constraint
  , minHeight :: Maybe Number       -- ^ Minimum height constraint
  , maxHeight :: Maybe Number       -- ^ Maximum height constraint
    -- Spacing
  , paddingTop :: Number            -- ^ Top padding
  , paddingRight :: Number          -- ^ Right padding
  , paddingBottom :: Number         -- ^ Bottom padding
  , paddingLeft :: Number           -- ^ Left padding
  , gap :: Number                   -- ^ Gap between icon and label
    -- Shape
  , cornerRadii :: Corner.CornerRadii  -- ^ Per-corner radius
  }

-- | Default button geometry.
-- |
-- | Auto-sized with 12px horizontal, 8px vertical padding, 8px corners.
defaultGeometry :: ButtonGeometry
defaultGeometry =
  { width: Nothing
  , height: Nothing
  , minWidth: Nothing
  , maxWidth: Nothing
  , minHeight: Just 36.0
  , maxHeight: Nothing
  , paddingTop: 8.0
  , paddingRight: 12.0
  , paddingBottom: 8.0
  , paddingLeft: 12.0
  , gap: 8.0
  , cornerRadii: Corner.uniform 8.0
  }

-- | Create custom geometry.
mkGeometry
  :: Maybe Number          -- ^ Width
  -> Maybe Number          -- ^ Height
  -> Number                -- ^ Padding X
  -> Number                -- ^ Padding Y
  -> Number                -- ^ Corner radius (uniform)
  -> ButtonGeometry
mkGeometry w h px py r =
  { width: w
  , height: h
  , minWidth: Nothing
  , maxWidth: Nothing
  , minHeight: Just 36.0
  , maxHeight: Nothing
  , paddingTop: py
  , paddingRight: px
  , paddingBottom: py
  , paddingLeft: px
  , gap: 8.0
  , cornerRadii: Corner.uniform r
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get width.
geoWidth :: ButtonGeometry -> Maybe Number
geoWidth g = g.width

-- | Get height.
geoHeight :: ButtonGeometry -> Maybe Number
geoHeight g = g.height

-- | Get padding as Spacing.Padding.
geoPadding :: ButtonGeometry -> Spacing.Padding
geoPadding g = Spacing.padding
  (Spacing.spacingValue g.paddingTop)
  (Spacing.spacingValue g.paddingRight)
  (Spacing.spacingValue g.paddingBottom)
  (Spacing.spacingValue g.paddingLeft)

-- | Get corner radii.
geoCornerRadii :: ButtonGeometry -> Corner.CornerRadii
geoCornerRadii g = g.cornerRadii
