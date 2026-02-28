-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // material // borderall
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BorderAll - four-sided border compound.
-- |
-- | Composes four BorderSide molecules into a complete border specification.
-- | Provides convenience constructors for common patterns (uniform, symmetric).
-- |
-- | ## Composition
-- |
-- | - BorderSide (top, right, bottom, left)
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Material.BorderSide
-- | - Hydrogen.Schema.Material.BorderWidth
-- | - Hydrogen.Schema.Color.RGB

module Hydrogen.Schema.Material.BorderAll
  ( -- * Types
    BorderAll(BorderAll)
  
  -- * Constructors
  , borderAll
  , borderAllUniform
  , borderAllSymmetric
  , borderAllNone
  
  -- * Accessors
  , top
  , right
  , bottom
  , left
  
  -- * Predicates
  , isUniform
  , hasVisibleBorder
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (&&)
  , (||)
  , (==)
  , (<>)
  )

import Hydrogen.Schema.Material.BorderSide (BorderSide)
import Hydrogen.Schema.Material.BorderSide (borderSideNone, isVisible) as BS

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // borderall
-- ═════════════════════════════════════════════════════════════════════════════

-- | BorderAll - four-sided border compound.
-- |
-- | Describes borders for all four edges of a rectangular element.
newtype BorderAll = BorderAll
  { top :: BorderSide
  , right :: BorderSide
  , bottom :: BorderSide
  , left :: BorderSide
  }

derive instance eqBorderAll :: Eq BorderAll

instance showBorderAll :: Show BorderAll where
  show (BorderAll b) = 
    "(BorderAll top:" <> show b.top 
      <> " right:" <> show b.right 
      <> " bottom:" <> show b.bottom 
      <> " left:" <> show b.left
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create BorderAll with explicit sides
borderAll 
  :: { top :: BorderSide
     , right :: BorderSide
     , bottom :: BorderSide
     , left :: BorderSide
     }
  -> BorderAll
borderAll cfg = BorderAll
  { top: cfg.top
  , right: cfg.right
  , bottom: cfg.bottom
  , left: cfg.left
  }

-- | Create BorderAll with same border on all sides
borderAllUniform :: BorderSide -> BorderAll
borderAllUniform side = BorderAll
  { top: side
  , right: side
  , bottom: side
  , left: side
  }

-- | Create BorderAll with horizontal/vertical symmetry
-- |
-- | First argument is top/bottom, second is left/right.
borderAllSymmetric :: BorderSide -> BorderSide -> BorderAll
borderAllSymmetric vertical horizontal = BorderAll
  { top: vertical
  , right: horizontal
  , bottom: vertical
  , left: horizontal
  }

-- | Create BorderAll with no borders
borderAllNone :: BorderAll
borderAllNone = BorderAll
  { top: BS.borderSideNone
  , right: BS.borderSideNone
  , bottom: BS.borderSideNone
  , left: BS.borderSideNone
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get top border
top :: BorderAll -> BorderSide
top (BorderAll b) = b.top

-- | Get right border
right :: BorderAll -> BorderSide
right (BorderAll b) = b.right

-- | Get bottom border
bottom :: BorderAll -> BorderSide
bottom (BorderAll b) = b.bottom

-- | Get left border
left :: BorderAll -> BorderSide
left (BorderAll b) = b.left

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if all four borders are identical
isUniform :: BorderAll -> Boolean
isUniform (BorderAll b) = 
  b.top == b.right && b.right == b.bottom && b.bottom == b.left

-- | Check if any border is visible
hasVisibleBorder :: BorderAll -> Boolean
hasVisibleBorder (BorderAll b) = 
  BS.isVisible b.top || BS.isVisible b.right || BS.isVisible b.bottom || BS.isVisible b.left
