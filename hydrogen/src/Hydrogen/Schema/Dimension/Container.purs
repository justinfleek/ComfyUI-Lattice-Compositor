-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // dimension // container
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Container-relative units - measurements for CSS container queries.
-- |
-- | These units are relative to a containment context's dimensions.
-- | They enable component-level responsive design independent of viewport.
-- |
-- | ## Usage
-- |
-- | These units require a container with `container-type` set:
-- | - inline-size: enables cqi, cqw, cqmin, cqmax
-- - size: enables all container units
-- |
-- | ## Dependencies
-- | - Prelude

module Hydrogen.Schema.Dimension.Container
  ( -- * Container Query Width
    Cqw(Cqw)
  , cqw
  , cqws
  , unwrapCqw
  
  -- * Container Query Height
  , Cqh(Cqh)
  , cqh
  , cqhs
  , unwrapCqh
  
  -- * Container Query Inline Size
  , Cqi(Cqi)
  , cqi
  , cqis
  , unwrapCqi
  
  -- * Container Query Block Size
  , Cqb(Cqb)
  , cqb
  , cqbs
  , unwrapCqb
  
  -- * Container Query Minimum
  , Cqmin(Cqmin)
  , cqmin
  , cqmins
  , unwrapCqmin
  
  -- * Container Query Maximum
  , Cqmax(Cqmax)
  , cqmax
  , cqmaxs
  , unwrapCqmax
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cqw // container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container query width - 1% of container width.
-- |
-- | Requires container-type: size or inline-size.
newtype Cqw = Cqw Number

derive instance eqCqw :: Eq Cqw
derive instance ordCqw :: Ord Cqw

instance showCqw :: Show Cqw where
  show (Cqw v) = show v <> "cqw"

-- | Create Cqw from Number
cqw :: Number -> Cqw
cqw = Cqw

-- | Create Cqw (plural alias)
cqws :: Number -> Cqw
cqws = cqw

-- | Unwrap Cqw to raw Number
unwrapCqw :: Cqw -> Number
unwrapCqw (Cqw v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cqh // container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container query height - 1% of container height.
-- |
-- | Requires container-type: size.
newtype Cqh = Cqh Number

derive instance eqCqh :: Eq Cqh
derive instance ordCqh :: Ord Cqh

instance showCqh :: Show Cqh where
  show (Cqh v) = show v <> "cqh"

-- | Create Cqh from Number
cqh :: Number -> Cqh
cqh = Cqh

-- | Create Cqh (plural alias)
cqhs :: Number -> Cqh
cqhs = cqh

-- | Unwrap Cqh to raw Number
unwrapCqh :: Cqh -> Number
unwrapCqh (Cqh v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cqi // container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container query inline size - 1% of container's inline size.
-- |
-- | Inline size is width in horizontal writing mode.
-- | Requires container-type: inline-size or size.
newtype Cqi = Cqi Number

derive instance eqCqi :: Eq Cqi
derive instance ordCqi :: Ord Cqi

instance showCqi :: Show Cqi where
  show (Cqi v) = show v <> "cqi"

-- | Create Cqi from Number
cqi :: Number -> Cqi
cqi = Cqi

-- | Create Cqi (plural alias)
cqis :: Number -> Cqi
cqis = cqi

-- | Unwrap Cqi to raw Number
unwrapCqi :: Cqi -> Number
unwrapCqi (Cqi v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // cqb // container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container query block size - 1% of container's block size.
-- |
-- | Block size is height in horizontal writing mode.
-- | Requires container-type: size.
newtype Cqb = Cqb Number

derive instance eqCqb :: Eq Cqb
derive instance ordCqb :: Ord Cqb

instance showCqb :: Show Cqb where
  show (Cqb v) = show v <> "cqb"

-- | Create Cqb from Number
cqb :: Number -> Cqb
cqb = Cqb

-- | Create Cqb (plural alias)
cqbs :: Number -> Cqb
cqbs = cqb

-- | Unwrap Cqb to raw Number
unwrapCqb :: Cqb -> Number
unwrapCqb (Cqb v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // cqmin // container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container query minimum - smaller of cqi or cqb.
-- |
-- | 1cqmin = 1% of the smaller of container's inline or block size.
newtype Cqmin = Cqmin Number

derive instance eqCqmin :: Eq Cqmin
derive instance ordCqmin :: Ord Cqmin

instance showCqmin :: Show Cqmin where
  show (Cqmin v) = show v <> "cqmin"

-- | Create Cqmin from Number
cqmin :: Number -> Cqmin
cqmin = Cqmin

-- | Create Cqmin (plural alias)
cqmins :: Number -> Cqmin
cqmins = cqmin

-- | Unwrap Cqmin to raw Number
unwrapCqmin :: Cqmin -> Number
unwrapCqmin (Cqmin v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // cqmax // container
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container query maximum - larger of cqi or cqb.
-- |
-- | 1cqmax = 1% of the larger of container's inline or block size.
newtype Cqmax = Cqmax Number

derive instance eqCqmax :: Eq Cqmax
derive instance ordCqmax :: Ord Cqmax

instance showCqmax :: Show Cqmax where
  show (Cqmax v) = show v <> "cqmax"

-- | Create Cqmax from Number
cqmax :: Number -> Cqmax
cqmax = Cqmax

-- | Create Cqmax (plural alias)
cqmaxs :: Number -> Cqmax
cqmaxs = cqmax

-- | Unwrap Cqmax to raw Number
unwrapCqmax :: Cqmax -> Number
unwrapCqmax (Cqmax v) = v
