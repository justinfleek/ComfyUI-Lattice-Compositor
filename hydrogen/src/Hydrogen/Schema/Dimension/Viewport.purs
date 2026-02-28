-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // dimension // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Viewport-relative units - measurements relative to the browser viewport.
-- |
-- | These units are percentage-based but have specific semantics:
-- | - vw/vh: 1% of viewport width/height
-- | - vmin/vmax: The smaller/larger of vw or vh
-- | - dvw/dvh: Dynamic viewport (accounts for mobile UI chrome)
-- | - svw/svh: Small viewport (like vw/vh but for @media)
-- | - lvw/lvh: Large viewport
-- |
-- | ## Type Safety
-- |
-- | Each unit is a distinct newtype. These are purely responsive units
-- | and cannot be mixed with absolute pixels without conversion.
-- |
-- | ## Dependencies
-- | - Prelude
-- |
-- | ## Dependents
-- | - Layout.Responsive (breakpoints)
-- | - Component.Fullscreen (sizing)

module Hydrogen.Schema.Dimension.Viewport
  ( -- * Viewport Width
    Vw(Vw)
  , vw
  , vws
  , unwrapVw
  
  -- * Viewport Height
  , Vh(Vh)
  , vh
  , vhs
  , unwrapVh
  
  -- * Viewport Minimum
  , Vmin(Vmin)
  , vmin
  , vmins
  , unwrapVmin
  
  -- * Viewport Maximum
  , Vmax(Vmax)
  , vmax
  , vmaxs
  , unwrapVmax
  
  -- * Dynamic Viewport Width
  , Dvw(Dvw)
  , dvw
  , dvws
  , unwrapDvw
  
  -- * Dynamic Viewport Height
  , Dvh(Dvh)
  , dvh
  , dvhs
  , unwrapDvh
  
  -- * Small Viewport Width
  , Svw(Svw)
  , svw
  , svws
  , unwrapSvw
  
  -- * Small Viewport Height
  , Svh(Svh)
  , svh
  , svhs
  , unwrapSvh
  
  -- * Large Viewport Width
  , Lvw(Lvw)
  , lvw
  , lvws
  , unwrapLvw
  
  -- * Large Viewport Height
  , Lvh(Lvh)
  , lvh
  , lvhs
  , unwrapLvh
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // vw // viewport
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport width unit - 1% of viewport width.
-- |
-- | 100vw = full viewport width. Useful for full-width elements.
newtype Vw = Vw Number

derive instance eqVw :: Eq Vw
derive instance ordVw :: Ord Vw

instance showVw :: Show Vw where
  show (Vw v) = show v <> "vw"

-- | Create Vw from Number
vw :: Number -> Vw
vw = Vw

-- | Create Vw (plural alias)
vws :: Number -> Vw
vws = vw

-- | Unwrap Vw to raw Number
unwrapVw :: Vw -> Number
unwrapVw (Vw v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // vh // viewport
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport height unit - 1% of viewport height.
-- |
-- | 100vh = full viewport height. Useful for hero sections.
newtype Vh = Vh Number

derive instance eqVh :: Eq Vh
derive instance ordVh :: Ord Vh

instance showVh :: Show Vh where
  show (Vh v) = show v <> "vh"

-- | Create Vh from Number
vh :: Number -> Vh
vh = Vh

-- | Create Vh (plural alias)
vhs :: Number -> Vh
vhs = vh

-- | Unwrap Vh to raw Number
unwrapVh :: Vh -> Number
unwrapVh (Vh v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // vmin // viewport
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport minimum unit - 1% of smaller viewport dimension.
-- |
-- | vmin = the smaller of vw or vh. 100vmin = square that fills
-- | the smallest viewport dimension. Good for responsive squares.
newtype Vmin = Vmin Number

derive instance eqVmin :: Eq Vmin
derive instance ordVmin :: Ord Vmin

instance showVmin :: Show Vmin where
  show (Vmin v) = show v <> "vmin"

-- | Create Vmin from Number
vmin :: Number -> Vmin
vmin = Vmin

-- | Create Vmin (plural alias)
vmins :: Number -> Vmin
vmins = vmin

-- | Unwrap Vmin to raw Number
unwrapVmin :: Vmin -> Number
unwrapVmin (Vmin v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // vmax // viewport
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport maximum unit - 1% of larger viewport dimension.
-- |
-- | vmax = the larger of vw or vh. 100vmax = square that fills
-- | the largest viewport dimension.
newtype Vmax = Vmax Number

derive instance eqVmax :: Eq Vmax
derive instance ordVmax :: Ord Vmax

instance showVmax :: Show Vmax where
  show (Vmax v) = show v <> "vmax"

-- | Create Vmax from Number
vmax :: Number -> Vmax
vmax = Vmax

-- | Create Vmax (plural alias)
vmaxs :: Number -> Vmax
vmaxs = vmax

-- | Unwrap Vmax to raw Number
unwrapVmax :: Vmax -> Number
unwrapVmax (Vmax v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // dvw // dynamic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dynamic viewport width - accounts for mobile UI chrome.
-- |
-- | Used on mobile browsers where address bars expand/contract.
-- | dvw is the current viewport width excluding browser chrome.
newtype Dvw = Dvw Number

derive instance eqDvw :: Eq Dvw
derive instance ordDvw :: Ord Dvw

instance showDvw :: Show Dvw where
  show (Dvw v) = show v <> "dvw"

-- | Create Dvw from Number
dvw :: Number -> Dvw
dvw = Dvw

-- | Create Dvw (plural alias)
dvws :: Number -> Dvw
dvws = dvw

-- | Unwrap Dvw to raw Number
unwrapDvw :: Dvw -> Number
unwrapDvw (Dvw v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // dvh // dynamic
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dynamic viewport height - accounts for mobile UI chrome.
-- |
-- | Used on mobile browsers where address bars expand/contract.
-- | dvh is the current viewport height excluding browser chrome.
newtype Dvh = Dvh Number

derive instance eqDvh :: Eq Dvh
derive instance ordDvh :: Ord Dvh

instance showDvh :: Show Dvh where
  show (Dvh v) = show v <> "dvh"

-- | Create Dvh from Number
dvh :: Number -> Dvh
dvh = Dvh

-- | Create Dvh (plural alias)
dvhs :: Number -> Dvh
dvhs = dvh

-- | Unwrap Dvh to raw Number
unwrapDvh :: Dvh -> Number
unwrapDvh (Dvh v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // svw // small
-- ═════════════════════════════════════════════════════════════════════════════

-- | Small viewport width - for @media (min-width: ...)
-- |
-- | Matches the small viewport width (when browser chrome is minimal).
-- | Used in conjunction with svh for container queries.
newtype Svw = Svw Number

derive instance eqSvw :: Eq Svw
derive instance ordSvw :: Ord Svw

instance showSvw :: Show Svw where
  show (Svw v) = show v <> "svw"

-- | Create Svw from Number
svw :: Number -> Svw
svw = Svw

-- | Create Svw (plural alias)
svws :: Number -> Svw
svws = svw

-- | Unwrap Svw to raw Number
unwrapSvw :: Svw -> Number
unwrapSvw (Svw v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // svh // small
-- ═════════════════════════════════════════════════════════════════════════════

-- | Small viewport height - for @media (min-height: ...)
-- |
-- | Matches the small viewport height (when browser chrome is minimal).
newtype Svh = Svh Number

derive instance eqSvh :: Eq Svh
derive instance ordSvh :: Ord Svh

instance showSvh :: Show Svh where
  show (Svh v) = show v <> "svh"

-- | Create Svh from Number
svh :: Number -> Svh
svh = Svh

-- | Create Svh (plural alias)
svhs :: Number -> Svh
svhs = svh

-- | Unwrap Svh to raw Number
unwrapSvh :: Svh -> Number
unwrapSvh (Svh v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // lvw // large
-- ═════════════════════════════════════════════════════════════════════════════

-- | Large viewport width - for @media (max-width: ...)
-- |
-- | Matches the large viewport width (when browser chrome is maximal).
newtype Lvw = Lvw Number

derive instance eqLvw :: Eq Lvw
derive instance ordLvw :: Ord Lvw

instance showLvw :: Show Lvw where
  show (Lvw v) = show v <> "lvw"

-- | Create Lvw from Number
lvw :: Number -> Lvw
lvw = Lvw

-- | Create Lvw (plural alias)
lvws :: Number -> Lvw
lvws = lvw

-- | Unwrap Lvw to raw Number
unwrapLvw :: Lvw -> Number
unwrapLvw (Lvw v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // lvh // large
-- ═════════════════════════════════════════════════════════════════════════════

-- | Large viewport height - for @media (max-height: ...)
-- |
-- | Matches the large viewport height (when browser chrome is maximal).
newtype Lvh = Lvh Number

derive instance eqLvh :: Eq Lvh
derive instance ordLvh :: Ord Lvh

instance showLvh :: Show Lvh where
  show (Lvh v) = show v <> "lvh"

-- | Create Lvh from Number
lvh :: Number -> Lvh
lvh = Lvh

-- | Create Lvh (plural alias)
lvhs :: Number -> Lvh
lvhs = lvh

-- | Unwrap Lvh to raw Number
unwrapLvh :: Lvh -> Number
unwrapLvh (Lvh v) = v
