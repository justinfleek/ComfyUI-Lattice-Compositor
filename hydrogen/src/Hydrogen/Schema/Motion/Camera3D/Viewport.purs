-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // motion // camera3d // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera3D Viewport: Viewport state and custom view management.
-- |
-- | Tracks layout, view assignments, and orbit camera parameters.

module Hydrogen.Schema.Motion.Camera3D.Viewport
  ( -- * Custom View State
    CustomViewState(..)
  , mkCustomViewState
  , defaultCustomViewState
  
    -- * Custom Views
  , CustomViews(..)
  , mkCustomViews
  , defaultCustomViews
  
    -- * Viewport State
  , ViewportState(..)
  , mkViewportState
  , defaultViewportState
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Data.Array (singleton)
import Hydrogen.Schema.Bounded (clampNumberMin)

import Hydrogen.Schema.Motion.Camera3D.Enums
  ( ViewType(VTActiveCamera)
  , ViewLayout(VLOneView)
  )
import Hydrogen.Schema.Motion.Camera3D.Vectors (Vec2, Vec3, vec2Zero, vec3Zero)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // custom // view-state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Custom view state for 3D viewport.
-- |
-- | Stores orbit camera parameters for custom views.
newtype CustomViewState = CustomViewState
  { orbitCenter   :: Vec3    -- ^ Center of orbit
  , orbitDistance :: Number  -- ^ Distance from center (positive)
  , orbitPhi      :: Number  -- ^ Vertical angle (0=top, 90=side)
  , orbitTheta    :: Number  -- ^ Horizontal angle
  , orthoZoom     :: Number  -- ^ Orthographic zoom (positive)
  , orthoOffset   :: Vec2    -- ^ Orthographic offset
  }

derive instance eqCustomViewState :: Eq CustomViewState

instance showCustomViewState :: Show CustomViewState where
  show (CustomViewState v) =
    "(CustomView dist:" <> show v.orbitDistance
    <> " phi:" <> show v.orbitPhi
    <> " theta:" <> show v.orbitTheta <> ")"

-- | Create custom view state with validation.
mkCustomViewState
  :: { orbitCenter   :: Vec3
     , orbitDistance :: Number
     , orbitPhi      :: Number
     , orbitTheta    :: Number
     , orthoZoom     :: Number
     , orthoOffset   :: Vec2
     }
  -> CustomViewState
mkCustomViewState cfg = CustomViewState
  { orbitCenter: cfg.orbitCenter
  , orbitDistance: clampNumberMin 0.1 cfg.orbitDistance
  , orbitPhi: cfg.orbitPhi
  , orbitTheta: cfg.orbitTheta
  , orthoZoom: clampNumberMin 0.1 cfg.orthoZoom
  , orthoOffset: cfg.orthoOffset
  }

-- | Default custom view state.
defaultCustomViewState :: CustomViewState
defaultCustomViewState = CustomViewState
  { orbitCenter: vec3Zero
  , orbitDistance: 1500.0
  , orbitPhi: 30.0
  , orbitTheta: 45.0
  , orthoZoom: 1.0
  , orthoOffset: vec2Zero
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // custom // views
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container for three custom view states.
newtype CustomViews = CustomViews
  { custom1 :: CustomViewState
  , custom2 :: CustomViewState
  , custom3 :: CustomViewState
  }

derive instance eqCustomViews :: Eq CustomViews

instance showCustomViews :: Show CustomViews where
  show _ = "(CustomViews 3 views)"

-- | Create custom views.
mkCustomViews
  :: CustomViewState
  -> CustomViewState
  -> CustomViewState
  -> CustomViews
mkCustomViews c1 c2 c3 = CustomViews
  { custom1: c1
  , custom2: c2
  , custom3: c3
  }

-- | Default custom views.
defaultCustomViews :: CustomViews
defaultCustomViews = CustomViews
  { custom1: defaultCustomViewState
  , custom2: defaultCustomViewState
  , custom3: defaultCustomViewState
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Viewport state for 3D composition.
-- |
-- | Tracks layout, view assignments, and active view.
newtype ViewportState = ViewportState
  { layout          :: ViewLayout
  , views           :: Array ViewType  -- ^ Which view in each panel
  , customViews     :: CustomViews
  , activeViewIndex :: Int             -- ^ Currently active view (0-based)
  }

derive instance eqViewportState :: Eq ViewportState

instance showViewportState :: Show ViewportState where
  show (ViewportState v) =
    "(ViewportState " <> show v.layout
    <> " active:" <> show v.activeViewIndex <> ")"

-- | Create viewport state.
mkViewportState
  :: { layout          :: ViewLayout
     , views           :: Array ViewType
     , customViews     :: CustomViews
     , activeViewIndex :: Int
     }
  -> ViewportState
mkViewportState cfg = ViewportState cfg

-- | Default viewport state (single active camera view).
defaultViewportState :: ViewportState
defaultViewportState = ViewportState
  { layout: VLOneView
  , views: singleton VTActiveCamera
  , customViews: defaultCustomViews
  , activeViewIndex: 0
  }
