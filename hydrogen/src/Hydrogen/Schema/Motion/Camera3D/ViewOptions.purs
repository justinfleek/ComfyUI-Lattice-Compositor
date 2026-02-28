-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // motion // camera3d // view-options
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Camera3D ViewOptions: Display settings for 3D composition views.
-- |
-- | Controls visibility of guides, wireframes, motion paths, and overlays.

module Hydrogen.Schema.Motion.Camera3D.ViewOptions
  ( ViewOptions(..)
  , mkViewOptions
  , defaultViewOptions
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Motion.Camera3D.Enums (WireframeVisibility(WVSelected))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // view // options
-- ═════════════════════════════════════════════════════════════════════════════

-- | View display options for 3D composition.
-- |
-- | Controls visibility of guides, wireframes, and overlays.
newtype ViewOptions = ViewOptions
  { cameraWireframes      :: WireframeVisibility
  , lightWireframes       :: WireframeVisibility
  , showMotionPaths       :: Boolean
  , showLayerPaths        :: Boolean  -- ^ Shape/mask path visibility
  , showLayerHandles      :: Boolean
  , showSafeZones         :: Boolean
  , showGrid              :: Boolean
  , showRulers            :: Boolean
  , show3DReferenceAxes   :: Boolean
  , showCompositionBounds :: Boolean  -- ^ Canvas as 3D plane
  , showFocalPlane        :: Boolean  -- ^ DOF focus indicator
  }

derive instance eqViewOptions :: Eq ViewOptions

instance showViewOptions :: Show ViewOptions where
  show (ViewOptions v) =
    "(ViewOptions motionPaths:" <> show v.showMotionPaths
    <> " grid:" <> show v.showGrid <> ")"

-- | Create view options.
mkViewOptions
  :: { cameraWireframes      :: WireframeVisibility
     , lightWireframes       :: WireframeVisibility
     , showMotionPaths       :: Boolean
     , showLayerPaths        :: Boolean
     , showLayerHandles      :: Boolean
     , showSafeZones         :: Boolean
     , showGrid              :: Boolean
     , showRulers            :: Boolean
     , show3DReferenceAxes   :: Boolean
     , showCompositionBounds :: Boolean
     , showFocalPlane        :: Boolean
     }
  -> ViewOptions
mkViewOptions cfg = ViewOptions cfg

-- | Default view options.
defaultViewOptions :: ViewOptions
defaultViewOptions = ViewOptions
  { cameraWireframes: WVSelected
  , lightWireframes: WVSelected
  , showMotionPaths: true
  , showLayerPaths: true
  , showLayerHandles: true
  , showSafeZones: false
  , showGrid: false
  , showRulers: true
  , show3DReferenceAxes: true
  , showCompositionBounds: true
  , showFocalPlane: false
  }
