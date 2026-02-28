-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // elevation // depth
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Depth and parallax compounds for elevation effects.
-- |
-- | ## Parallax
-- | Scroll-linked depth effect where layers move at different speeds.
-- |
-- | ## DepthStack
-- | Z-ordered layers with elevation and shadow.
-- |
-- | ## FloatingUI
-- | Elevated UI element with backdrop and shadow.

module Hydrogen.Schema.Elevation.Depth
  ( -- * Parallax
    ParallaxLayer
  , parallaxLayer
  , parallaxLayerDepth
  , parallaxLayerSpeed
  , parallaxLayerContent
  
  , Parallax
  , parallax
  , parallaxLayers
  , parallaxDirection
  
  , ParallaxDirection(..)
  , parallaxDirectionLabel
  
  -- * Depth Stack
  , DepthLayer
  , depthLayer
  , depthLayerZIndex
  , depthLayerElevation
  , depthLayerContent
  
  , DepthStack
  , depthStack
  , depthStackLayers
  , depthStackBase
  
  -- * Floating UI
  , FloatingUI
  , floatingUI
  , floatingUIElevation
  , floatingUIBackdrop
  , floatingUIShadow
  , floatingUIContent
  
  -- * Backdrop
  , Backdrop
  , backdrop
  , backdropBlur
  , backdropOpacity
  , backdropColor
  , backdropNone
  
  -- * Bokeh (Depth of Field)
  , BokehRadius(..)
  , bokehRadius
  , unwrapBokehRadius
  , bokehRadiusBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , max
  , min
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // parallax
-- ═════════════════════════════════════════════════════════════════════════════

-- | ParallaxDirection - scroll direction for parallax effect.
data ParallaxDirection
  = ParallaxVertical    -- ^ Vertical scroll (most common)
  | ParallaxHorizontal  -- ^ Horizontal scroll
  | ParallaxBoth        -- ^ Both directions

derive instance eqParallaxDirection :: Eq ParallaxDirection
derive instance ordParallaxDirection :: Ord ParallaxDirection

instance showParallaxDirection :: Show ParallaxDirection where
  show = parallaxDirectionLabel

-- | Get label for parallax direction.
parallaxDirectionLabel :: ParallaxDirection -> String
parallaxDirectionLabel ParallaxVertical = "vertical"
parallaxDirectionLabel ParallaxHorizontal = "horizontal"
parallaxDirectionLabel ParallaxBoth = "both"

-- | ParallaxLayer - a single layer in a parallax effect.
type ParallaxLayer =
  { depth :: Number       -- 0.0 = foreground, 1.0 = background
  , speed :: Number       -- Movement speed multiplier (0.0 = static, 1.0 = normal)
  , contentId :: String   -- Reference to content element
  }

-- | Construct a parallax layer.
parallaxLayer :: Number -> Number -> String -> ParallaxLayer
parallaxLayer d s c =
  { depth: max 0.0 (min 1.0 d)
  , speed: max 0.0 (min 2.0 s)
  , contentId: c
  }

-- | Get layer depth.
parallaxLayerDepth :: ParallaxLayer -> Number
parallaxLayerDepth l = l.depth

-- | Get layer speed.
parallaxLayerSpeed :: ParallaxLayer -> Number
parallaxLayerSpeed l = l.speed

-- | Get content ID.
parallaxLayerContent :: ParallaxLayer -> String
parallaxLayerContent l = l.contentId

-- | Parallax - complete parallax configuration.
type Parallax =
  { layers :: Array ParallaxLayer
  , direction :: ParallaxDirection
  }

-- | Construct a parallax effect.
parallax :: Array ParallaxLayer -> ParallaxDirection -> Parallax
parallax ls dir = { layers: ls, direction: dir }

-- | Get layers.
parallaxLayers :: Parallax -> Array ParallaxLayer
parallaxLayers p = p.layers

-- | Get direction.
parallaxDirection :: Parallax -> ParallaxDirection
parallaxDirection p = p.direction

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // depth stack
-- ═════════════════════════════════════════════════════════════════════════════

-- | DepthLayer - a layer in a depth stack.
type DepthLayer =
  { zIndex :: Int
  , elevation :: Number   -- Shadow elevation in dp/px
  , contentId :: String
  }

-- | Construct a depth layer.
depthLayer :: Int -> Number -> String -> DepthLayer
depthLayer z e c =
  { zIndex: z
  , elevation: max 0.0 e
  , contentId: c
  }

-- | Get z-index.
depthLayerZIndex :: DepthLayer -> Int
depthLayerZIndex l = l.zIndex

-- | Get elevation.
depthLayerElevation :: DepthLayer -> Number
depthLayerElevation l = l.elevation

-- | Get content ID.
depthLayerContent :: DepthLayer -> String
depthLayerContent l = l.contentId

-- | DepthStack - z-ordered layers with elevation.
type DepthStack =
  { layers :: Array DepthLayer
  , baseElevation :: Number   -- Base elevation for entire stack
  }

-- | Construct a depth stack.
depthStack :: Array DepthLayer -> Number -> DepthStack
depthStack ls base =
  { layers: ls
  , baseElevation: max 0.0 base
  }

-- | Get layers.
depthStackLayers :: DepthStack -> Array DepthLayer
depthStackLayers s = s.layers

-- | Get base elevation.
depthStackBase :: DepthStack -> Number
depthStackBase s = s.baseElevation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // backdrop
-- ═════════════════════════════════════════════════════════════════════════════

-- | Backdrop - visual effect behind floating elements.
type Backdrop =
  { blurRadius :: Number    -- Blur in pixels
  , opacity :: Number       -- 0.0 to 1.0
  , colorHex :: String      -- Background color (hex)
  }

-- | Construct a backdrop.
backdrop :: Number -> Number -> String -> Backdrop
backdrop blur op color =
  { blurRadius: max 0.0 blur
  , opacity: max 0.0 (min 1.0 op)
  , colorHex: color
  }

-- | Get blur radius.
backdropBlur :: Backdrop -> Number
backdropBlur b = b.blurRadius

-- | Get opacity.
backdropOpacity :: Backdrop -> Number
backdropOpacity b = b.opacity

-- | Get color.
backdropColor :: Backdrop -> String
backdropColor b = b.colorHex

-- | No backdrop effect.
backdropNone :: Backdrop
backdropNone = { blurRadius: 0.0, opacity: 0.0, colorHex: "" }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // floating ui
-- ═════════════════════════════════════════════════════════════════════════════

-- | FloatingUI - elevated UI element with backdrop and shadow.
type FloatingUI =
  { elevation :: Number     -- Elevation level (dp)
  , backdrop :: Backdrop
  , shadowOpacity :: Number
  , contentId :: String
  }

-- | Construct a floating UI element.
floatingUI :: Number -> Backdrop -> Number -> String -> FloatingUI
floatingUI e bd shadow c =
  { elevation: max 0.0 e
  , backdrop: bd
  , shadowOpacity: max 0.0 (min 1.0 shadow)
  , contentId: c
  }

-- | Get elevation.
floatingUIElevation :: FloatingUI -> Number
floatingUIElevation f = f.elevation

-- | Get backdrop.
floatingUIBackdrop :: FloatingUI -> Backdrop
floatingUIBackdrop f = f.backdrop

-- | Get shadow opacity.
floatingUIShadow :: FloatingUI -> Number
floatingUIShadow f = f.shadowOpacity

-- | Get content ID.
floatingUIContent :: FloatingUI -> String
floatingUIContent f = f.contentId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // bokeh
-- ═════════════════════════════════════════════════════════════════════════════

-- | BokehRadius - depth of field blur radius.
-- | Simulates camera lens bokeh effect.
newtype BokehRadius = BokehRadius Number

derive instance eqBokehRadius :: Eq BokehRadius
derive instance ordBokehRadius :: Ord BokehRadius

instance showBokehRadius :: Show BokehRadius where
  show (BokehRadius r) = "(BokehRadius " <> show r <> "px)"

-- | Bounds for bokeh radius.
bokehRadiusBounds :: Bounded.NumberBounds
bokehRadiusBounds = Bounded.numberBounds 0.0 100.0 "BokehRadius" "Depth of field blur radius"

-- | Construct a bokeh radius.
bokehRadius :: Number -> BokehRadius
bokehRadius r = BokehRadius (Bounded.clampNumber 0.0 100.0 r)

-- | Unwrap bokeh radius.
unwrapBokehRadius :: BokehRadius -> Number
unwrapBokehRadius (BokehRadius r) = r
