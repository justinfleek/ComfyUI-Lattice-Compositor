-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // elevation // depth-effects
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Depth effect compounds — complex elevation behaviors.
-- |
-- | ## Design Philosophy
-- |
-- | These compounds combine multiple elevation primitives to create
-- | sophisticated depth illusions:
-- |
-- | - **Parallax**: Scroll-linked depth movement (layers move at different speeds)
-- | - **DepthStack**: Z-ordered layer composition (explicit stacking)
-- | - **FloatingUI**: Combined elevation + backdrop blur (modern glass effect)
-- |
-- | ## Pure Data
-- |
-- | These are configuration records, NOT runtime behaviors. The runtime
-- | interprets these records to produce the actual effects. This means:
-- |
-- | - Same config = same visual result (deterministic)
-- | - Configs can be serialized, compared, composed
-- | - No side effects in the type definitions
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Elevation.DepthEffects as DE
-- |
-- | -- Parallax scrolling hero section
-- | heroParallax :: DE.Parallax
-- | heroParallax = DE.parallax
-- |   { baseLayer: DE.parallaxLayer { depth: 0.0, content: "background" }
-- |   , layers: 
-- |       [ DE.parallaxLayer { depth: 0.3, content: "mountains" }
-- |       , DE.parallaxLayer { depth: 0.6, content: "trees" }
-- |       , DE.parallaxLayer { depth: 1.0, content: "foreground" }
-- |       ]
-- |   }
-- |
-- | -- Floating toolbar with blur
-- | toolbar :: DE.FloatingUI
-- | toolbar = DE.floatingUI
-- |   { elevation: SemanticElevation.Floating
-- |   , backdropBlur: 12.0
-- |   , backdropSaturation: 1.2
-- |   }
-- | ```

module Hydrogen.Schema.Elevation.DepthEffects
  ( -- * Parallax Effect
    Parallax
  , ParallaxLayer
  , ParallaxDepth
  , ScrollAxis(..)
  , parallax
  , parallaxLayer
  , parallaxDepth
  , getParallaxLayers
  , getParallaxDepth
  , addParallaxLayer
  
  -- * Parallax Calculations
  , calculateDisplacement
  , calculateLayerY
  , scaleParallaxDepth
  , addParallaxDepths
  , subtractParallaxDepths
  , compareParallaxDepths
  , sortLayersByDepth
  
  -- * Depth Stack
  , DepthStack
  , DepthLayer
  , depthStack
  , depthLayer
  , emptyStack
  , pushLayer
  , popLayer
  , getStackLayers
  , stackDepth
  
  -- * Depth Stack Operations
  , mergeStacks
  , filterLayers
  , findLayerById
  , sortStackByZIndex
  , compareLayerZIndex
  , topLayer
  , bottomLayer
  , layersBetween
  
  -- * Floating UI
  , FloatingUI
  , BackdropBlur
  , BackdropSaturation
  , floatingUI
  , backdropBlur
  , backdropSaturation
  , getBackdropBlur
  , getBackdropSaturation
  , getFloatingElevation
  , withBackdropBlur
  , withBackdropSaturation
  
  -- * Backdrop Operations
  , combineBackdropBlur
  , maxBackdropBlur
  , scaleBackdropBlur
  
  -- * Conversion (Legacy CSS, not FFI)
  , parallaxToLegacyCss
  , floatingToLegacyCss
  
  -- * Predicates
  , hasParallax
  , hasBackdropBlur
  , isFloating
  , hasLayer
  , isEmptyStack
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , not
  , negate
  , Ordering(LT, GT, EQ)
  , (+)
  , (-)
  , (*)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (<>)
  , (==)
  , ($)
  , (&&)
  , max
  , min
  )

import Data.Array (length, snoc, filter, sortBy, head, findIndex)
import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing), isJust)
import Data.Int as Int
import Hydrogen.Schema.Elevation.SemanticElevation 
  ( ElevationLevel(Floating)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // parallax depth
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parallax depth factor (0.0 - 1.0).
-- |
-- | Controls how fast a layer moves relative to scroll:
-- | - 0.0: Fixed (doesn't move with scroll)
-- | - 0.5: Moves at half scroll speed
-- | - 1.0: Moves at full scroll speed (normal scrolling)
-- | - >1.0: Moves faster than scroll (uncommon, can cause motion sickness)
-- |
-- | Values are clamped to 0.0 - 2.0 for safety.
newtype ParallaxDepth = ParallaxDepth Number

derive instance eqParallaxDepth :: Eq ParallaxDepth
derive instance ordParallaxDepth :: Ord ParallaxDepth

instance showParallaxDepth :: Show ParallaxDepth where
  show (ParallaxDepth n) = "ParallaxDepth " <> show n

-- | Create a parallax depth factor
-- |
-- | Clamped to 0.0 - 2.0.
parallaxDepth :: Number -> ParallaxDepth
parallaxDepth n = ParallaxDepth (clampRange 0.0 2.0 n)

-- | Extract the depth factor
getParallaxDepth :: ParallaxDepth -> Number
getParallaxDepth (ParallaxDepth n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // parallax layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single layer in a parallax composition.
-- |
-- | Each layer has a depth factor and a content identifier.
-- | The content identifier is abstract — it could be an image URL,
-- | an element ID, or any other reference the runtime understands.
type ParallaxLayer =
  { depth :: ParallaxDepth      -- ^ How fast this layer scrolls
  , contentId :: String         -- ^ Identifier for layer content
  , offsetY :: Number           -- ^ Initial Y offset in pixels
  }

-- | Create a parallax layer
parallaxLayer :: 
  { depth :: Number
  , contentId :: String
  , offsetY :: Number
  } -> ParallaxLayer
parallaxLayer config =
  { depth: parallaxDepth config.depth
  , contentId: config.contentId
  , offsetY: config.offsetY
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // parallax effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parallax scrolling configuration.
-- |
-- | Defines a set of layers that move at different speeds during scroll,
-- | creating an illusion of depth.
type Parallax =
  { layers :: Array ParallaxLayer  -- ^ All layers, front to back
  , scrollAxis :: ScrollAxis       -- ^ Scroll direction
  , perspective :: Number          -- ^ CSS perspective value (px)
  }

-- | Scroll axis for parallax
data ScrollAxis
  = ScrollVertical
  | ScrollHorizontal
  | ScrollBoth

derive instance eqScrollAxis :: Eq ScrollAxis

instance showScrollAxis :: Show ScrollAxis where
  show ScrollVertical = "vertical"
  show ScrollHorizontal = "horizontal"
  show ScrollBoth = "both"

-- | Create a parallax configuration
parallax ::
  { layers :: Array ParallaxLayer
  , scrollAxis :: ScrollAxis
  , perspective :: Number
  } -> Parallax
parallax config =
  { layers: config.layers
  , scrollAxis: config.scrollAxis
  , perspective: clampNonNegative config.perspective
  }

-- | Get all layers from parallax config
getParallaxLayers :: Parallax -> Array ParallaxLayer
getParallaxLayers p = p.layers

-- | Add a layer to parallax (appended to front)
addParallaxLayer :: ParallaxLayer -> Parallax -> Parallax
addParallaxLayer layer p = p { layers = snoc p.layers layer }

-- | Check if parallax has multiple layers (actual parallax effect)
hasParallax :: Parallax -> Boolean
hasParallax p = length p.layers > 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // parallax calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate displacement for a layer at a given scroll position.
-- |
-- | Displacement = scrollPosition * (1.0 - depth)
-- | - depth 0.0 (fixed): displacement = scrollPosition (moves opposite to scroll)
-- | - depth 0.5: displacement = scrollPosition * 0.5
-- | - depth 1.0 (normal): displacement = 0 (moves with scroll)
calculateDisplacement :: ParallaxDepth -> Number -> Number
calculateDisplacement (ParallaxDepth depth) scrollPosition =
  scrollPosition * (1.0 - depth)

-- | Calculate the Y position of a layer given scroll position.
-- |
-- | Combines the layer's initial offset with scroll-based displacement.
calculateLayerY :: ParallaxLayer -> Number -> Number
calculateLayerY layer scrollPosition =
  layer.offsetY - calculateDisplacement layer.depth scrollPosition

-- | Scale a parallax depth by a factor.
-- |
-- | Useful for adjusting parallax intensity. Result clamped to 0.0-2.0.
scaleParallaxDepth :: Number -> ParallaxDepth -> ParallaxDepth
scaleParallaxDepth factor (ParallaxDepth d) = 
  parallaxDepth (d * factor)

-- | Add two parallax depths (clamped result).
addParallaxDepths :: ParallaxDepth -> ParallaxDepth -> ParallaxDepth
addParallaxDepths (ParallaxDepth a) (ParallaxDepth b) =
  parallaxDepth (a + b)

-- | Subtract parallax depths (clamped result).
subtractParallaxDepths :: ParallaxDepth -> ParallaxDepth -> ParallaxDepth
subtractParallaxDepths (ParallaxDepth a) (ParallaxDepth b) =
  parallaxDepth (a - b)

-- | Compare two parallax depths.
-- |
-- | Useful for sorting layers by depth.
compareParallaxDepths :: ParallaxDepth -> ParallaxDepth -> Ordering
compareParallaxDepths (ParallaxDepth a) (ParallaxDepth b) = compare a b

-- | Sort parallax layers by depth (back to front).
-- |
-- | Layers with lower depth values are considered "farther back"
-- | and should be rendered first.
sortLayersByDepth :: Array ParallaxLayer -> Array ParallaxLayer
sortLayersByDepth = sortBy compareLayerDepth
  where
    compareLayerDepth :: ParallaxLayer -> ParallaxLayer -> Ordering
    compareLayerDepth a b = compareParallaxDepths a.depth b.depth

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // depth layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | A layer in a depth stack.
-- |
-- | Unlike parallax layers, depth layers have explicit z-index values
-- | and don't move with scroll.
type DepthLayer =
  { zIndex :: Int               -- ^ Stacking order
  , contentId :: String         -- ^ Identifier for layer content
  , opacity :: Number           -- ^ Layer opacity (0.0 - 1.0)
  }

-- | Create a depth layer
depthLayer ::
  { zIndex :: Int
  , contentId :: String
  , opacity :: Number
  } -> DepthLayer
depthLayer config =
  { zIndex: config.zIndex
  , contentId: config.contentId
  , opacity: clampRange 0.0 1.0 config.opacity
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // depth stack
-- ═════════════════════════════════════════════════════════════════════════════

-- | Depth stack — explicit z-ordered layer composition.
-- |
-- | Unlike CSS's implicit stacking, this makes layer order explicit
-- | and predictable. Useful for complex compositions where stacking
-- | order must be deterministic.
newtype DepthStack = DepthStack (Array DepthLayer)

derive instance eqDepthStack :: Eq DepthStack

instance showDepthStack :: Show DepthStack where
  show (DepthStack ls) = "DepthStack[" <> show (length ls) <> " layers]"

-- | Create a depth stack from layers
depthStack :: Array DepthLayer -> DepthStack
depthStack = DepthStack

-- | Empty depth stack
emptyStack :: DepthStack
emptyStack = DepthStack []

-- | Push a layer onto the stack (highest z-index)
pushLayer :: DepthLayer -> DepthStack -> DepthStack
pushLayer layer (DepthStack ls) = DepthStack (snoc ls layer)

-- | Pop the top layer from the stack
popLayer :: DepthStack -> Maybe { layer :: DepthLayer, remaining :: DepthStack }
popLayer (DepthStack ls) = case Array.unsnoc ls of
  Nothing -> Nothing
  Just { init, last } -> Just { layer: last, remaining: DepthStack init }

-- | Get all layers in the stack
getStackLayers :: DepthStack -> Array DepthLayer
getStackLayers (DepthStack ls) = ls

-- | Get the number of layers in the stack
stackDepth :: DepthStack -> Int
stackDepth (DepthStack ls) = length ls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // depth stack operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Merge two depth stacks.
-- |
-- | Layers from the second stack are appended after the first.
-- | Does NOT re-sort by z-index; use sortStackByZIndex if needed.
mergeStacks :: DepthStack -> DepthStack -> DepthStack
mergeStacks (DepthStack a) (DepthStack b) = DepthStack (a <> b)

-- | Filter layers in a stack by a predicate.
filterLayers :: (DepthLayer -> Boolean) -> DepthStack -> DepthStack
filterLayers predicate (DepthStack ls) = DepthStack (filter predicate ls)

-- | Find a layer by content ID.
-- |
-- | Returns the first layer with matching contentId, or Nothing.
findLayerById :: String -> DepthStack -> Maybe DepthLayer
findLayerById targetId (DepthStack ls) =
  head (filter (\layer -> layer.contentId == targetId) ls)

-- | Sort stack layers by z-index (ascending).
-- |
-- | Lower z-index layers are rendered first (behind higher ones).
sortStackByZIndex :: DepthStack -> DepthStack
sortStackByZIndex (DepthStack ls) = DepthStack (sortBy compareLayerZIndex ls)

-- | Compare two depth layers by z-index.
compareLayerZIndex :: DepthLayer -> DepthLayer -> Ordering
compareLayerZIndex a b = compare a.zIndex b.zIndex

-- | Get the top layer (highest z-index).
-- |
-- | Returns Nothing if stack is empty.
topLayer :: DepthStack -> Maybe DepthLayer
topLayer stack =
  let sorted = sortStackByZIndex stack
      (DepthStack ls) = sorted
  in Array.last ls

-- | Get the bottom layer (lowest z-index).
-- |
-- | Returns Nothing if stack is empty.
bottomLayer :: DepthStack -> Maybe DepthLayer
bottomLayer stack =
  let sorted = sortStackByZIndex stack
      (DepthStack ls) = sorted
  in head ls

-- | Get layers between two z-index values (inclusive).
layersBetween :: Int -> Int -> DepthStack -> DepthStack
layersBetween minZ maxZ (DepthStack ls) =
  DepthStack (filter inRange ls)
  where
    inRange :: DepthLayer -> Boolean
    inRange layer = layer.zIndex >= minZ && layer.zIndex <= maxZ

-- | Check if a stack contains a layer with the given content ID.
hasLayer :: String -> DepthStack -> Boolean
hasLayer targetId stack = isJust (findLayerById targetId stack)

-- | Check if a stack is empty.
isEmptyStack :: DepthStack -> Boolean
isEmptyStack (DepthStack ls) = length ls == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // backdrop blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Backdrop blur radius in pixels.
-- |
-- | CSS `backdrop-filter: blur()` blurs everything behind the element,
-- | creating a frosted glass effect.
newtype BackdropBlur = BackdropBlur Number

derive instance eqBackdropBlur :: Eq BackdropBlur
derive instance ordBackdropBlur :: Ord BackdropBlur

instance showBackdropBlur :: Show BackdropBlur where
  show (BackdropBlur n) = "BackdropBlur " <> show n <> "px"

-- | Create a backdrop blur value
-- |
-- | Clamped to >= 0.
backdropBlur :: Number -> BackdropBlur
backdropBlur n = BackdropBlur (clampNonNegative n)

-- | Extract the blur radius
getBackdropBlur :: BackdropBlur -> Number
getBackdropBlur (BackdropBlur n) = n

-- | Backdrop saturation multiplier.
-- |
-- | CSS `backdrop-filter: saturate()` adjusts color saturation of
-- | content behind the element:
-- | - 0.0: Fully desaturated (grayscale)
-- | - 1.0: Normal saturation
-- | - >1.0: Increased saturation
newtype BackdropSaturation = BackdropSaturation Number

derive instance eqBackdropSaturation :: Eq BackdropSaturation
derive instance ordBackdropSaturation :: Ord BackdropSaturation

instance showBackdropSaturation :: Show BackdropSaturation where
  show (BackdropSaturation n) = "BackdropSaturation " <> show n

-- | Create a backdrop saturation value
-- |
-- | Clamped to >= 0.
backdropSaturation :: Number -> BackdropSaturation
backdropSaturation n = BackdropSaturation (clampNonNegative n)

-- | Extract the saturation multiplier
getBackdropSaturation :: BackdropSaturation -> Number
getBackdropSaturation (BackdropSaturation n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // backdrop operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combine two backdrop blurs (additive).
-- |
-- | When multiple blur elements overlap, their visual effect is approximately
-- | additive. This function combines them for calculation purposes.
combineBackdropBlur :: BackdropBlur -> BackdropBlur -> BackdropBlur
combineBackdropBlur (BackdropBlur a) (BackdropBlur b) =
  backdropBlur (a + b)

-- | Get the maximum of two backdrop blurs.
-- |
-- | Useful when you want the dominant blur effect rather than combining.
maxBackdropBlur :: BackdropBlur -> BackdropBlur -> BackdropBlur
maxBackdropBlur (BackdropBlur a) (BackdropBlur b) =
  BackdropBlur (max a b)

-- | Scale a backdrop blur by a factor.
-- |
-- | Useful for responsive adjustments or animation.
scaleBackdropBlur :: Number -> BackdropBlur -> BackdropBlur
scaleBackdropBlur factor (BackdropBlur b) =
  backdropBlur (b * factor)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // floating ui
-- ═════════════════════════════════════════════════════════════════════════════

-- | Floating UI — combined elevation + backdrop effects.
-- |
-- | This compound represents the modern "glassmorphism" style:
-- | - Elevated above content (shadow)
-- | - Translucent with blur (frosted glass)
-- | - Optional saturation adjustment
-- |
-- | Common uses: toolbars, modals, sidebars, floating action buttons.
type FloatingUI =
  { elevation :: ElevationLevel        -- ^ Semantic elevation
  , blur :: BackdropBlur               -- ^ Blur radius
  , saturation :: BackdropSaturation   -- ^ Saturation adjustment
  , backgroundOpacity :: Number        -- ^ Background color opacity (0-1)
  }

-- | Create a floating UI configuration
floatingUI ::
  { elevation :: ElevationLevel
  , blur :: Number
  , saturation :: Number
  , backgroundOpacity :: Number
  } -> FloatingUI
floatingUI config =
  { elevation: config.elevation
  , blur: backdropBlur config.blur
  , saturation: backdropSaturation config.saturation
  , backgroundOpacity: clampRange 0.0 1.0 config.backgroundOpacity
  }

-- | Get elevation from floating UI
getFloatingElevation :: FloatingUI -> ElevationLevel
getFloatingElevation f = f.elevation

-- | Update backdrop blur
withBackdropBlur :: Number -> FloatingUI -> FloatingUI
withBackdropBlur b f = f { blur = backdropBlur b }

-- | Update backdrop saturation
withBackdropSaturation :: Number -> FloatingUI -> FloatingUI
withBackdropSaturation s f = f { saturation = backdropSaturation s }

-- | Check if floating UI has backdrop blur
hasBackdropBlur :: FloatingUI -> Boolean
hasBackdropBlur f = 
  let BackdropBlur b = f.blur
  in b > 0.0

-- | Check if floating UI is at Floating elevation or higher
isFloating :: FloatingUI -> Boolean
isFloating f = 
  let level = f.elevation
  in level >= floatingLevel
  where
    floatingLevel :: ElevationLevel
    floatingLevel = floatingLevelValue

-- Import the Floating level constructor
floatingLevelValue :: ElevationLevel
floatingLevelValue = Floating

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert parallax to CSS transform style hints.
-- |
-- | Note: Full parallax requires JavaScript for scroll handling.
-- | This generates the CSS perspective setup.
-- | NOT an FFI boundary — pure string generation.
parallaxToLegacyCss :: Parallax -> String
parallaxToLegacyCss p =
  "perspective: " <> show p.perspective <> "px; transform-style: preserve-3d;"

-- | Convert floating UI to CSS backdrop-filter string.
-- |
-- | NOT an FFI boundary — pure string generation.
floatingToLegacyCss :: FloatingUI -> String
floatingToLegacyCss f =
  let
    BackdropBlur b = f.blur
    BackdropSaturation s = f.saturation
    blurPart = if b > 0.0 then "blur(" <> show b <> "px)" else ""
    satPart = if s == 1.0 then "" else " saturate(" <> show s <> ")"
    combined = blurPart <> satPart
  in
    if combined == "" then "none" else combined

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to non-negative
clampNonNegative :: Number -> Number
clampNonNegative n = if n < 0.0 then 0.0 else n

-- | Clamp to range
clampRange :: Number -> Number -> Number -> Number
clampRange minVal maxVal n
  | n < minVal = minVal
  | n > maxVal = maxVal
  | true = n
