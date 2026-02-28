-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // composition // blend
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Blend Modes — How layers composite with layers below.
-- |
-- | 36 blend modes organized by category:
-- | - Normal: normal, dissolve
-- | - Darken: darken, multiply, color-burn, linear-burn, darker-color
-- | - Lighten: lighten, screen, color-dodge, linear-dodge, lighter-color, add
-- | - Contrast: overlay, soft-light, hard-light, vivid-light, linear-light, pin-light, hard-mix
-- | - Inversion: difference, exclusion, subtract, divide
-- | - Component: hue, saturation, color, luminosity
-- | - Utility: stencil-alpha, stencil-luma, silhouette-alpha, silhouette-luma
-- |
-- | Also includes composite operations (Porter-Duff).

module Hydrogen.Composition.Blend
  ( -- * Blend Mode
    BlendMode(..)
  , BlendCategory(..)
  , blendCategory
  , defaultBlendMode
  
  -- * Composite Operation
  , CompositeOp(..)
  , defaultCompositeOp
  
  -- * Blend Helpers
  , isPassThrough
  , affectsTransparency
  , sameCategory
  , isLighteningMode
  , isDarkeningMode
  , blendModeLabel
  , compositeModeLabel
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (||)
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // blend category
-- ═══════════════════════════════════════════════════════════════════════════════

data BlendCategory
  = CategoryNormal
  | CategoryDarken
  | CategoryLighten
  | CategoryContrast
  | CategoryInversion
  | CategoryComponent
  | CategoryUtility

derive instance eqBlendCategory :: Eq BlendCategory
derive instance ordBlendCategory :: Ord BlendCategory

instance showBlendCategory :: Show BlendCategory where
  show CategoryNormal = "normal"
  show CategoryDarken = "darken"
  show CategoryLighten = "lighten"
  show CategoryContrast = "contrast"
  show CategoryInversion = "inversion"
  show CategoryComponent = "component"
  show CategoryUtility = "utility"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // blend mode
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Blend mode — how this layer's pixels combine with pixels below.
data BlendMode
  -- Normal (2)
  = BlendNormal
  | BlendDissolve
  -- Darken (5)
  | BlendDarken
  | BlendMultiply
  | BlendColorBurn
  | BlendLinearBurn
  | BlendDarkerColor
  -- Lighten (6)
  | BlendLighten
  | BlendScreen
  | BlendColorDodge
  | BlendLinearDodge
  | BlendLighterColor
  | BlendAdd
  -- Contrast (7)
  | BlendOverlay
  | BlendSoftLight
  | BlendHardLight
  | BlendVividLight
  | BlendLinearLight
  | BlendPinLight
  | BlendHardMix
  -- Inversion (4)
  | BlendDifference
  | BlendExclusion
  | BlendSubtract
  | BlendDivide
  -- Component (4)
  | BlendHue
  | BlendSaturation
  | BlendColor
  | BlendLuminosity
  -- Utility (8)
  | BlendStencilAlpha
  | BlendStencilLuma
  | BlendSilhouetteAlpha
  | BlendSilhouetteLuma
  | BlendAlphaAdd
  | BlendLuminescentPremul
  | BlendPassThrough        -- For groups: don't composite, children blend directly
  | BlendBehind             -- Draw behind existing pixels

derive instance eqBlendMode :: Eq BlendMode
derive instance ordBlendMode :: Ord BlendMode

instance showBlendMode :: Show BlendMode where
  show BlendNormal = "normal"
  show BlendDissolve = "dissolve"
  show BlendDarken = "darken"
  show BlendMultiply = "multiply"
  show BlendColorBurn = "color-burn"
  show BlendLinearBurn = "linear-burn"
  show BlendDarkerColor = "darker-color"
  show BlendLighten = "lighten"
  show BlendScreen = "screen"
  show BlendColorDodge = "color-dodge"
  show BlendLinearDodge = "linear-dodge"
  show BlendLighterColor = "lighter-color"
  show BlendAdd = "add"
  show BlendOverlay = "overlay"
  show BlendSoftLight = "soft-light"
  show BlendHardLight = "hard-light"
  show BlendVividLight = "vivid-light"
  show BlendLinearLight = "linear-light"
  show BlendPinLight = "pin-light"
  show BlendHardMix = "hard-mix"
  show BlendDifference = "difference"
  show BlendExclusion = "exclusion"
  show BlendSubtract = "subtract"
  show BlendDivide = "divide"
  show BlendHue = "hue"
  show BlendSaturation = "saturation"
  show BlendColor = "color"
  show BlendLuminosity = "luminosity"
  show BlendStencilAlpha = "stencil-alpha"
  show BlendStencilLuma = "stencil-luma"
  show BlendSilhouetteAlpha = "silhouette-alpha"
  show BlendSilhouetteLuma = "silhouette-luma"
  show BlendAlphaAdd = "alpha-add"
  show BlendLuminescentPremul = "luminescent-premul"
  show BlendPassThrough = "pass-through"
  show BlendBehind = "behind"

-- | Get the category of a blend mode.
blendCategory :: BlendMode -> BlendCategory
blendCategory BlendNormal = CategoryNormal
blendCategory BlendDissolve = CategoryNormal
blendCategory BlendDarken = CategoryDarken
blendCategory BlendMultiply = CategoryDarken
blendCategory BlendColorBurn = CategoryDarken
blendCategory BlendLinearBurn = CategoryDarken
blendCategory BlendDarkerColor = CategoryDarken
blendCategory BlendLighten = CategoryLighten
blendCategory BlendScreen = CategoryLighten
blendCategory BlendColorDodge = CategoryLighten
blendCategory BlendLinearDodge = CategoryLighten
blendCategory BlendLighterColor = CategoryLighten
blendCategory BlendAdd = CategoryLighten
blendCategory BlendOverlay = CategoryContrast
blendCategory BlendSoftLight = CategoryContrast
blendCategory BlendHardLight = CategoryContrast
blendCategory BlendVividLight = CategoryContrast
blendCategory BlendLinearLight = CategoryContrast
blendCategory BlendPinLight = CategoryContrast
blendCategory BlendHardMix = CategoryContrast
blendCategory BlendDifference = CategoryInversion
blendCategory BlendExclusion = CategoryInversion
blendCategory BlendSubtract = CategoryInversion
blendCategory BlendDivide = CategoryInversion
blendCategory BlendHue = CategoryComponent
blendCategory BlendSaturation = CategoryComponent
blendCategory BlendColor = CategoryComponent
blendCategory BlendLuminosity = CategoryComponent
blendCategory BlendStencilAlpha = CategoryUtility
blendCategory BlendStencilLuma = CategoryUtility
blendCategory BlendSilhouetteAlpha = CategoryUtility
blendCategory BlendSilhouetteLuma = CategoryUtility
blendCategory BlendAlphaAdd = CategoryUtility
blendCategory BlendLuminescentPremul = CategoryUtility
blendCategory BlendPassThrough = CategoryUtility
blendCategory BlendBehind = CategoryUtility

-- | Default blend mode.
defaultBlendMode :: BlendMode
defaultBlendMode = BlendNormal

-- | Check if blend mode is pass-through (for groups).
isPassThrough :: BlendMode -> Boolean
isPassThrough BlendPassThrough = true
isPassThrough _ = false

-- | Check if blend mode affects transparency.
affectsTransparency :: BlendMode -> Boolean
affectsTransparency BlendStencilAlpha = true
affectsTransparency BlendStencilLuma = true
affectsTransparency BlendSilhouetteAlpha = true
affectsTransparency BlendSilhouetteLuma = true
affectsTransparency BlendAlphaAdd = true
affectsTransparency BlendBehind = true
affectsTransparency _ = false

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // composite operation
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Porter-Duff composite operations.
-- |
-- | These define how source and destination alpha combine.
-- | More fundamental than blend modes — blend modes operate on color,
-- | composite ops operate on coverage.
data CompositeOp
  = CompSourceOver      -- Default: source over destination
  | CompSourceIn        -- Source where destination is opaque
  | CompSourceOut       -- Source where destination is transparent
  | CompSourceAtop      -- Source over destination, only where dest is opaque
  | CompDestOver        -- Destination over source
  | CompDestIn          -- Destination where source is opaque
  | CompDestOut         -- Destination where source is transparent
  | CompDestAtop        -- Destination over source, only where source is opaque
  | CompClear           -- Clear both
  | CompCopy            -- Replace with source
  | CompXor             -- Source XOR destination
  | CompLighter         -- Sum of source and destination

derive instance eqCompositeOp :: Eq CompositeOp
derive instance ordCompositeOp :: Ord CompositeOp

instance showCompositeOp :: Show CompositeOp where
  show CompSourceOver = "source-over"
  show CompSourceIn = "source-in"
  show CompSourceOut = "source-out"
  show CompSourceAtop = "source-atop"
  show CompDestOver = "destination-over"
  show CompDestIn = "destination-in"
  show CompDestOut = "destination-out"
  show CompDestAtop = "destination-atop"
  show CompClear = "clear"
  show CompCopy = "copy"
  show CompXor = "xor"
  show CompLighter = "lighter"

-- | Default composite operation.
defaultCompositeOp :: CompositeOp
defaultCompositeOp = CompSourceOver

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if two blend modes are in the same category.
sameCategory :: BlendMode -> BlendMode -> Boolean
sameCategory a b = blendCategory a == blendCategory b

-- | Check if blend mode lightens the image.
isLighteningMode :: BlendMode -> Boolean
isLighteningMode mode = 
  blendCategory mode == CategoryLighten || mode == BlendColorDodge

-- | Check if blend mode darkens the image.
isDarkeningMode :: BlendMode -> Boolean
isDarkeningMode mode = 
  blendCategory mode == CategoryDarken || mode == BlendMultiply

-- | Get display label for blend mode.
blendModeLabel :: BlendMode -> String
blendModeLabel = show

-- | Get display label for composite operation.
compositeModeLabel :: CompositeOp -> String
compositeModeLabel = show
