-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // geometry // mask
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mask — Alpha mask for compositing.
-- |
-- | ## Purpose
-- |
-- | A Mask defines an alpha channel that controls visibility of content.
-- | Unlike ClipPath (which is binary — visible or not), masks support
-- | partial transparency through alpha values.
-- |
-- | ## Use Cases
-- |
-- | - **Gradient fades**: Fade content from opaque to transparent
-- | - **Soft edges**: Feathered transitions instead of hard clips
-- | - **Luminance masking**: Use brightness of an image as alpha
-- | - **Complex compositing**: Blend multiple layers with varying opacity
-- |
-- | ## Mask Sources
-- |
-- | - **Alpha**: Use alpha channel directly
-- | - **Luminance**: Convert brightness to alpha (black = transparent)
-- | - **InverseLuminance**: Invert luminance (white = transparent)
-- | - **Shape**: Geometric shape with optional feathering
-- | - **Gradient**: Linear/radial gradient as alpha
-- | - **Image**: External image as alpha source
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Path (shape masks)
-- | - Schema.Color.Opacity (alpha values)

module Hydrogen.Schema.Geometry.Mask
  ( -- * Mask Mode
    MaskMode(..)
  
  -- * Mask Source
  , MaskSource(..)
  
  -- * Mask
  , Mask(Mask)
  , mask
  , maskFromShape
  , maskFromGradient
  , maskFromLuminance
  
  -- * Accessors
  , source
  , mode
  , feather
  , invert
  
  -- * Transformations
  , withFeather
  , withInvert
  , withMode
  
  -- * Presets
  , maskNone
  , maskFull
  , maskHorizontalFade
  , maskVerticalFade
  , maskRadialFade
  , maskVignette
  
  -- * Queries
  , isFullyTransparent
  , isFullyOpaque
  , hasFeather
  , isInverted
  
  -- * Composition
  , MaskComposite(..)
  , composeMasks
  , intersectMasks
  , subtractMask
  , addMasks
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (>)
  , (==)
  , max
  )

import Hydrogen.Schema.Geometry.Path (Path)
import Hydrogen.Schema.Geometry.Path as Path

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // mask mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How the mask source is interpreted.
data MaskMode
  = AlphaMode           -- ^ Use alpha channel directly
  | LuminanceMode       -- ^ Convert brightness to alpha (black = 0, white = 1)
  | InverseLuminanceMode -- ^ Invert luminance (white = 0, black = 1)

derive instance eqMaskMode :: Eq MaskMode

instance showMaskMode :: Show MaskMode where
  show AlphaMode = "alpha"
  show LuminanceMode = "luminance"
  show InverseLuminanceMode = "inverse-luminance"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // mask source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source of mask alpha values.
data MaskSource
  = ShapeSource Path            -- ^ Shape defines the mask
  | LinearGradientSource        -- ^ Linear gradient (start to end)
      { angle :: Number         -- ^ Gradient angle in degrees
      , startOpacity :: Number  -- ^ Opacity at start (0.0-1.0)
      , endOpacity :: Number    -- ^ Opacity at end (0.0-1.0)
      }
  | RadialGradientSource        -- ^ Radial gradient (center outward)
      { centerX :: Number       -- ^ Center X (0.0-1.0 normalized)
      , centerY :: Number       -- ^ Center Y (0.0-1.0 normalized)
      , innerOpacity :: Number  -- ^ Opacity at center (0.0-1.0)
      , outerOpacity :: Number  -- ^ Opacity at edge (0.0-1.0)
      }
  | ImageSource String          -- ^ Image URL/ID as mask source
  | SolidSource Number          -- ^ Uniform opacity (0.0-1.0)

derive instance eqMaskSource :: Eq MaskSource

instance showMaskSource :: Show MaskSource where
  show (ShapeSource p) = "(ShapeSource " <> show (Path.commandCount p) <> " commands)"
  show (LinearGradientSource _) = "LinearGradientSource"
  show (RadialGradientSource _) = "RadialGradientSource"
  show (ImageSource url) = "(ImageSource " <> url <> ")"
  show (SolidSource o) = "(SolidSource " <> show o <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // mask
-- ═════════════════════════════════════════════════════════════════════════════

-- | Alpha mask for compositing.
-- |
-- | Defines how content visibility is modulated by an alpha source.
newtype Mask = Mask
  { source :: MaskSource     -- ^ Source of alpha values
  , mode :: MaskMode         -- ^ How to interpret the source
  , feather :: Number        -- ^ Edge feathering/blur in pixels (>= 0)
  , invert :: Boolean        -- ^ Invert the mask (swap opaque/transparent)
  }

derive instance eqMask :: Eq Mask

instance showMask :: Show Mask where
  show (Mask m) = 
    "(Mask " <> show m.source 
    <> " mode:" <> show m.mode
    <> " feather:" <> show m.feather <> "px"
    <> (if m.invert then " inverted" else "") <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a mask with explicit parameters
mask 
  :: { source :: MaskSource
     , mode :: MaskMode
     , feather :: Number
     , invert :: Boolean
     }
  -> Mask
mask cfg = Mask
  { source: cfg.source
  , mode: cfg.mode
  , feather: max 0.0 cfg.feather
  , invert: cfg.invert
  }

-- | Create a mask from a shape path
maskFromShape :: Path -> Mask
maskFromShape path = Mask
  { source: ShapeSource path
  , mode: AlphaMode
  , feather: 0.0
  , invert: false
  }

-- | Create a mask from a linear gradient
maskFromGradient 
  :: { angle :: Number
     , startOpacity :: Number
     , endOpacity :: Number
     }
  -> Mask
maskFromGradient cfg = Mask
  { source: LinearGradientSource cfg
  , mode: AlphaMode
  , feather: 0.0
  , invert: false
  }

-- | Create a mask from luminance (grayscale image)
maskFromLuminance :: String -> Mask
maskFromLuminance imageUrl = Mask
  { source: ImageSource imageUrl
  , mode: LuminanceMode
  , feather: 0.0
  , invert: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the mask source
source :: Mask -> MaskSource
source (Mask m) = m.source

-- | Get the mask mode
mode :: Mask -> MaskMode
mode (Mask m) = m.mode

-- | Get the feather amount in pixels
feather :: Mask -> Number
feather (Mask m) = m.feather

-- | Check if the mask is inverted
invert :: Mask -> Boolean
invert (Mask m) = m.invert

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set the feather amount
withFeather :: Number -> Mask -> Mask
withFeather f (Mask m) = Mask (m { feather = max 0.0 f })

-- | Set whether the mask is inverted
withInvert :: Boolean -> Mask -> Mask
withInvert i (Mask m) = Mask (m { invert = i })

-- | Set the mask mode
withMode :: MaskMode -> Mask -> Mask
withMode md (Mask m) = Mask (m { mode = md })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | No mask (fully transparent)
maskNone :: Mask
maskNone = Mask
  { source: SolidSource 0.0
  , mode: AlphaMode
  , feather: 0.0
  , invert: false
  }

-- | Full mask (fully opaque)
maskFull :: Mask
maskFull = Mask
  { source: SolidSource 1.0
  , mode: AlphaMode
  , feather: 0.0
  , invert: false
  }

-- | Horizontal fade (left to right)
maskHorizontalFade :: Mask
maskHorizontalFade = Mask
  { source: LinearGradientSource
      { angle: 90.0
      , startOpacity: 0.0
      , endOpacity: 1.0
      }
  , mode: AlphaMode
  , feather: 0.0
  , invert: false
  }

-- | Vertical fade (top to bottom)
maskVerticalFade :: Mask
maskVerticalFade = Mask
  { source: LinearGradientSource
      { angle: 180.0
      , startOpacity: 0.0
      , endOpacity: 1.0
      }
  , mode: AlphaMode
  , feather: 0.0
  , invert: false
  }

-- | Radial fade (center outward)
maskRadialFade :: Mask
maskRadialFade = Mask
  { source: RadialGradientSource
      { centerX: 0.5
      , centerY: 0.5
      , innerOpacity: 1.0
      , outerOpacity: 0.0
      }
  , mode: AlphaMode
  , feather: 0.0
  , invert: false
  }

-- | Vignette effect (dark edges)
maskVignette :: Mask
maskVignette = Mask
  { source: RadialGradientSource
      { centerX: 0.5
      , centerY: 0.5
      , innerOpacity: 1.0
      , outerOpacity: 0.3
      }
  , mode: AlphaMode
  , feather: 20.0
  , invert: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if the mask is fully transparent (no content visible)
isFullyTransparent :: Mask -> Boolean
isFullyTransparent (Mask m) = case m.source of
  SolidSource o -> if m.invert then o == 1.0 else o == 0.0
  _ -> false

-- | Check if the mask is fully opaque (all content visible)
isFullyOpaque :: Mask -> Boolean
isFullyOpaque (Mask m) = case m.source of
  SolidSource o -> if m.invert then o == 0.0 else o == 1.0
  _ -> false

-- | Check if the mask has feathering
hasFeather :: Mask -> Boolean
hasFeather (Mask m) = m.feather > 0.0

-- | Check if the mask is inverted
isInverted :: Mask -> Boolean
isInverted (Mask m) = m.invert

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mask composition operation.
-- |
-- | Represents how two masks combine. The runtime interprets this
-- | to produce the final alpha values.
data MaskComposite
  = MultiplyMasks Mask Mask    -- ^ Multiply alpha (both must be visible)
  | IntersectMasks Mask Mask   -- ^ Minimum alpha (intersection)
  | SubtractMasks Mask Mask    -- ^ First minus second
  | AddMasks Mask Mask         -- ^ Add alpha (union, clamped to 1.0)

derive instance eqMaskComposite :: Eq MaskComposite

instance showMaskComposite :: Show MaskComposite where
  show (MultiplyMasks _ _) = "MultiplyMasks"
  show (IntersectMasks _ _) = "IntersectMasks"
  show (SubtractMasks _ _) = "SubtractMasks"
  show (AddMasks _ _) = "AddMasks"

-- | Compose two masks (multiply alpha values)
-- |
-- | Result: areas visible in BOTH masks remain visible.
-- | Runtime interprets this as alpha multiplication.
composeMasks :: Mask -> Mask -> MaskComposite
composeMasks = MultiplyMasks

-- | Intersect two masks (minimum alpha)
-- |
-- | Result: only areas visible in BOTH masks.
intersectMasks :: Mask -> Mask -> MaskComposite
intersectMasks = IntersectMasks

-- | Subtract one mask from another
-- |
-- | Result: areas visible in first mask but NOT in second.
subtractMask :: Mask -> Mask -> MaskComposite
subtractMask = SubtractMasks

-- | Add two masks (union)
-- |
-- | Result: areas visible in EITHER mask (clamped to 1.0).
addMasks :: Mask -> Mask -> MaskComposite
addMasks = AddMasks
