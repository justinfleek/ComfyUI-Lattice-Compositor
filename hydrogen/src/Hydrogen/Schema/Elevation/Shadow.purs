-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // elevation // shadow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Shadow atoms — typed parameters for CSS box-shadow and drop-shadow.
-- |
-- | ## Physical Model
-- |
-- | Shadows simulate light occlusion. The parameters model:
-- |
-- | - **Offset (X, Y)**: Direction of the light source. Positive Y = light from above.
-- | - **Blur radius**: Gaussian blur sigma. Larger = softer, more diffuse shadow.
-- | - **Spread radius**: Expand or contract the shadow shape before blurring.
-- | - **Color**: Shadow color with alpha for intensity.
-- | - **Inset**: Inner shadow (inset) vs outer shadow (default).
-- |
-- | ## CSS Mapping
-- |
-- | ```css
-- | box-shadow: <offset-x> <offset-y> <blur-radius> <spread-radius> <color> [inset];
-- | filter: drop-shadow(<offset-x> <offset-y> <blur-radius> <color>);
-- | ```
-- |
-- | Note: `drop-shadow` does not support spread radius or inset.
-- |
-- | ## Concrete Values, Not Semantics
-- |
-- | This module provides **concrete typed parameters**, not semantic tokens
-- | like "sm", "md", "lg". The visual size of a shadow depends on:
-- |
-- | - The element's size
-- | - The viewing distance
-- | - The display's PPI
-- | - The surrounding context
-- |
-- | A "16px blur shadow" on a button is very different from the same shadow
-- | on a modal dialog. Semantic scales belong in BrandSchema, not atoms.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Elevation.Shadow as Shadow
-- | import Hydrogen.Schema.Color as Color
-- |
-- | -- Create a shadow with explicit parameters
-- | cardShadow :: Shadow.BoxShadow
-- | cardShadow = Shadow.boxShadow
-- |   { offsetX: 0.0
-- |   , offsetY: 4.0
-- |   , blur: 6.0
-- |   , spread: -1.0
-- |   , color: Color.rgba 0 0 0 0.1
-- |   , inset: false
-- |   }
-- |
-- | -- Convert to CSS
-- | css = Shadow.toLegacyCss cardShadow
-- | -- "0px 4px 6px -1px rgba(0, 0, 0, 0.1)"
-- |
-- | -- Layered shadows for depth
-- | elevatedShadow :: Shadow.LayeredShadow
-- | elevatedShadow = Shadow.layered
-- |   [ Shadow.boxShadow { offsetX: 0.0, offsetY: 1.0, blur: 3.0, spread: 0.0
-- |                      , color: Color.rgba 0 0 0 0.1, inset: false }
-- |   , Shadow.boxShadow { offsetX: 0.0, offsetY: 4.0, blur: 6.0, spread: -1.0
-- |                      , color: Color.rgba 0 0 0 0.1, inset: false }
-- |   ]
-- | ```

module Hydrogen.Schema.Elevation.Shadow
  ( -- * Core Types
    BoxShadow
  , DropShadow
  , LayeredShadow
  , ShadowOffset
  
  -- * Constructors
  , boxShadow
  , dropShadow
  , insetShadow
  , layered
  , noShadow
  
  -- * Accessors
  , offsetX
  , offsetY
  , blur
  , spread
  , color
  , isInset
  , layers
  
  -- * Operations
  , withOffset
  , withBlur
  , withSpread
  , withColor
  , withInset
  , addLayer
  , scaleBlur
  , scaleShadow
  
  -- * Conversion (Legacy string generation, NOT FFI)
  , toLegacyCss
  , dropShadowToLegacyCss
  , layeredToLegacyCss
  
  -- * Predicates
  , isNoShadow
  , hasInset
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , not
  , (<>)
  , (==)
  , (*)
  , ($)
  , (<)
  )

import Data.Array (filter, null)
import Data.Array as Array
import Data.Int as Int
import Data.String (joinWith)
import Hydrogen.Schema.Color.RGB as RGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow offset in pixels
-- |
-- | Represents the displacement of the shadow from the element.
-- | Positive X = shadow to the right (light from left)
-- | Positive Y = shadow below (light from above)
type ShadowOffset =
  { x :: Number  -- ^ Horizontal offset in pixels
  , y :: Number  -- ^ Vertical offset in pixels
  }

-- | Box shadow — full CSS box-shadow parameters
-- |
-- | All measurements are in CSS pixels. For physical accuracy, convert
-- | using DisplayContext before setting these values.
type BoxShadow =
  { offsetX :: Number    -- ^ Horizontal offset (px)
  , offsetY :: Number    -- ^ Vertical offset (px)
  , blur :: Number       -- ^ Blur radius (px), >= 0
  , spread :: Number     -- ^ Spread radius (px), can be negative
  , color :: RGB.RGBA    -- ^ Shadow color with alpha
  , inset :: Boolean     -- ^ True for inner shadow
  }

-- | Drop shadow — CSS filter drop-shadow parameters
-- |
-- | Simpler than box-shadow: no spread, no inset.
-- | Follows the alpha channel of the element's shape.
type DropShadow =
  { offsetX :: Number    -- ^ Horizontal offset (px)
  , offsetY :: Number    -- ^ Vertical offset (px)
  , blur :: Number       -- ^ Blur radius (px), >= 0
  , color :: RGB.RGBA    -- ^ Shadow color with alpha
  }

-- | Multiple shadows layered together
-- |
-- | CSS allows comma-separated shadows. This represents that list.
-- | Shadows are rendered in order: first in array is painted first (bottommost).
newtype LayeredShadow = LayeredShadow (Array BoxShadow)

derive instance eqLayeredShadow :: Eq LayeredShadow

instance showLayeredShadow :: Show LayeredShadow where
  show = layeredToLegacyCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a box shadow
-- |
-- | Blur is clamped to >= 0 (negative blur is undefined).
boxShadow :: 
  { offsetX :: Number
  , offsetY :: Number
  , blur :: Number
  , spread :: Number
  , color :: RGB.RGBA
  , inset :: Boolean
  } -> BoxShadow
boxShadow params =
  { offsetX: params.offsetX
  , offsetY: params.offsetY
  , blur: clampPositive params.blur
  , spread: params.spread
  , color: params.color
  , inset: params.inset
  }

-- | Create a drop shadow (for CSS filter)
-- |
-- | Blur is clamped to >= 0.
dropShadow ::
  { offsetX :: Number
  , offsetY :: Number
  , blur :: Number
  , color :: RGB.RGBA
  } -> DropShadow
dropShadow params =
  { offsetX: params.offsetX
  , offsetY: params.offsetY
  , blur: clampPositive params.blur
  , color: params.color
  }

-- | Create an inset (inner) shadow
-- |
-- | Convenience constructor that sets inset = true.
insetShadow ::
  { offsetX :: Number
  , offsetY :: Number
  , blur :: Number
  , spread :: Number
  , color :: RGB.RGBA
  } -> BoxShadow
insetShadow params = boxShadow
  { offsetX: params.offsetX
  , offsetY: params.offsetY
  , blur: params.blur
  , spread: params.spread
  , color: params.color
  , inset: true
  }

-- | Create a layered shadow from multiple box shadows
layered :: Array BoxShadow -> LayeredShadow
layered = LayeredShadow

-- | No shadow (empty)
-- |
-- | Renders as "none" in CSS.
noShadow :: LayeredShadow
noShadow = LayeredShadow []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get horizontal offset
offsetX :: BoxShadow -> Number
offsetX s = s.offsetX

-- | Get vertical offset
offsetY :: BoxShadow -> Number
offsetY s = s.offsetY

-- | Get blur radius
blur :: BoxShadow -> Number
blur s = s.blur

-- | Get spread radius
spread :: BoxShadow -> Number
spread s = s.spread

-- | Get shadow color
color :: BoxShadow -> RGB.RGBA
color s = s.color

-- | Check if shadow is inset
isInset :: BoxShadow -> Boolean
isInset s = s.inset

-- | Get all layers from a layered shadow
layers :: LayeredShadow -> Array BoxShadow
layers (LayeredShadow ls) = ls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update shadow offset
withOffset :: Number -> Number -> BoxShadow -> BoxShadow
withOffset x y s = s { offsetX = x, offsetY = y }

-- | Update blur radius
withBlur :: Number -> BoxShadow -> BoxShadow
withBlur b s = s { blur = clampPositive b }

-- | Update spread radius
withSpread :: Number -> BoxShadow -> BoxShadow
withSpread sp s = s { spread = sp }

-- | Update shadow color
withColor :: RGB.RGBA -> BoxShadow -> BoxShadow
withColor c s = s { color = c }

-- | Set inset flag
withInset :: Boolean -> BoxShadow -> BoxShadow
withInset i s = s { inset = i }

-- | Add a layer to a layered shadow
addLayer :: BoxShadow -> LayeredShadow -> LayeredShadow
addLayer shadow (LayeredShadow ls) = LayeredShadow (Array.snoc ls shadow)

-- | Scale the blur radius by a factor
scaleBlur :: Number -> BoxShadow -> BoxShadow
scaleBlur factor s = s { blur = clampPositive (s.blur * factor) }

-- | Scale all shadow dimensions (offset, blur, spread) by a factor
-- |
-- | Useful for responsive scaling.
scaleShadow :: Number -> BoxShadow -> BoxShadow
scaleShadow factor s = s
  { offsetX = s.offsetX * factor
  , offsetY = s.offsetY * factor
  , blur = clampPositive (s.blur * factor)
  , spread = s.spread * factor
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert box shadow to legacy CSS string.
-- |
-- | Format: "[inset] <offset-x> <offset-y> <blur> <spread> <color>"
-- | NOT an FFI boundary - pure string generation.
toLegacyCss :: BoxShadow -> String
toLegacyCss s =
  let
    insetStr = if s.inset then "inset " else ""
    offsetXStr = showPx s.offsetX
    offsetYStr = showPx s.offsetY
    blurStr = showPx s.blur
    spreadStr = showPx s.spread
    colorStr = RGB.toLegacyCssA s.color
  in
    insetStr <> offsetXStr <> " " <> offsetYStr <> " " <> blurStr <> " " <> spreadStr <> " " <> colorStr

-- | Convert drop shadow to legacy CSS filter string.
-- |
-- | Format: "drop-shadow(<offset-x> <offset-y> <blur> <color>)"
-- | NOT an FFI boundary - pure string generation.
dropShadowToLegacyCss :: DropShadow -> String
dropShadowToLegacyCss s =
  "drop-shadow(" <> showPx s.offsetX <> " " <> showPx s.offsetY <> " " 
    <> showPx s.blur <> " " <> RGB.toLegacyCssA s.color <> ")"

-- | Convert layered shadow to legacy CSS string.
-- |
-- | Multiple shadows are comma-separated.
-- | Returns "none" if no layers.
-- | NOT an FFI boundary - pure string generation.
layeredToLegacyCss :: LayeredShadow -> String
layeredToLegacyCss (LayeredShadow ls) =
  if null ls
    then "none"
    else joinWith ", " (map toLegacyCss ls)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a layered shadow is empty (no shadow)
isNoShadow :: LayeredShadow -> Boolean
isNoShadow (LayeredShadow ls) = null ls

-- | Check if any layer is an inset shadow
hasInset :: LayeredShadow -> Boolean
hasInset (LayeredShadow ls) = 
  not $ null $ filter (\s -> s.inset) ls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to non-negative
clampPositive :: Number -> Number
clampPositive n = if n < 0.0 then 0.0 else n

-- | Show number as CSS pixel value
showPx :: Number -> String
showPx n = showNumber n <> "px"

-- | Show number cleanly (no trailing .0 for integers)
showNumber :: Number -> String
showNumber n =
  let rounded = Int.round n
  in if Int.toNumber rounded == n
    then show rounded
    else show n
