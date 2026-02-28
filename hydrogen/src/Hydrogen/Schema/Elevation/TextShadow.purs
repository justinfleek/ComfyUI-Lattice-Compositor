-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // elevation // text-shadow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TextShadow molecule — shadow effect for text elements.
-- |
-- | ## CSS text-shadow
-- |
-- | Unlike box-shadow, text-shadow:
-- | - Has NO spread radius
-- | - Has NO inset option
-- | - Follows the glyph contours precisely
-- | - Can be layered (comma-separated)
-- |
-- | Format: `text-shadow: <offset-x> <offset-y> <blur-radius> <color>;`
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Elevation.TextShadow as TS
-- | import Hydrogen.Schema.Color.RGB as RGB
-- |
-- | -- Create a text shadow
-- | glow :: TS.TextShadow
-- | glow = TS.textShadow
-- |   { offsetX: 0.0
-- |   , offsetY: 0.0
-- |   , blur: 10.0
-- |   , color: RGB.rgba 59 130 246 80  -- blue glow
-- |   }
-- |
-- | -- Layered shadows for 3D effect
-- | embossed :: TS.LayeredTextShadow
-- | embossed = TS.layeredText
-- |   [ TS.textShadow { offsetX: 1.0, offsetY: 1.0, blur: 0.0
-- |                   , color: RGB.rgba 255 255 255 50 }  -- highlight
-- |   , TS.textShadow { offsetX: -1.0, offsetY: -1.0, blur: 0.0
-- |                   , color: RGB.rgba 0 0 0 30 }  -- shadow
-- |   ]
-- |
-- | -- Convert to CSS
-- | css = TS.toLegacyCss glow  -- "0px 0px 10px rgba(59, 130, 246, 0.8)"
-- | ```

module Hydrogen.Schema.Elevation.TextShadow
  ( -- * Core Types
    TextShadow
  , LayeredTextShadow(..)
  
  -- * Constructors
  , textShadow
  , noTextShadow
  , layeredText
  
  -- * Accessors
  , getOffsetX
  , getOffsetY
  , getBlur
  , getColor
  , getLayers
  
  -- * Operations
  , withOffset
  , withBlur
  , withColor
  , addTextLayer
  , scaleTextShadow
  
  -- * Common Effects
  , dropShadowText
  , glowText
  , outlineText
  , embossedText
  , letterpress
  
  -- * Conversion (Legacy CSS, not FFI)
  , toLegacyCss
  , layeredToLegacyCss
  
  -- * Predicates
  , hasTextShadow
  , isGlowEffect
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , map
  , not
  , negate
  , (<>)
  , (==)
  , (*)
  , (<)
  , (>)
  , (&&)
  )

import Data.Array (null)
import Data.Array as Array
import Data.Int as Int
import Data.String (joinWith)
import Hydrogen.Schema.Color.RGB as RGB

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // core types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text shadow — parameters for CSS text-shadow.
-- |
-- | All measurements in CSS pixels.
type TextShadow =
  { offsetX :: Number    -- ^ Horizontal offset (px)
  , offsetY :: Number    -- ^ Vertical offset (px)
  , blur :: Number       -- ^ Blur radius (px), >= 0
  , color :: RGB.RGBA    -- ^ Shadow color with alpha
  }

-- | Multiple text shadows layered together.
-- |
-- | Text shadows are rendered in order: first in array is painted first.
newtype LayeredTextShadow = LayeredTextShadow (Array TextShadow)

derive instance eqLayeredTextShadow :: Eq LayeredTextShadow

instance showLayeredTextShadow :: Show LayeredTextShadow where
  show = layeredToLegacyCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a text shadow
-- |
-- | Blur is clamped to >= 0.
textShadow ::
  { offsetX :: Number
  , offsetY :: Number
  , blur :: Number
  , color :: RGB.RGBA
  } -> TextShadow
textShadow params =
  { offsetX: params.offsetX
  , offsetY: params.offsetY
  , blur: clampPositive params.blur
  , color: params.color
  }

-- | No text shadow (empty layers)
noTextShadow :: LayeredTextShadow
noTextShadow = LayeredTextShadow []

-- | Create layered text shadow from array
layeredText :: Array TextShadow -> LayeredTextShadow
layeredText = LayeredTextShadow

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get horizontal offset
getOffsetX :: TextShadow -> Number
getOffsetX s = s.offsetX

-- | Get vertical offset
getOffsetY :: TextShadow -> Number
getOffsetY s = s.offsetY

-- | Get blur radius
getBlur :: TextShadow -> Number
getBlur s = s.blur

-- | Get shadow color
getColor :: TextShadow -> RGB.RGBA
getColor s = s.color

-- | Get all layers from layered text shadow
getLayers :: LayeredTextShadow -> Array TextShadow
getLayers (LayeredTextShadow ls) = ls

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update shadow offset
withOffset :: Number -> Number -> TextShadow -> TextShadow
withOffset x y s = s { offsetX = x, offsetY = y }

-- | Update blur radius
withBlur :: Number -> TextShadow -> TextShadow
withBlur b s = s { blur = clampPositive b }

-- | Update shadow color
withColor :: RGB.RGBA -> TextShadow -> TextShadow
withColor c s = s { color = c }

-- | Add a layer to layered text shadow
addTextLayer :: TextShadow -> LayeredTextShadow -> LayeredTextShadow
addTextLayer shadow (LayeredTextShadow ls) = LayeredTextShadow (Array.snoc ls shadow)

-- | Scale all text shadow dimensions by a factor
scaleTextShadow :: Number -> TextShadow -> TextShadow
scaleTextShadow factor s = s
  { offsetX = s.offsetX * factor
  , offsetY = s.offsetY * factor
  , blur = clampPositive (s.blur * factor)
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drop shadow effect — standard offset shadow
-- |
-- | Creates a shadow below and to the right, simulating light from upper-left.
dropShadowText :: RGB.RGBA -> TextShadow
dropShadowText c = textShadow
  { offsetX: 1.0
  , offsetY: 1.0
  , blur: 2.0
  , color: c
  }

-- | Glow effect — no offset, just blur
-- |
-- | Creates a halo around text. Common for neon effects, highlights.
glowText :: RGB.RGBA -> Number -> TextShadow
glowText c blurRadius = textShadow
  { offsetX: 0.0
  , offsetY: 0.0
  , blur: blurRadius
  , color: c
  }

-- | Outline effect — multiple shadows at cardinal directions
-- |
-- | Creates a pseudo-outline around text using 4 shadows.
outlineText :: RGB.RGBA -> LayeredTextShadow
outlineText c = layeredText
  [ textShadow { offsetX: 1.0, offsetY: 0.0, blur: 0.0, color: c }
  , textShadow { offsetX: -1.0, offsetY: 0.0, blur: 0.0, color: c }
  , textShadow { offsetX: 0.0, offsetY: 1.0, blur: 0.0, color: c }
  , textShadow { offsetX: 0.0, offsetY: -1.0, blur: 0.0, color: c }
  ]

-- | Embossed effect — highlight above, shadow below
-- |
-- | Creates a raised, 3D appearance.
embossedText :: { highlight :: RGB.RGBA, shadow :: RGB.RGBA } -> LayeredTextShadow
embossedText colors = layeredText
  [ textShadow { offsetX: 1.0, offsetY: 1.0, blur: 0.0, color: colors.shadow }
  , textShadow { offsetX: -1.0, offsetY: -1.0, blur: 0.0, color: colors.highlight }
  ]

-- | Letterpress effect — inset appearance
-- |
-- | Creates a pressed-in appearance with highlight above shadow below.
letterpress :: { highlight :: RGB.RGBA, shadow :: RGB.RGBA } -> LayeredTextShadow
letterpress colors = layeredText
  [ textShadow { offsetX: 0.0, offsetY: -1.0, blur: 0.0, color: colors.shadow }
  , textShadow { offsetX: 0.0, offsetY: 1.0, blur: 0.0, color: colors.highlight }
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert text shadow to CSS string.
-- |
-- | Format: "<offset-x> <offset-y> <blur-radius> <color>"
-- | NOT an FFI boundary — pure string generation.
toLegacyCss :: TextShadow -> String
toLegacyCss s =
  showPx s.offsetX <> " " <> showPx s.offsetY <> " " 
    <> showPx s.blur <> " " <> RGB.toLegacyCssA s.color

-- | Convert layered text shadow to CSS string.
-- |
-- | Returns "none" if empty, otherwise comma-separated shadows.
-- | NOT an FFI boundary — pure string generation.
layeredToLegacyCss :: LayeredTextShadow -> String
layeredToLegacyCss (LayeredTextShadow ls) =
  if null ls
    then "none"
    else joinWith ", " (map toLegacyCss ls)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if layered text shadow has any layers
hasTextShadow :: LayeredTextShadow -> Boolean
hasTextShadow (LayeredTextShadow ls) = not (null ls)

-- | Check if shadow is a glow effect (no offset)
isGlowEffect :: TextShadow -> Boolean
isGlowEffect s = s.offsetX == 0.0 && s.offsetY == 0.0 && s.blur > 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to non-negative
clampPositive :: Number -> Number
clampPositive n = if n < 0.0 then 0.0 else n

-- | Show number as CSS pixel value
showPx :: Number -> String
showPx n = showNumber n <> "px"

-- | Show number cleanly
showNumber :: Number -> String
showNumber n =
  let rounded = Int.round n
  in if Int.toNumber rounded == n
    then show rounded
    else show n
