-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // style // token
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Design tokens as types
-- |
-- | This module provides type-safe design tokens for:
-- | - Spacing (padding, margin, gap)
-- | - Border radius
-- | - Shadows
-- | - Z-index layers
-- |
-- | All tokens map to Tailwind CSS classes for zero-runtime styling.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Style.Token as Token
-- |
-- | -- Type-safe spacing
-- | padding Token.P4        -- "p-4"
-- | margin Token.M2         -- "m-2"
-- | gap Token.Gap4          -- "gap-4"
-- |
-- | -- Border radius
-- | radius Token.RoundedLg  -- "rounded-lg"
-- |
-- | -- Shadows
-- | shadow Token.ShadowMd   -- "shadow-md"
-- | ```
module Hydrogen.Style.Token
  ( -- * Spacing
    Spacing(..)
  , spacing
  , spacingPx
    -- * Padding
  , Padding(..)
  , padding
  , paddingX
  , paddingY
  , paddingT
  , paddingB
  , paddingL
  , paddingR
    -- * Margin
  , Margin(..)
  , margin
  , marginX
  , marginY
  , marginT
  , marginB
  , marginL
  , marginR
    -- * Gap
  , Gap(..)
  , gap
  , gapX
  , gapY
    -- * Border Radius
  , Radius(..)
  , radius
    -- * Shadow
  , Shadow(..)
  , shadow
    -- * Z-Index
  , ZIndex(..)
  , zIndex
    -- * Size
  , Size(..)
  , width
  , height
  , size
  , minWidth
  , maxWidth
  , minHeight
  , maxHeight
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spacing scale (maps to Tailwind's spacing scale)
-- |
-- | Each step is 0.25rem (4px at default font size)
data Spacing
  = S0      -- 0px
  | S0_5    -- 2px
  | S1      -- 4px
  | S1_5    -- 6px
  | S2      -- 8px
  | S2_5    -- 10px
  | S3      -- 12px
  | S3_5    -- 14px
  | S4      -- 16px
  | S5      -- 20px
  | S6      -- 24px
  | S7      -- 28px
  | S8      -- 32px
  | S9      -- 36px
  | S10     -- 40px
  | S11     -- 44px
  | S12     -- 48px
  | S14     -- 56px
  | S16     -- 64px
  | S20     -- 80px
  | S24     -- 96px
  | S28     -- 112px
  | S32     -- 128px
  | S36     -- 144px
  | S40     -- 160px
  | S44     -- 176px
  | S48     -- 192px
  | S52     -- 208px
  | S56     -- 224px
  | S60     -- 240px
  | S64     -- 256px
  | S72     -- 288px
  | S80     -- 320px
  | S96     -- 384px
  | SAuto   -- auto

derive instance eqSpacing :: Eq Spacing
derive instance ordSpacing :: Ord Spacing

-- | Convert spacing to Tailwind class suffix
spacing :: Spacing -> String
spacing = case _ of
  S0 -> "0"
  S0_5 -> "0.5"
  S1 -> "1"
  S1_5 -> "1.5"
  S2 -> "2"
  S2_5 -> "2.5"
  S3 -> "3"
  S3_5 -> "3.5"
  S4 -> "4"
  S5 -> "5"
  S6 -> "6"
  S7 -> "7"
  S8 -> "8"
  S9 -> "9"
  S10 -> "10"
  S11 -> "11"
  S12 -> "12"
  S14 -> "14"
  S16 -> "16"
  S20 -> "20"
  S24 -> "24"
  S28 -> "28"
  S32 -> "32"
  S36 -> "36"
  S40 -> "40"
  S44 -> "44"
  S48 -> "48"
  S52 -> "52"
  S56 -> "56"
  S60 -> "60"
  S64 -> "64"
  S72 -> "72"
  S80 -> "80"
  S96 -> "96"
  SAuto -> "auto"

-- | Get spacing in pixels (at 16px base)
spacingPx :: Spacing -> Int
spacingPx = case _ of
  S0 -> 0
  S0_5 -> 2
  S1 -> 4
  S1_5 -> 6
  S2 -> 8
  S2_5 -> 10
  S3 -> 12
  S3_5 -> 14
  S4 -> 16
  S5 -> 20
  S6 -> 24
  S7 -> 28
  S8 -> 32
  S9 -> 36
  S10 -> 40
  S11 -> 44
  S12 -> 48
  S14 -> 56
  S16 -> 64
  S20 -> 80
  S24 -> 96
  S28 -> 112
  S32 -> 128
  S36 -> 144
  S40 -> 160
  S44 -> 176
  S48 -> 192
  S52 -> 208
  S56 -> 224
  S60 -> 240
  S64 -> 256
  S72 -> 288
  S80 -> 320
  S96 -> 384
  SAuto -> 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // padding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Padding values
newtype Padding = Padding Spacing

derive instance eqPadding :: Eq Padding
derive newtype instance ordPadding :: Ord Padding

-- | All sides padding
padding :: Spacing -> String
padding s = "p-" <> spacing s

-- | Horizontal padding (left and right)
paddingX :: Spacing -> String
paddingX s = "px-" <> spacing s

-- | Vertical padding (top and bottom)
paddingY :: Spacing -> String
paddingY s = "py-" <> spacing s

-- | Top padding
paddingT :: Spacing -> String
paddingT s = "pt-" <> spacing s

-- | Bottom padding
paddingB :: Spacing -> String
paddingB s = "pb-" <> spacing s

-- | Left padding
paddingL :: Spacing -> String
paddingL s = "pl-" <> spacing s

-- | Right padding
paddingR :: Spacing -> String
paddingR s = "pr-" <> spacing s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // margin
-- ═════════════════════════════════════════════════════════════════════════════

-- | Margin values
newtype Margin = Margin Spacing

derive instance eqMargin :: Eq Margin
derive newtype instance ordMargin :: Ord Margin

-- | All sides margin
margin :: Spacing -> String
margin s = "m-" <> spacing s

-- | Horizontal margin (left and right)
marginX :: Spacing -> String
marginX s = "mx-" <> spacing s

-- | Vertical margin (top and bottom)
marginY :: Spacing -> String
marginY s = "my-" <> spacing s

-- | Top margin
marginT :: Spacing -> String
marginT s = "mt-" <> spacing s

-- | Bottom margin
marginB :: Spacing -> String
marginB s = "mb-" <> spacing s

-- | Left margin
marginL :: Spacing -> String
marginL s = "ml-" <> spacing s

-- | Right margin
marginR :: Spacing -> String
marginR s = "mr-" <> spacing s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // gap
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gap values (for flex/grid)
newtype Gap = Gap Spacing

derive instance eqGap :: Eq Gap
derive newtype instance ordGap :: Ord Gap

-- | Gap (both directions)
gap :: Spacing -> String
gap s = "gap-" <> spacing s

-- | Horizontal gap
gapX :: Spacing -> String
gapX s = "gap-x-" <> spacing s

-- | Vertical gap
gapY :: Spacing -> String
gapY s = "gap-y-" <> spacing s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // border radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border radius scale
data Radius
  = RoundedNone   -- 0px
  | RoundedSm     -- 2px
  | Rounded       -- 4px
  | RoundedMd     -- 6px
  | RoundedLg     -- 8px
  | RoundedXl     -- 12px
  | Rounded2xl    -- 16px
  | Rounded3xl    -- 24px
  | RoundedFull   -- 9999px (pill)

derive instance eqRadius :: Eq Radius
derive instance ordRadius :: Ord Radius

-- | Convert radius to Tailwind class
radius :: Radius -> String
radius = case _ of
  RoundedNone -> "rounded-none"
  RoundedSm -> "rounded-sm"
  Rounded -> "rounded"
  RoundedMd -> "rounded-md"
  RoundedLg -> "rounded-lg"
  RoundedXl -> "rounded-xl"
  Rounded2xl -> "rounded-2xl"
  Rounded3xl -> "rounded-3xl"
  RoundedFull -> "rounded-full"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // shadow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shadow scale
data Shadow
  = ShadowNone
  | ShadowSm
  | Shadow
  | ShadowMd
  | ShadowLg
  | ShadowXl
  | Shadow2xl
  | ShadowInner

derive instance eqShadow :: Eq Shadow
derive instance ordShadow :: Ord Shadow

-- | Convert shadow to Tailwind class
shadow :: Shadow -> String
shadow = case _ of
  ShadowNone -> "shadow-none"
  ShadowSm -> "shadow-sm"
  Shadow -> "shadow"
  ShadowMd -> "shadow-md"
  ShadowLg -> "shadow-lg"
  ShadowXl -> "shadow-xl"
  Shadow2xl -> "shadow-2xl"
  ShadowInner -> "shadow-inner"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // z-index
-- ═════════════════════════════════════════════════════════════════════════════

-- | Z-index layers
data ZIndex
  = Z0
  | Z10
  | Z20
  | Z30
  | Z40
  | Z50
  | ZAuto

derive instance eqZIndex :: Eq ZIndex
derive instance ordZIndex :: Ord ZIndex

-- | Convert z-index to Tailwind class
zIndex :: ZIndex -> String
zIndex = case _ of
  Z0 -> "z-0"
  Z10 -> "z-10"
  Z20 -> "z-20"
  Z30 -> "z-30"
  Z40 -> "z-40"
  Z50 -> "z-50"
  ZAuto -> "z-auto"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // size
-- ═════════════════════════════════════════════════════════════════════════════

-- | Size values (for width/height)
data Size
  = SizeSpacing Spacing  -- Use spacing scale
  | SizeFull             -- 100%
  | SizeScreen           -- 100vw/100vh
  | SizeMin              -- min-content
  | SizeMax              -- max-content
  | SizeFit              -- fit-content
  | SizeAuto             -- auto
  | SizeFraction Int Int -- fraction (e.g., 1/2, 2/3)
  | SizePx Int           -- arbitrary pixel value

derive instance eqSize :: Eq Size

-- | Width class
width :: Size -> String
width = sizeClass "w"

-- | Height class
height :: Size -> String
height = sizeClass "h"

-- | Both width and height (square)
size :: Size -> String
size s = width s <> " " <> height s

-- | Min-width class
minWidth :: Size -> String
minWidth = sizeClass "min-w"

-- | Max-width class
maxWidth :: Size -> String
maxWidth = sizeClass "max-w"

-- | Min-height class
minHeight :: Size -> String
minHeight = sizeClass "min-h"

-- | Max-height class
maxHeight :: Size -> String
maxHeight = sizeClass "max-h"

sizeClass :: String -> Size -> String
sizeClass prefix = case _ of
  SizeSpacing s -> prefix <> "-" <> spacing s
  SizeFull -> prefix <> "-full"
  SizeScreen -> prefix <> "-screen"
  SizeMin -> prefix <> "-min"
  SizeMax -> prefix <> "-max"
  SizeFit -> prefix <> "-fit"
  SizeAuto -> prefix <> "-auto"
  SizeFraction n d -> prefix <> "-" <> show n <> "/" <> show d
  SizePx px -> prefix <> "-[" <> show px <> "px]"
