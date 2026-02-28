-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // component // card // badge
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Badge — Overlay badges, tags, and labels for cards.
-- |
-- | ## Design Philosophy
-- |
-- | Badges are positioned overlays that communicate status, price, category,
-- | or other metadata. They can be placed at corners or edges.
-- |
-- | ## Badge Types
-- |
-- | - **Status**: "NEW", "SALE", "SOLD OUT", "HOT"
-- | - **Price**: "$19.99", "From $5"
-- | - **Rating**: "4.5 ★"
-- | - **Category**: "Electronics", "Fashion"
-- | - **Custom**: Any text/icon combination
-- |
-- | ## Use Cases
-- |
-- | - E-commerce product cards (price, sale badge)
-- | - Etsy/Amazon-style UGC cards
-- | - Article cards (category tag)
-- | - Profile cards (online status)
-- |
-- | ## Dependencies
-- |
-- | - Schema.Color.RGB (badge colors)
-- | - Schema.Typography (text styling)

module Hydrogen.Element.Compound.Card.Badge
  ( -- * Badge Position
    BadgePosition
      ( BadgeTopLeft
      , BadgeTopRight
      , BadgeBottomLeft
      , BadgeBottomRight
      , BadgeTopCenter
      , BadgeBottomCenter
      )
  
  -- * Badge Variant
  , BadgeVariant
      ( BadgeStatus
      , BadgePrice
      , BadgeRating
      , BadgeCategory
      , BadgeCustom
      )
  
  -- * Badge Style
  , BadgeStyle
      ( StyleSolid
      , StyleOutline
      , StyleGlass
      , StyleGradient
      )
  
  -- * Icon Position
  , IconPosition
      ( IconBefore
      , IconAfter
      , IconOnly
      )
  
  -- * Badge Config
  , BadgeConfig(..)
  , badgeConfig
  , defaultBadgeConfig
  
  -- * Status Presets
  , newBadge
  , saleBadge
  , soldOutBadge
  , hotBadge
  
  -- * Content Presets
  , priceBadge
  , priceBadgeWith
  , ratingBadge
  , ratingBadgeWith
  , categoryBadge
  , textBadge
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // badge position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of badge on the card
data BadgePosition
  = BadgeTopLeft
  | BadgeTopRight
  | BadgeBottomLeft
  | BadgeBottomRight
  | BadgeTopCenter
  | BadgeBottomCenter

derive instance eqBadgePosition :: Eq BadgePosition
derive instance ordBadgePosition :: Ord BadgePosition

instance showBadgePosition :: Show BadgePosition where
  show BadgeTopLeft = "top-left"
  show BadgeTopRight = "top-right"
  show BadgeBottomLeft = "bottom-left"
  show BadgeBottomRight = "bottom-right"
  show BadgeTopCenter = "top-center"
  show BadgeBottomCenter = "bottom-center"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // badge variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic badge type
data BadgeVariant
  = BadgeStatus       -- ^ Status indicator (NEW, SALE, etc.)
  | BadgePrice        -- ^ Price display
  | BadgeRating       -- ^ Rating display (stars)
  | BadgeCategory     -- ^ Category/tag
  | BadgeCustom       -- ^ Custom content

derive instance eqBadgeVariant :: Eq BadgeVariant
derive instance ordBadgeVariant :: Ord BadgeVariant

instance showBadgeVariant :: Show BadgeVariant where
  show BadgeStatus = "status"
  show BadgePrice = "price"
  show BadgeRating = "rating"
  show BadgeCategory = "category"
  show BadgeCustom = "custom"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // badge style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual style of the badge
data BadgeStyle
  = StyleSolid        -- ^ Solid background
  | StyleOutline      -- ^ Border only, transparent fill
  | StyleGlass        -- ^ Frosted glass effect
  | StyleGradient     -- ^ Gradient background

derive instance eqBadgeStyle :: Eq BadgeStyle
derive instance ordBadgeStyle :: Ord BadgeStyle

instance showBadgeStyle :: Show BadgeStyle where
  show StyleSolid = "solid"
  show StyleOutline = "outline"
  show StyleGlass = "glass"
  show StyleGradient = "gradient"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // badge config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete badge configuration.
-- |
-- | Defines all visual and semantic properties of a card badge:
-- | - Content (text, icon, or both)
-- | - Position on the card
-- | - Visual style (solid, outline, glass, gradient)
-- | - Colors (background, text, border)
-- | - Size and spacing
-- |
-- | ## Color Configuration
-- |
-- | Colors are specified as hex strings (e.g., "#EF4444").
-- | In production, these map to Schema.Color.RGB atoms.
-- |
-- | ## Icon Support
-- |
-- | Icons can be:
-- | - Named icons from icon library (e.g., "star", "fire")
-- | - SVG path data
-- | - Emoji characters
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Custom "FLASH SALE" badge
-- | flashSale = badgeConfig
-- |   { text: "FLASH SALE"
-- |   , icon: Just "lightning"
-- |   , position: BadgeTopRight
-- |   , variant: BadgeStatus
-- |   , style: StyleGradient
-- |   , backgroundColor: "#EF4444"
-- |   , textColor: "#FFFFFF"
-- |   , borderRadius: 4.0
-- |   , paddingX: 8.0
-- |   , paddingY: 4.0
-- |   , fontSize: 12.0
-- |   , fontWeight: 700
-- |   }
-- | ```
newtype BadgeConfig = BadgeConfig
  { text :: String                    -- ^ Badge text content
  , icon :: Maybe String              -- ^ Icon name or SVG path (optional)
  , iconPosition :: IconPosition      -- ^ Icon before or after text
  , position :: BadgePosition         -- ^ Position on card
  , variant :: BadgeVariant           -- ^ Semantic variant
  , style :: BadgeStyle               -- ^ Visual style
  , backgroundColor :: String         -- ^ Background color (hex)
  , textColor :: String               -- ^ Text color (hex)
  , borderColor :: Maybe String       -- ^ Border color (hex, for outline style)
  , borderRadius :: Number            -- ^ Corner radius (pixels)
  , paddingX :: Number                -- ^ Horizontal padding (pixels)
  , paddingY :: Number                -- ^ Vertical padding (pixels)
  , fontSize :: Number                -- ^ Font size (pixels)
  , fontWeight :: Int                 -- ^ Font weight (100-900)
  , offsetX :: Number                 -- ^ Offset from edge X (pixels)
  , offsetY :: Number                 -- ^ Offset from edge Y (pixels)
  , shadow :: Boolean                 -- ^ Add drop shadow
  , animate :: Boolean                -- ^ Animate entrance
  }

-- | Icon position relative to text
data IconPosition
  = IconBefore                        -- ^ Icon before text
  | IconAfter                         -- ^ Icon after text
  | IconOnly                          -- ^ Icon only, no text

derive instance eqIconPosition :: Eq IconPosition

instance showIconPosition :: Show IconPosition where
  show IconBefore = "before"
  show IconAfter = "after"
  show IconOnly = "only"

derive instance eqBadgeConfig :: Eq BadgeConfig

instance showBadgeConfig :: Show BadgeConfig where
  show (BadgeConfig c) = 
    "BadgeConfig(\"" <> c.text <> "\", " <> show c.position <> ")"

-- | Create badge config with full options
badgeConfig
  :: { text :: String
     , icon :: Maybe String
     , iconPosition :: IconPosition
     , position :: BadgePosition
     , variant :: BadgeVariant
     , style :: BadgeStyle
     , backgroundColor :: String
     , textColor :: String
     , borderColor :: Maybe String
     , borderRadius :: Number
     , paddingX :: Number
     , paddingY :: Number
     , fontSize :: Number
     , fontWeight :: Int
     , offsetX :: Number
     , offsetY :: Number
     , shadow :: Boolean
     , animate :: Boolean
     }
  -> BadgeConfig
badgeConfig cfg = BadgeConfig
  { text: cfg.text
  , icon: cfg.icon
  , iconPosition: cfg.iconPosition
  , position: cfg.position
  , variant: cfg.variant
  , style: cfg.style
  , backgroundColor: cfg.backgroundColor
  , textColor: cfg.textColor
  , borderColor: cfg.borderColor
  , borderRadius: clampRadius cfg.borderRadius
  , paddingX: clampPadding cfg.paddingX
  , paddingY: clampPadding cfg.paddingY
  , fontSize: clampFontSize cfg.fontSize
  , fontWeight: clampWeight cfg.fontWeight
  , offsetX: cfg.offsetX
  , offsetY: cfg.offsetY
  , shadow: cfg.shadow
  , animate: cfg.animate
  }
  where
    clampRadius r
      | r < 0.0 = 0.0
      | r > 100.0 = 100.0
      | otherwise = r
    clampPadding p
      | p < 0.0 = 0.0
      | p > 50.0 = 50.0
      | otherwise = p
    clampFontSize s
      | s < 8.0 = 8.0
      | s > 32.0 = 32.0
      | otherwise = s
    clampWeight w
      | w < 100 = 100
      | w > 900 = 900
      | otherwise = w

-- | Default badge config (neutral style)
defaultBadgeConfig :: BadgeConfig
defaultBadgeConfig = BadgeConfig
  { text: ""
  , icon: Nothing
  , iconPosition: IconBefore
  , position: BadgeTopRight
  , variant: BadgeCustom
  , style: StyleSolid
  , backgroundColor: "#6B7280"
  , textColor: "#FFFFFF"
  , borderColor: Nothing
  , borderRadius: 4.0
  , paddingX: 8.0
  , paddingY: 4.0
  , fontSize: 12.0
  , fontWeight: 600
  , offsetX: 8.0
  , offsetY: 8.0
  , shadow: false
  , animate: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | "NEW" badge preset — bright blue, top-left
newBadge :: BadgeConfig
newBadge = BadgeConfig
  { text: "NEW"
  , icon: Nothing
  , iconPosition: IconBefore
  , position: BadgeTopLeft
  , variant: BadgeStatus
  , style: StyleSolid
  , backgroundColor: "#3B82F6"
  , textColor: "#FFFFFF"
  , borderColor: Nothing
  , borderRadius: 4.0
  , paddingX: 8.0
  , paddingY: 4.0
  , fontSize: 11.0
  , fontWeight: 700
  , offsetX: 8.0
  , offsetY: 8.0
  , shadow: true
  , animate: true
  }

-- | "SALE" badge preset — red, top-right
saleBadge :: BadgeConfig
saleBadge = BadgeConfig
  { text: "SALE"
  , icon: Nothing
  , iconPosition: IconBefore
  , position: BadgeTopRight
  , variant: BadgeStatus
  , style: StyleSolid
  , backgroundColor: "#EF4444"
  , textColor: "#FFFFFF"
  , borderColor: Nothing
  , borderRadius: 4.0
  , paddingX: 8.0
  , paddingY: 4.0
  , fontSize: 11.0
  , fontWeight: 700
  , offsetX: 8.0
  , offsetY: 8.0
  , shadow: true
  , animate: false
  }

-- | "SOLD OUT" badge preset — dark, centered
soldOutBadge :: BadgeConfig
soldOutBadge = BadgeConfig
  { text: "SOLD OUT"
  , icon: Nothing
  , iconPosition: IconBefore
  , position: BadgeTopCenter
  , variant: BadgeStatus
  , style: StyleSolid
  , backgroundColor: "#1F2937"
  , textColor: "#FFFFFF"
  , borderColor: Nothing
  , borderRadius: 4.0
  , paddingX: 12.0
  , paddingY: 6.0
  , fontSize: 12.0
  , fontWeight: 700
  , offsetX: 0.0
  , offsetY: 8.0
  , shadow: true
  , animate: false
  }

-- | "HOT" badge preset — orange with fire icon
hotBadge :: BadgeConfig
hotBadge = BadgeConfig
  { text: "HOT"
  , icon: Just "fire"
  , iconPosition: IconBefore
  , position: BadgeTopRight
  , variant: BadgeStatus
  , style: StyleGradient
  , backgroundColor: "#F97316"
  , textColor: "#FFFFFF"
  , borderColor: Nothing
  , borderRadius: 16.0
  , paddingX: 10.0
  , paddingY: 4.0
  , fontSize: 11.0
  , fontWeight: 700
  , offsetX: 8.0
  , offsetY: 8.0
  , shadow: true
  , animate: true
  }

-- | Price badge preset — bottom-right, pill shape
priceBadge :: BadgeConfig
priceBadge = BadgeConfig
  { text: "$0.00"
  , icon: Nothing
  , iconPosition: IconBefore
  , position: BadgeBottomRight
  , variant: BadgePrice
  , style: StyleSolid
  , backgroundColor: "#059669"
  , textColor: "#FFFFFF"
  , borderColor: Nothing
  , borderRadius: 16.0
  , paddingX: 10.0
  , paddingY: 4.0
  , fontSize: 14.0
  , fontWeight: 700
  , offsetX: 8.0
  , offsetY: 8.0
  , shadow: true
  , animate: false
  }

-- | Rating badge preset — bottom-left with star
ratingBadge :: BadgeConfig
ratingBadge = BadgeConfig
  { text: "0.0"
  , icon: Just "star"
  , iconPosition: IconAfter
  , position: BadgeBottomLeft
  , variant: BadgeRating
  , style: StyleGlass
  , backgroundColor: "#000000"
  , textColor: "#FFFFFF"
  , borderColor: Nothing
  , borderRadius: 4.0
  , paddingX: 8.0
  , paddingY: 4.0
  , fontSize: 12.0
  , fontWeight: 600
  , offsetX: 8.0
  , offsetY: 8.0
  , shadow: false
  , animate: false
  }

-- | Create price badge with specific price
priceBadgeWith :: String -> BadgeConfig
priceBadgeWith price = BadgeConfig
  { text: price
  , icon: Nothing
  , iconPosition: IconBefore
  , position: BadgeBottomRight
  , variant: BadgePrice
  , style: StyleSolid
  , backgroundColor: "#059669"
  , textColor: "#FFFFFF"
  , borderColor: Nothing
  , borderRadius: 16.0
  , paddingX: 10.0
  , paddingY: 4.0
  , fontSize: 14.0
  , fontWeight: 700
  , offsetX: 8.0
  , offsetY: 8.0
  , shadow: true
  , animate: false
  }

-- | Create rating badge with specific rating
ratingBadgeWith :: String -> BadgeConfig
ratingBadgeWith rating = BadgeConfig
  { text: rating
  , icon: Just "star"
  , iconPosition: IconAfter
  , position: BadgeBottomLeft
  , variant: BadgeRating
  , style: StyleGlass
  , backgroundColor: "#000000"
  , textColor: "#FFFFFF"
  , borderColor: Nothing
  , borderRadius: 4.0
  , paddingX: 8.0
  , paddingY: 4.0
  , fontSize: 12.0
  , fontWeight: 600
  , offsetX: 8.0
  , offsetY: 8.0
  , shadow: false
  , animate: false
  }

-- | Create category tag badge
categoryBadge :: String -> BadgeConfig
categoryBadge category = BadgeConfig
  { text: category
  , icon: Nothing
  , iconPosition: IconBefore
  , position: BadgeTopLeft
  , variant: BadgeCategory
  , style: StyleOutline
  , backgroundColor: "#FFFFFF"
  , textColor: "#6B7280"
  , borderColor: Just "#D1D5DB"
  , borderRadius: 4.0
  , paddingX: 8.0
  , paddingY: 4.0
  , fontSize: 11.0
  , fontWeight: 500
  , offsetX: 8.0
  , offsetY: 8.0
  , shadow: false
  , animate: false
  }

-- | Create custom text badge
textBadge :: String -> String -> String -> BadgeConfig
textBadge text bgColor txtColor = BadgeConfig
  { text: text
  , icon: Nothing
  , iconPosition: IconBefore
  , position: BadgeTopRight
  , variant: BadgeCustom
  , style: StyleSolid
  , backgroundColor: bgColor
  , textColor: txtColor
  , borderColor: Nothing
  , borderRadius: 4.0
  , paddingX: 8.0
  , paddingY: 4.0
  , fontSize: 11.0
  , fontWeight: 600
  , offsetX: 8.0
  , offsetY: 8.0
  , shadow: false
  , animate: false
  }
