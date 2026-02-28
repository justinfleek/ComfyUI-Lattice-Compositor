-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // carousel // navigation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Navigation — Navigation UI configurations.
-- |
-- | ## Design Philosophy
-- |
-- | Navigation components are declarative configurations that the
-- | render function interprets into actual UI elements.
-- |
-- | ## Navigation Types
-- |
-- | - Arrows: Previous/Next buttons
-- | - Dots: Indicator dots for each slide
-- | - Thumbnails: Mini preview images
-- | - Progress: Progress bar showing position
-- | - Numbers: "3 / 10" style indicator
-- |
-- | ## Dependencies
-- |
-- | - Carousel.Types (NavigationMode)

module Hydrogen.Element.Compound.Carousel.Navigation
  ( -- * Arrow Config
    ArrowConfig
  , arrowConfig
  , defaultArrows
  , ArrowPosition
      ( ArrowsInside
      , ArrowsOutside
      , ArrowsOverlay
      )
  
  -- * Dots Config
  , DotsConfig
  , dotsConfig
  , defaultDots
  , DotsPosition
      ( DotsBottom
      , DotsTop
      , DotsLeft
      , DotsRight
      , DotsOverlay
      )
  
  -- * Progress Config
  , ProgressConfig
  , progressConfig
  , defaultProgress
  
  -- * Thumbnail Config
  , ThumbnailConfig
  , thumbnailConfig
  , defaultThumbnails
  , ThumbnailPosition
      ( ThumbnailsBottom
      , ThumbnailsTop
      , ThumbnailsLeft
      , ThumbnailsRight
      )
  
  -- * Navigation Config
  , NavigationConfig
  , defaultNavigation
  , minimalNavigation
  , fullNavigation
  , thumbnailNavigation
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  )

import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Color.RGB as Color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // arrow config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of navigation arrows
data ArrowPosition
  = ArrowsInside       -- ^ Inside the carousel container
  | ArrowsOutside      -- ^ Outside the carousel edges
  | ArrowsOverlay      -- ^ Overlay on top of slides

derive instance eqArrowPosition :: Eq ArrowPosition

instance showArrowPosition :: Show ArrowPosition where
  show ArrowsInside = "inside"
  show ArrowsOutside = "outside"
  show ArrowsOverlay = "overlay"

-- | Arrow navigation configuration
type ArrowConfig =
  { enabled :: Boolean
  , position :: ArrowPosition
  , size :: Device.Pixel
  , color :: Color.RGB
  , hoverColor :: Color.RGB
  , showOnHover :: Boolean       -- Only show arrows on hover
  }

-- | Create arrow config
arrowConfig :: ArrowPosition -> Device.Pixel -> Color.RGB -> ArrowConfig
arrowConfig position size color =
  { enabled: true
  , position
  , size
  , color
  , hoverColor: color
  , showOnHover: false
  }

-- | Default arrow configuration
defaultArrows :: ArrowConfig
defaultArrows = arrowConfig 
  ArrowsInside 
  (Device.px 40.0) 
  (Color.rgb 255 255 255)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // dots config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of dot indicators
data DotsPosition
  = DotsBottom         -- ^ Below the carousel
  | DotsTop            -- ^ Above the carousel
  | DotsLeft           -- ^ Left side (vertical)
  | DotsRight          -- ^ Right side (vertical)
  | DotsOverlay        -- ^ Inside carousel at bottom

derive instance eqDotsPosition :: Eq DotsPosition

instance showDotsPosition :: Show DotsPosition where
  show DotsBottom = "bottom"
  show DotsTop = "top"
  show DotsLeft = "left"
  show DotsRight = "right"
  show DotsOverlay = "overlay"

-- | Dot indicator configuration
type DotsConfig =
  { enabled :: Boolean
  , position :: DotsPosition
  , size :: Device.Pixel
  , gap :: Device.Pixel
  , activeColor :: Color.RGB
  , inactiveColor :: Color.RGB
  , clickable :: Boolean
  }

-- | Create dots config
dotsConfig :: DotsPosition -> Device.Pixel -> Color.RGB -> Color.RGB -> DotsConfig
dotsConfig position size activeColor inactiveColor =
  { enabled: true
  , position
  , size
  , gap: Device.px 8.0
  , activeColor
  , inactiveColor
  , clickable: true
  }

-- | Default dots configuration
defaultDots :: DotsConfig
defaultDots = dotsConfig 
  DotsBottom 
  (Device.px 10.0) 
  (Color.rgb 59 130 246)    -- Blue active
  (Color.rgb 156 163 175)   -- Gray inactive

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // progress config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress bar configuration
type ProgressConfig =
  { enabled :: Boolean
  , height :: Device.Pixel
  , backgroundColor :: Color.RGB
  , fillColor :: Color.RGB
  , showOnTop :: Boolean
  }

-- | Create progress config
progressConfig :: Device.Pixel -> Color.RGB -> Color.RGB -> ProgressConfig
progressConfig height bgColor fillColor =
  { enabled: true
  , height
  , backgroundColor: bgColor
  , fillColor
  , showOnTop: false
  }

-- | Default progress configuration
defaultProgress :: ProgressConfig
defaultProgress = progressConfig 
  (Device.px 4.0) 
  (Color.rgb 229 231 235)   -- Light gray
  (Color.rgb 59 130 246)    -- Blue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // thumbnail config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of thumbnail strip
data ThumbnailPosition
  = ThumbnailsBottom     -- ^ Below the main carousel
  | ThumbnailsTop        -- ^ Above the main carousel
  | ThumbnailsLeft       -- ^ Left side (vertical strip)
  | ThumbnailsRight      -- ^ Right side (vertical strip)

derive instance eqThumbnailPosition :: Eq ThumbnailPosition

instance showThumbnailPosition :: Show ThumbnailPosition where
  show ThumbnailsBottom = "bottom"
  show ThumbnailsTop = "top"
  show ThumbnailsLeft = "left"
  show ThumbnailsRight = "right"

-- | Thumbnail navigation configuration
type ThumbnailConfig =
  { enabled :: Boolean
  , position :: ThumbnailPosition
  , width :: Device.Pixel           -- Width of each thumbnail
  , height :: Device.Pixel          -- Height of each thumbnail
  , gap :: Device.Pixel             -- Gap between thumbnails
  , borderWidth :: Device.Pixel     -- Border width on active thumbnail
  , borderColor :: Color.RGB        -- Border color on active thumbnail
  , inactiveBorderColor :: Color.RGB -- Border color on inactive thumbnails
  , opacity :: Number               -- Opacity of inactive thumbnails (0.0-1.0)
  , activeOpacity :: Number         -- Opacity of active thumbnail (0.0-1.0)
  }

-- | Create thumbnail config
thumbnailConfig :: ThumbnailPosition -> Device.Pixel -> Device.Pixel -> ThumbnailConfig
thumbnailConfig position width height =
  { enabled: true
  , position
  , width
  , height
  , gap: Device.px 8.0
  , borderWidth: Device.px 2.0
  , borderColor: Color.rgb 59 130 246         -- Blue for active
  , inactiveBorderColor: Color.rgb 229 231 235 -- Light gray for inactive
  , opacity: 0.6
  , activeOpacity: 1.0
  }

-- | Default thumbnail configuration
defaultThumbnails :: ThumbnailConfig
defaultThumbnails = thumbnailConfig
  ThumbnailsBottom
  (Device.px 80.0)
  (Device.px 60.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // navigation config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined navigation configuration
type NavigationConfig =
  { arrows :: ArrowConfig
  , dots :: DotsConfig
  , progress :: ProgressConfig
  , thumbnails :: ThumbnailConfig
  , keyboardEnabled :: Boolean
  , swipeEnabled :: Boolean
  }

-- | Default navigation (arrows and dots)
defaultNavigation :: NavigationConfig
defaultNavigation =
  { arrows: defaultArrows
  , dots: defaultDots
  , progress: defaultProgress { enabled = false }
  , thumbnails: defaultThumbnails { enabled = false }
  , keyboardEnabled: true
  , swipeEnabled: true
  }

-- | Minimal navigation (just dots)
minimalNavigation :: NavigationConfig
minimalNavigation =
  { arrows: defaultArrows { enabled = false }
  , dots: defaultDots
  , progress: defaultProgress { enabled = false }
  , thumbnails: defaultThumbnails { enabled = false }
  , keyboardEnabled: true
  , swipeEnabled: true
  }

-- | Full navigation (all controls)
fullNavigation :: NavigationConfig
fullNavigation =
  { arrows: defaultArrows
  , dots: defaultDots
  , progress: defaultProgress
  , thumbnails: defaultThumbnails { enabled = false }
  , keyboardEnabled: true
  , swipeEnabled: true
  }

-- | Thumbnail-based navigation (thumbnails instead of dots)
thumbnailNavigation :: NavigationConfig
thumbnailNavigation =
  { arrows: defaultArrows
  , dots: defaultDots { enabled = false }
  , progress: defaultProgress { enabled = false }
  , thumbnails: defaultThumbnails
  , keyboardEnabled: true
  , swipeEnabled: true
  }
