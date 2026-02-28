-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // component // card // media
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Card Media — Media zones for cards.
-- |
-- | ## Design Philosophy
-- |
-- | Media (images, videos, Lottie animations) can be positioned in various
-- | zones within a card:
-- | - Top/Bottom: Full-width media above/below content
-- | - Left/Right: Side-by-side with content
-- | - Cover: Full background with overlay
-- | - Background: Behind content (parallax capable)
-- |
-- | ## Use Cases
-- |
-- | - Product cards with hero images
-- | - Profile cards with avatars
-- | - Article cards with cover images
-- | - Portfolio items with video previews
-- |
-- | ## Dependencies
-- |
-- | - Schema.Dimension.Device (sizing)

module Hydrogen.Element.Compound.Card.Media
  ( -- * Media Position
    MediaPosition
      ( MediaTop
      , MediaBottom
      , MediaLeft
      , MediaRight
      , MediaCover
      , MediaBackground
      )
  
  -- * Media Type
  , MediaType
      ( MediaImage
      , MediaVideo
      , MediaLottie
      , MediaIcon
      , MediaAvatar
      )
  
  -- * Media Config
  , MediaConfig
  , mediaConfig
  , defaultMediaConfig
  
  -- * Media Source
  , MediaSource
      ( SourceUrl
      , SourceData
      )
  , sourceUrl
  , sourceData
  
  -- * Aspect Ratio
  , AspectRatio
      ( Ratio16x9
      , Ratio4x3
      , Ratio1x1
      , Ratio3x2
      , Ratio21x9
      , RatioCustom
      )
  , aspectRatio
  
  -- * Object Fit
  , ObjectFit
      ( FitCover
      , FitContain
      , FitFill
      , FitNone
      , FitScaleDown
      )
  
  -- * Media Dimension
  , MediaDimension
      ( DimAuto
      , DimPixels
      , DimPercent
      , DimFill
      )
  
  -- * Loading Strategy
  , LoadingStrategy
      ( LoadEager
      , LoadLazy
      , LoadOnHover
      )
  
  -- * Media Placeholder
  , MediaPlaceholder
      ( PlaceholderNone
      , PlaceholderColor
      , PlaceholderBlur
      , PlaceholderShimmer
      , PlaceholderSkeleton
      )
  
  -- * Autoplay Behavior
  , AutoplayBehavior
      ( AutoplayNever
      , AutoplayAlways
      , AutoplayOnHover
      , AutoplayInViewport
      )
  
  -- * Overlay Config
  , OverlayConfig
      ( OverlayNone
      , OverlaySolid
      , OverlayGradient
      )
  , GradientDirection
      ( GradientTop
      , GradientBottom
      , GradientLeft
      , GradientRight
      )
  
  -- * Presets
  , heroImage
  , squareThumbnail
  , coverWithOverlay
  , videoPreview
  , avatarMedia
  , parallaxBackground
  , lottieMedia
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (<>)
  , (<)
  , (>)
  , otherwise
  , show
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // media position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Position of media within the card
data MediaPosition
  = MediaTop          -- ^ Full-width at top
  | MediaBottom       -- ^ Full-width at bottom
  | MediaLeft         -- ^ Left side, content on right
  | MediaRight        -- ^ Right side, content on left
  | MediaCover        -- ^ Full card background with content overlay
  | MediaBackground   -- ^ Behind content (can have parallax)

derive instance eqMediaPosition :: Eq MediaPosition
derive instance ordMediaPosition :: Ord MediaPosition

instance showMediaPosition :: Show MediaPosition where
  show MediaTop = "top"
  show MediaBottom = "bottom"
  show MediaLeft = "left"
  show MediaRight = "right"
  show MediaCover = "cover"
  show MediaBackground = "background"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // media type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of media content
data MediaType
  = MediaImage        -- ^ Static image
  | MediaVideo        -- ^ Video (auto-plays on hover typically)
  | MediaLottie       -- ^ Lottie animation
  | MediaIcon         -- ^ Icon/symbol
  | MediaAvatar       -- ^ Avatar/profile image (rounded)

derive instance eqMediaType :: Eq MediaType
derive instance ordMediaType :: Ord MediaType

instance showMediaType :: Show MediaType where
  show MediaImage = "image"
  show MediaVideo = "video"
  show MediaLottie = "lottie"
  show MediaIcon = "icon"
  show MediaAvatar = "avatar"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // media source
-- ═════════════════════════════════════════════════════════════════════════════

-- | Source of media content
data MediaSource
  = SourceUrl String      -- ^ URL to media file
  | SourceData String     -- ^ Base64-encoded or data URI

derive instance eqMediaSource :: Eq MediaSource
derive instance ordMediaSource :: Ord MediaSource

instance showMediaSource :: Show MediaSource where
  show (SourceUrl _) = "url"
  show (SourceData _) = "data"

-- | Create URL media source
sourceUrl :: String -> MediaSource
sourceUrl = SourceUrl

-- | Create data media source
sourceData :: String -> MediaSource
sourceData = SourceData

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // aspect ratio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Aspect ratio presets
data AspectRatio
  = Ratio16x9         -- ^ Widescreen video (16:9)
  | Ratio4x3          -- ^ Traditional TV (4:3)
  | Ratio1x1          -- ^ Square
  | Ratio3x2          -- ^ Classic photo (3:2)
  | Ratio21x9         -- ^ Ultrawide (21:9)
  | RatioCustom Number Number  -- ^ Custom ratio (width:height)

derive instance eqAspectRatio :: Eq AspectRatio

instance showAspectRatio :: Show AspectRatio where
  show Ratio16x9 = "16/9"
  show Ratio4x3 = "4/3"
  show Ratio1x1 = "1/1"
  show Ratio3x2 = "3/2"
  show Ratio21x9 = "21/9"
  show (RatioCustom w h) = show w <> "/" <> show h

-- | Create aspect ratio
aspectRatio :: AspectRatio -> AspectRatio
aspectRatio = \r -> r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // object fit
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS object-fit values
data ObjectFit
  = FitCover          -- ^ Cover container, may crop
  | FitContain        -- ^ Fit inside container, may letterbox
  | FitFill           -- ^ Stretch to fill (distorts)
  | FitNone           -- ^ No resizing
  | FitScaleDown      -- ^ Like contain but never scales up

derive instance eqObjectFit :: Eq ObjectFit
derive instance ordObjectFit :: Ord ObjectFit

instance showObjectFit :: Show ObjectFit where
  show FitCover = "cover"
  show FitContain = "contain"
  show FitFill = "fill"
  show FitNone = "none"
  show FitScaleDown = "scale-down"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // media config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete media configuration for card media zones.
-- |
-- | ## Configuration Fields
-- |
-- | - `source`: Media source (URL or embedded data)
-- | - `mediaType`: Type of media content (image, video, Lottie, etc.)
-- | - `position`: Where media appears in the card
-- | - `aspectRatio`: Aspect ratio constraint
-- | - `objectFit`: How media fits within its container
-- | - `alt`: Accessible alternative text
-- | - `loading`: Loading strategy (lazy, eager)
-- | - `autoplay`: Video/Lottie autoplay behavior
-- | - `muted`: Video mute state
-- | - `loop`: Video/Lottie loop behavior
-- | - `overlay`: Optional color overlay for cover media
-- | - `overlayOpacity`: Overlay opacity (0.0 to 1.0)
-- | - `parallaxEnabled`: Enable parallax scrolling effect
-- | - `parallaxIntensity`: Parallax movement intensity
-- | - `borderRadius`: Corner radius for media
-- | - `grayscale`: Apply grayscale filter
-- | - `grayscaleOnHover`: Toggle grayscale on hover
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Simple hero image
-- | heroMedia = mediaConfig
-- |   { source: sourceUrl "/images/hero.jpg"
-- |   , mediaType: MediaImage
-- |   , position: MediaTop
-- |   , aspectRatio: Ratio16x9
-- |   , objectFit: FitCover
-- |   , alt: "Product hero image"
-- |   }
-- |
-- | -- Video preview on hover
-- | videoPreview = mediaConfig
-- |   { source: sourceUrl "/videos/preview.mp4"
-- |   , mediaType: MediaVideo
-- |   , position: MediaCover
-- |   , autoplay: AutoplayOnHover
-- |   , muted: true
-- |   , loop: true
-- |   }
-- | ```
newtype MediaConfig = MediaConfig
  { -- Source
    source :: MediaSource               -- ^ Media source
  , mediaType :: MediaType              -- ^ Type of media
  
  -- Position & Sizing
  , position :: MediaPosition           -- ^ Position within card
  , aspectRatio :: AspectRatio          -- ^ Aspect ratio constraint
  , objectFit :: ObjectFit              -- ^ How media fits container
  , width :: MediaDimension             -- ^ Width constraint
  , height :: MediaDimension            -- ^ Height constraint
  
  -- Accessibility
  , alt :: String                       -- ^ Alternative text
  
  -- Loading
  , loading :: LoadingStrategy          -- ^ Loading strategy
  , placeholder :: MediaPlaceholder     -- ^ Placeholder while loading
  
  -- Video/Animation Behavior
  , autoplay :: AutoplayBehavior        -- ^ Autoplay behavior
  , muted :: Boolean                    -- ^ Mute video audio
  , loop :: Boolean                     -- ^ Loop video/animation
  , playbackRate :: Number              -- ^ Playback speed (1.0 = normal)
  
  -- Overlay (for cover/background media)
  , overlay :: OverlayConfig            -- ^ Color overlay config
  
  -- Effects
  , parallaxEnabled :: Boolean          -- ^ Enable parallax effect
  , parallaxIntensity :: Number         -- ^ Parallax intensity (0.0 to 1.0)
  , grayscale :: Boolean                -- ^ Apply grayscale filter
  , grayscaleOnHover :: Boolean         -- ^ Remove grayscale on hover
  , blur :: Number                      -- ^ Blur amount in pixels
  
  -- Styling
  , borderRadius :: Number              -- ^ Corner radius in pixels
  }

derive instance eqMediaConfig :: Eq MediaConfig

instance showMediaConfig :: Show MediaConfig where
  show (MediaConfig c) = 
    "MediaConfig(" <> show c.mediaType <> 
    " @ " <> show c.position <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // media dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dimension constraint for media
data MediaDimension
  = DimAuto                   -- ^ Automatic sizing
  | DimPixels Number          -- ^ Fixed pixel size
  | DimPercent Number         -- ^ Percentage of container
  | DimFill                   -- ^ Fill available space

derive instance eqMediaDimension :: Eq MediaDimension

instance showMediaDimension :: Show MediaDimension where
  show DimAuto = "auto"
  show (DimPixels n) = show n <> "px"
  show (DimPercent n) = show n <> "%"
  show DimFill = "100%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // loading strategy
-- ═════════════════════════════════════════════════════════════════════════════

-- | Media loading strategy
data LoadingStrategy
  = LoadEager          -- ^ Load immediately
  | LoadLazy           -- ^ Load when entering viewport
  | LoadOnHover        -- ^ Load when card is hovered

derive instance eqLoadingStrategy :: Eq LoadingStrategy

instance showLoadingStrategy :: Show LoadingStrategy where
  show LoadEager = "eager"
  show LoadLazy = "lazy"
  show LoadOnHover = "hover"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // media placeholder
-- ═════════════════════════════════════════════════════════════════════════════

-- | Placeholder shown while media loads
data MediaPlaceholder
  = PlaceholderNone                -- ^ No placeholder
  | PlaceholderColor String        -- ^ Solid color (hex)
  | PlaceholderBlur String         -- ^ Blurred low-res image URL
  | PlaceholderShimmer             -- ^ Animated shimmer effect
  | PlaceholderSkeleton            -- ^ Skeleton loading state

derive instance eqMediaPlaceholder :: Eq MediaPlaceholder

instance showMediaPlaceholder :: Show MediaPlaceholder where
  show PlaceholderNone = "none"
  show (PlaceholderColor _) = "color"
  show (PlaceholderBlur _) = "blur"
  show PlaceholderShimmer = "shimmer"
  show PlaceholderSkeleton = "skeleton"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // autoplay behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Video/animation autoplay behavior
data AutoplayBehavior
  = AutoplayNever          -- ^ Never autoplay
  | AutoplayAlways         -- ^ Always autoplay (muted required)
  | AutoplayOnHover        -- ^ Play when hovered
  | AutoplayInViewport     -- ^ Play when scrolled into view

derive instance eqAutoplayBehavior :: Eq AutoplayBehavior

instance showAutoplayBehavior :: Show AutoplayBehavior where
  show AutoplayNever = "never"
  show AutoplayAlways = "always"
  show AutoplayOnHover = "hover"
  show AutoplayInViewport = "viewport"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // overlay config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overlay configuration for cover/background media
data OverlayConfig
  = OverlayNone                            -- ^ No overlay
  | OverlaySolid String Number             -- ^ Solid color with opacity
  | OverlayGradient GradientDirection String String Number
                                           -- ^ Gradient overlay

derive instance eqOverlayConfig :: Eq OverlayConfig

instance showOverlayConfig :: Show OverlayConfig where
  show OverlayNone = "none"
  show (OverlaySolid _ _) = "solid"
  show (OverlayGradient _ _ _ _) = "gradient"

-- | Gradient direction
data GradientDirection
  = GradientTop           -- ^ Top to bottom
  | GradientBottom        -- ^ Bottom to top
  | GradientLeft          -- ^ Left to right
  | GradientRight         -- ^ Right to left

derive instance eqGradientDirection :: Eq GradientDirection

instance showGradientDirection :: Show GradientDirection where
  show GradientTop = "to-bottom"
  show GradientBottom = "to-top"
  show GradientLeft = "to-right"
  show GradientRight = "to-left"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create media config with full options
mediaConfig
  :: { source :: MediaSource
     , mediaType :: MediaType
     , position :: MediaPosition
     , aspectRatio :: AspectRatio
     , objectFit :: ObjectFit
     , width :: MediaDimension
     , height :: MediaDimension
     , alt :: String
     , loading :: LoadingStrategy
     , placeholder :: MediaPlaceholder
     , autoplay :: AutoplayBehavior
     , muted :: Boolean
     , loop :: Boolean
     , playbackRate :: Number
     , overlay :: OverlayConfig
     , parallaxEnabled :: Boolean
     , parallaxIntensity :: Number
     , grayscale :: Boolean
     , grayscaleOnHover :: Boolean
     , blur :: Number
     , borderRadius :: Number
     }
  -> MediaConfig
mediaConfig cfg = MediaConfig
  { source: cfg.source
  , mediaType: cfg.mediaType
  , position: cfg.position
  , aspectRatio: cfg.aspectRatio
  , objectFit: cfg.objectFit
  , width: cfg.width
  , height: cfg.height
  , alt: cfg.alt
  , loading: cfg.loading
  , placeholder: cfg.placeholder
  , autoplay: cfg.autoplay
  , muted: cfg.muted
  , loop: cfg.loop
  , playbackRate: clampPlaybackRate cfg.playbackRate
  , overlay: cfg.overlay
  , parallaxEnabled: cfg.parallaxEnabled
  , parallaxIntensity: clampIntensity cfg.parallaxIntensity
  , grayscale: cfg.grayscale
  , grayscaleOnHover: cfg.grayscaleOnHover
  , blur: clampBlur cfg.blur
  , borderRadius: clampRadius cfg.borderRadius
  }
  where
    clampPlaybackRate r
      | r < 0.25 = 0.25
      | r > 4.0 = 4.0
      | otherwise = r
    clampIntensity i
      | i < 0.0 = 0.0
      | i > 1.0 = 1.0
      | otherwise = i
    clampBlur b
      | b < 0.0 = 0.0
      | b > 100.0 = 100.0
      | otherwise = b
    clampRadius r
      | r < 0.0 = 0.0
      | r > 100.0 = 100.0
      | otherwise = r

-- | Default media config for a simple image
defaultMediaConfig :: MediaConfig
defaultMediaConfig = MediaConfig
  { source: SourceUrl ""
  , mediaType: MediaImage
  , position: MediaTop
  , aspectRatio: Ratio16x9
  , objectFit: FitCover
  , width: DimFill
  , height: DimAuto
  , alt: ""
  , loading: LoadLazy
  , placeholder: PlaceholderSkeleton
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.2
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hero image preset (full-width top image)
heroImage :: MediaSource -> String -> MediaConfig
heroImage src altText = MediaConfig
  { source: src
  , mediaType: MediaImage
  , position: MediaTop
  , aspectRatio: Ratio16x9
  , objectFit: FitCover
  , width: DimFill
  , height: DimAuto
  , alt: altText
  , loading: LoadEager
  , placeholder: PlaceholderShimmer
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }

-- | Square thumbnail preset (1:1 ratio)
squareThumbnail :: MediaSource -> String -> MediaConfig
squareThumbnail src altText = MediaConfig
  { source: src
  , mediaType: MediaImage
  , position: MediaTop
  , aspectRatio: Ratio1x1
  , objectFit: FitCover
  , width: DimFill
  , height: DimAuto
  , alt: altText
  , loading: LoadLazy
  , placeholder: PlaceholderSkeleton
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 8.0
  }

-- | Cover media with dark overlay (for text readability)
coverWithOverlay :: MediaSource -> String -> String -> Number -> MediaConfig
coverWithOverlay src altText overlayColor overlayOpacity = MediaConfig
  { source: src
  , mediaType: MediaImage
  , position: MediaCover
  , aspectRatio: Ratio16x9
  , objectFit: FitCover
  , width: DimFill
  , height: DimFill
  , alt: altText
  , loading: LoadEager
  , placeholder: PlaceholderColor overlayColor
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlaySolid overlayColor overlayOpacity
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }

-- | Video preview (plays on hover)
videoPreview :: MediaSource -> MediaConfig
videoPreview src = MediaConfig
  { source: src
  , mediaType: MediaVideo
  , position: MediaTop
  , aspectRatio: Ratio16x9
  , objectFit: FitCover
  , width: DimFill
  , height: DimAuto
  , alt: "Video preview"
  , loading: LoadOnHover
  , placeholder: PlaceholderSkeleton
  , autoplay: AutoplayOnHover
  , muted: true
  , loop: true
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }

-- | Avatar preset (circular profile image)
avatarMedia :: MediaSource -> String -> MediaConfig
avatarMedia src altText = MediaConfig
  { source: src
  , mediaType: MediaAvatar
  , position: MediaLeft
  , aspectRatio: Ratio1x1
  , objectFit: FitCover
  , width: DimPixels 48.0
  , height: DimPixels 48.0
  , alt: altText
  , loading: LoadLazy
  , placeholder: PlaceholderShimmer
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 50.0
  }

-- | Background with parallax effect
parallaxBackground :: MediaSource -> String -> MediaConfig
parallaxBackground src altText = MediaConfig
  { source: src
  , mediaType: MediaImage
  , position: MediaBackground
  , aspectRatio: Ratio16x9
  , objectFit: FitCover
  , width: DimFill
  , height: DimFill
  , alt: altText
  , loading: LoadEager
  , placeholder: PlaceholderBlur ""
  , autoplay: AutoplayNever
  , muted: true
  , loop: false
  , playbackRate: 1.0
  , overlay: OverlayGradient GradientBottom "#000000" "#00000000" 0.5
  , parallaxEnabled: true
  , parallaxIntensity: 0.3
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }

-- | Lottie animation preset
lottieMedia :: MediaSource -> MediaConfig
lottieMedia src = MediaConfig
  { source: src
  , mediaType: MediaLottie
  , position: MediaTop
  , aspectRatio: Ratio1x1
  , objectFit: FitContain
  , width: DimFill
  , height: DimAuto
  , alt: "Animation"
  , loading: LoadLazy
  , placeholder: PlaceholderNone
  , autoplay: AutoplayInViewport
  , muted: true
  , loop: true
  , playbackRate: 1.0
  , overlay: OverlayNone
  , parallaxEnabled: false
  , parallaxIntensity: 0.0
  , grayscale: false
  , grayscaleOnHover: false
  , blur: 0.0
  , borderRadius: 0.0
  }
