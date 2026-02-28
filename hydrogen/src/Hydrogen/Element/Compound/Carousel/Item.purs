-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // element // carousel // item
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Carousel Item — Content wrapper with shape, border, and hover effects.
-- |
-- | ## Design Philosophy
-- |
-- | An Item is the container for carousel content. It wraps content with:
-- | - Shape masking (star, hexagon, custom SVG)
-- | - Animated borders (gradient strokes, glowing edges)
-- | - Hover effects (audio triggers, Lottie animations)
-- |
-- | Items can contain:
-- | - Images, videos, point clouds
-- | - Cards (full Card compound)
-- | - Lottie animations
-- | - Custom elements
-- |
-- | ## Architecture
-- |
-- | ```
-- | Item
-- |   └─ ItemShape (geometry mask)
-- |   └─ ItemBorder (animated stroke)
-- |   └─ ItemHover (hover behaviors)
-- |   └─ ItemContent (actual content)
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Card.Shape (shape masking)
-- | - Card.Hover (hover effects)
-- | - Schema.Geometry.AnimatedBorder (border effects)

module Hydrogen.Element.Compound.Carousel.Item
  ( -- * Item Shape
    ItemShape
      ( ShapeRectangle
      , ShapeCircle
      , ShapeEllipse
      , ShapePolygon
      , ShapeStar
      , ShapeSvgPath
      , ShapeNone
      )
  , itemShape
  , noItemShape
  , rectangleShape
  , starItem
  , starItemWithRatio
  , hexagonItem
  , octagonItem
  , circleItem
  , ellipseItem
  , polygonItem
  , customShapeItem
  
  -- * Item Border
  , ItemBorder
      ( BorderNone
      , BorderSolid
      , BorderGradientLinear
      , BorderGradientConic
      , BorderGlow
      , BorderDashed
      , BorderAnimatedDash
      , BorderPulse
      , BorderRainbow
      )
  , itemBorder
  , noItemBorder
  , solidBorder
  , glowingBorder
  , glowingBorderWith
  , gradientBorder
  , gradientBorderWith
  , animatedDashBorder
  , animatedDashBorderWith
  , dashedBorder
  , pulseBorder
  , rainbowBorder
  
  -- * Item Hover
  , ItemHover
      ( HoverNone
      , HoverAudio
      , HoverAudioEnterLeave
      , HoverLottie
      , HoverLottieReverse
      , HoverScale
      , HoverLift
      , HoverCombined
      )
  , ItemHoverConfig
  , itemHover
  , noItemHover
  , audioOnHover
  , audioOnHoverWith
  , audioOnHoverEnterLeave
  , lottieOnHover
  , lottieOnHoverReverse
  , scaleOnHover
  , liftOnHover
  , combinedHover
  , combinedHoverWith
  , defaultHoverConfig
  
  -- * Item Content
  , ItemContent
      ( ContentImage
      , ContentVideo
      , ContentCard
      , ContentLottie
      , ContentPointCloud
      , ContentCustom
      )
  , ImageConfig
  , ImageLoading(LoadLazy, LoadEager)
  , ObjectFit(FitContain, FitCover, FitFill, FitNone, FitScaleDown)
  , VideoConfig
  , CardConfig
  , PointCloudConfig
  , PointColorMode(ColorFromData, ColorUniform, ColorByHeight, ColorByDepth)
  , imageContent
  , imageContentWith
  , videoContent
  , videoContentWith
  , cardContent
  , cardContentWith
  , lottieContent
  , pointCloudContent
  , customContent
  
  -- * Item Config
  , ItemConfig(..)
  , itemConfig
  , defaultItemConfig
  , imageItemConfig
  , cardItemConfig
  , interactiveItemConfig
  
  -- * Complete Item
  , Item(..)
  , item
  , simpleItem
  , imageItem
  , videoItem
  , lottieItem
  , cardItem
  , interactiveItem
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , otherwise
  , (<>)
  , (<)
  , (>)
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // item shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape configuration for an item.
-- |
-- | Defines the clipping mask applied to item content:
-- | - Rectangle (default, with optional corner radius)
-- | - Circle or ellipse
-- | - Regular polygons (hexagon, octagon, etc.)
-- | - Stars with configurable points
-- | - Custom SVG path
-- |
-- | ## Corner Radius
-- |
-- | For rectangular shapes, corner radius creates rounded corners.
-- | Radius is clamped to half the smaller dimension.
-- |
-- | ## Star Configuration
-- |
-- | Stars are defined by:
-- | - Point count (minimum 3)
-- | - Inner radius ratio (0.0 to 1.0, where 0.5 is typical)
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Rounded rectangle
-- | rounded = rectangleShape 8.0
-- |
-- | -- 5-pointed star with 50% inner radius
-- | star = starShape 5 0.5
-- |
-- | -- Custom heart shape
-- | heart = customShapeItem "M12 21.35l-1.45-1.32..."
-- | ```
data ItemShape
  = ShapeRectangle Number            -- ^ Rectangle with corner radius
  | ShapeCircle                      -- ^ Circle (aspect ratio preserved)
  | ShapeEllipse                     -- ^ Ellipse (fills container)
  | ShapePolygon Int                 -- ^ Regular polygon with n sides
  | ShapeStar Int Number             -- ^ Star with n points and inner ratio
  | ShapeSvgPath String              -- ^ Custom SVG path data
  | ShapeNone                        -- ^ No clipping (full rectangle)

derive instance eqItemShape :: Eq ItemShape

instance showItemShape :: Show ItemShape where
  show (ShapeRectangle r) = "rectangle:" <> show r
  show ShapeCircle = "circle"
  show ShapeEllipse = "ellipse"
  show (ShapePolygon n) = "polygon:" <> show n
  show (ShapeStar n _) = "star:" <> show n
  show (ShapeSvgPath _) = "svg-path"
  show ShapeNone = "none"

-- | Create rectangular shape with corner radius
itemShape :: Number -> ItemShape
itemShape radius = ShapeRectangle (clampRadius radius)
  where
    clampRadius r
      | r < 0.0 = 0.0
      | otherwise = r

-- | No shape clipping (default rectangle, no radius)
noItemShape :: ItemShape
noItemShape = ShapeNone

-- | Rectangle with rounded corners
rectangleShape :: Number -> ItemShape
rectangleShape = itemShape

-- | Star-shaped item with configurable points
-- |
-- | - points: Number of star points (minimum 3)
-- | - innerRatio: Inner radius as ratio of outer (0.0 to 1.0)
starItem :: Int -> ItemShape
starItem points = ShapeStar (clampPoints points) 0.5
  where
    clampPoints p
      | p < 3 = 3
      | p > 32 = 32
      | otherwise = p

-- | Star with custom inner radius ratio
starItemWithRatio :: Int -> Number -> ItemShape
starItemWithRatio points ratio = ShapeStar (clampPoints points) (clampRatio ratio)
  where
    clampPoints p
      | p < 3 = 3
      | p > 32 = 32
      | otherwise = p
    clampRatio r
      | r < 0.1 = 0.1
      | r > 0.9 = 0.9
      | otherwise = r

-- | Hexagon-shaped item (6-sided polygon)
hexagonItem :: ItemShape
hexagonItem = ShapePolygon 6

-- | Octagon-shaped item (8-sided polygon)
octagonItem :: ItemShape
octagonItem = ShapePolygon 8

-- | Circle-shaped item (preserves aspect ratio)
circleItem :: ItemShape
circleItem = ShapeCircle

-- | Ellipse-shaped item (fills container)
ellipseItem :: ItemShape
ellipseItem = ShapeEllipse

-- | Regular polygon with n sides
polygonItem :: Int -> ItemShape
polygonItem sides = ShapePolygon (clampSides sides)
  where
    clampSides s
      | s < 3 = 3
      | s > 32 = 32
      | otherwise = s

-- | Custom SVG path item
-- |
-- | Path data should be valid SVG path syntax (M, L, C, Z commands).
customShapeItem :: String -> ItemShape
customShapeItem = ShapeSvgPath

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // item border
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border configuration for an item.
-- |
-- | Defines visual border effects applied to item edges:
-- | - Solid color borders with configurable width
-- | - Gradient stroke borders (linear or conic)
-- | - Glowing/neon borders with blur
-- | - Animated borders (dash march, pulse, rainbow)
-- |
-- | ## Border Width
-- |
-- | Width is in pixels, clamped to 0.0-20.0 range.
-- |
-- | ## Animation
-- |
-- | Animated borders have timing parameters:
-- | - speed: Animation cycle duration in ms
-- | - direction: Forward, reverse, or alternate
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Simple 2px solid border
-- | simple = solidBorder 2.0 "#3B82F6"
-- |
-- | -- Neon glow effect
-- | neon = glowingBorder 3.0 "#00FF00" 10.0
-- |
-- | -- Animated gradient
-- | rainbow = rainbowBorder 2.0 2000.0
-- | ```
data ItemBorder
  = BorderNone                                    -- ^ No border
  | BorderSolid Number String                     -- ^ width, color (hex)
  | BorderGradientLinear Number String String Number
      -- ^ width, startColor, endColor, angle (degrees)
  | BorderGradientConic Number (Array String)     -- ^ width, colors array
  | BorderGlow Number String Number               -- ^ width, color, blur radius
  | BorderDashed Number String Number Number      -- ^ width, color, dashLength, gapLength
  | BorderAnimatedDash Number String Number       -- ^ width, color, speed (ms per cycle)
  | BorderPulse Number String Number Number       -- ^ width, color, minOpacity, speed
  | BorderRainbow Number Number                   -- ^ width, speed (ms per cycle)

derive instance eqItemBorder :: Eq ItemBorder

instance showItemBorder :: Show ItemBorder where
  show BorderNone = "none"
  show (BorderSolid w _) = "solid:" <> show w <> "px"
  show (BorderGradientLinear w _ _ _) = "gradient-linear:" <> show w <> "px"
  show (BorderGradientConic w _) = "gradient-conic:" <> show w <> "px"
  show (BorderGlow w _ _) = "glow:" <> show w <> "px"
  show (BorderDashed w _ _ _) = "dashed:" <> show w <> "px"
  show (BorderAnimatedDash w _ _) = "animated-dash:" <> show w <> "px"
  show (BorderPulse w _ _ _) = "pulse:" <> show w <> "px"
  show (BorderRainbow w _) = "rainbow:" <> show w <> "px"

-- | Create solid border
itemBorder :: Number -> String -> ItemBorder
itemBorder width color = BorderSolid (clampWidth width) color
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w

-- | No border
noItemBorder :: ItemBorder
noItemBorder = BorderNone

-- | Simple solid border
solidBorder :: Number -> String -> ItemBorder
solidBorder = itemBorder

-- | Glowing border effect (neon style)
-- |
-- | - width: Border line width
-- | - color: Glow color (hex)
-- | - blur: Blur radius for glow effect
glowingBorder :: ItemBorder
glowingBorder = BorderGlow 2.0 "#3B82F6" 8.0

-- | Glowing border with custom parameters
glowingBorderWith :: Number -> String -> Number -> ItemBorder
glowingBorderWith width color blur = BorderGlow 
  (clampWidth width) 
  color 
  (clampBlur blur)
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w
    clampBlur b
      | b < 0.0 = 0.0
      | b > 50.0 = 50.0
      | otherwise = b

-- | Gradient stroke border (linear)
gradientBorder :: ItemBorder
gradientBorder = BorderGradientLinear 2.0 "#3B82F6" "#8B5CF6" 45.0

-- | Gradient border with custom colors and angle
gradientBorderWith :: Number -> String -> String -> Number -> ItemBorder
gradientBorderWith width startColor endColor angle = 
  BorderGradientLinear (clampWidth width) startColor endColor (clampAngle angle)
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w
    clampAngle a
      | a < 0.0 = 0.0
      | a > 360.0 = 360.0
      | otherwise = a

-- | Animated dash border (marching ants)
animatedDashBorder :: ItemBorder
animatedDashBorder = BorderAnimatedDash 2.0 "#3B82F6" 1000.0

-- | Animated dash border with custom parameters
animatedDashBorderWith :: Number -> String -> Number -> ItemBorder
animatedDashBorderWith width color speed = 
  BorderAnimatedDash (clampWidth width) color (clampSpeed speed)
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w
    clampSpeed s
      | s < 100.0 = 100.0
      | s > 10000.0 = 10000.0
      | otherwise = s

-- | Dashed border (static)
dashedBorder :: Number -> String -> Number -> Number -> ItemBorder
dashedBorder width color dashLen gapLen = 
  BorderDashed (clampWidth width) color (clampDash dashLen) (clampDash gapLen)
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w
    clampDash d
      | d < 1.0 = 1.0
      | d > 50.0 = 50.0
      | otherwise = d

-- | Pulsing border (opacity animation)
pulseBorder :: Number -> String -> ItemBorder
pulseBorder width color = BorderPulse width color 0.3 1000.0

-- | Rainbow animated border
rainbowBorder :: Number -> Number -> ItemBorder
rainbowBorder width speed = BorderRainbow (clampWidth width) (clampSpeed speed)
  where
    clampWidth w
      | w < 0.0 = 0.0
      | w > 20.0 = 20.0
      | otherwise = w
    clampSpeed s
      | s < 500.0 = 500.0
      | s > 10000.0 = 10000.0
      | otherwise = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // item hover
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hover effect configuration for an item.
-- |
-- | Defines interactive behaviors when hovering over carousel items:
-- | - Audio playback (enter/leave/loop sounds)
-- | - Lottie animation triggers
-- | - Transform effects (scale, lift)
-- | - Combined effects
-- |
-- | ## Audio Hover
-- |
-- | Play sounds when mouse enters/leaves the item.
-- | Volume is normalized 0.0 to 1.0.
-- |
-- | ## Lottie Hover
-- |
-- | Start a Lottie animation on hover. Can play forward on enter
-- | and reverse on leave for smooth transitions.
-- |
-- | ## Transform Hover
-- |
-- | Scale, translate, or rotate the item on hover.
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Play bark sound at 50% volume
-- | dogCard = audioOnHover "/sounds/bark.mp3" 0.5
-- |
-- | -- Animate dog wagging tail
-- | animatedDog = lottieOnHover "/animations/dog-wag.json"
-- |
-- | -- Scale up with sound
-- | combined = combinedHoverWith 
-- |   (Just "/sounds/hover.mp3") 
-- |   (Just "/animations/pulse.json")
-- |   1.05
-- | ```
data ItemHover
  = HoverNone                                     -- ^ No hover effects
  | HoverAudio String Number                      -- ^ audioUrl, volume
  | HoverAudioEnterLeave String String Number     -- ^ enterUrl, leaveUrl, volume
  | HoverLottie String                            -- ^ lottieUrl
  | HoverLottieReverse String                     -- ^ lottieUrl (reverse on leave)
  | HoverScale Number Number                      -- ^ scale factor, duration ms
  | HoverLift Number Number                       -- ^ lift pixels, duration ms
  | HoverCombined ItemHoverConfig                 -- ^ Full configuration

-- | Full hover configuration for combined effects
type ItemHoverConfig =
  { audioUrl :: Maybe String           -- ^ Sound to play on enter
  , audioVolume :: Number              -- ^ Audio volume (0.0 to 1.0)
  , lottieUrl :: Maybe String          -- ^ Lottie animation URL
  , lottieReverse :: Boolean           -- ^ Reverse animation on leave
  , scaleFactor :: Number              -- ^ Scale multiplier (1.0 = no change)
  , liftPixels :: Number               -- ^ Vertical lift in pixels
  , durationMs :: Number               -- ^ Transition duration
  }

derive instance eqItemHover :: Eq ItemHover

instance showItemHover :: Show ItemHover where
  show HoverNone = "none"
  show (HoverAudio _ v) = "audio:" <> show v
  show (HoverAudioEnterLeave _ _ v) = "audio-enter-leave:" <> show v
  show (HoverLottie _) = "lottie"
  show (HoverLottieReverse _) = "lottie-reverse"
  show (HoverScale s _) = "scale:" <> show s
  show (HoverLift l _) = "lift:" <> show l <> "px"
  show (HoverCombined _) = "combined"

-- | Create hover with scale effect
itemHover :: Number -> Number -> ItemHover
itemHover scale duration = HoverScale (clampScale scale) (clampDuration duration)
  where
    clampScale s
      | s < 0.5 = 0.5
      | s > 2.0 = 2.0
      | otherwise = s
    clampDuration d
      | d < 0.0 = 0.0
      | d > 2000.0 = 2000.0
      | otherwise = d

-- | No hover effects
noItemHover :: ItemHover
noItemHover = HoverNone

-- | Play audio on hover enter
-- |
-- | - url: Audio file URL
-- | - volume: Playback volume (0.0 to 1.0)
audioOnHover :: String -> ItemHover
audioOnHover url = HoverAudio url 0.7

-- | Play audio with custom volume
audioOnHoverWith :: String -> Number -> ItemHover
audioOnHoverWith url volume = HoverAudio url (clampVolume volume)
  where
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v

-- | Play different sounds on enter and leave
audioOnHoverEnterLeave :: String -> String -> Number -> ItemHover
audioOnHoverEnterLeave enterUrl leaveUrl volume = 
  HoverAudioEnterLeave enterUrl leaveUrl (clampVolume volume)
  where
    clampVolume v
      | v < 0.0 = 0.0
      | v > 1.0 = 1.0
      | otherwise = v

-- | Start Lottie animation on hover
lottieOnHover :: String -> ItemHover
lottieOnHover = HoverLottie

-- | Lottie with reverse playback on leave
lottieOnHoverReverse :: String -> ItemHover
lottieOnHoverReverse = HoverLottieReverse

-- | Scale effect on hover
scaleOnHover :: Number -> ItemHover
scaleOnHover factor = HoverScale factor 200.0

-- | Lift effect on hover (vertical translate)
liftOnHover :: Number -> ItemHover
liftOnHover pixels = HoverLift pixels 200.0

-- | Combined hover effects
combinedHover :: ItemHover
combinedHover = HoverCombined defaultHoverConfig

-- | Combined hover with custom configuration
combinedHoverWith 
  :: Maybe String    -- ^ Audio URL
  -> Maybe String    -- ^ Lottie URL
  -> Number          -- ^ Scale factor
  -> ItemHover
combinedHoverWith audio lottie scale = HoverCombined
  { audioUrl: audio
  , audioVolume: 0.7
  , lottieUrl: lottie
  , lottieReverse: true
  , scaleFactor: scale
  , liftPixels: 0.0
  , durationMs: 200.0
  }

-- | Default hover configuration
defaultHoverConfig :: ItemHoverConfig
defaultHoverConfig =
  { audioUrl: Nothing
  , audioVolume: 0.7
  , lottieUrl: Nothing
  , lottieReverse: true
  , scaleFactor: 1.0
  , liftPixels: 0.0
  , durationMs: 200.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // item content
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content types for carousel items.
-- |
-- | Each carousel item wraps a piece of content:
-- | - Images with lazy loading and srcset support
-- | - Videos with autoplay and poster options
-- | - Card compounds (full Card component)
-- | - Lottie animations
-- | - Point clouds (3D data visualization)
-- | - Custom elements (user-provided)
-- |
-- | ## Image Options
-- |
-- | Images support:
-- | - url: Main image URL
-- | - alt: Accessibility text
-- | - srcset: Responsive image sources
-- | - loading: lazy or eager
-- |
-- | ## Video Options
-- |
-- | Videos support:
-- | - url: Video file URL
-- | - poster: Preview image URL
-- | - autoplay, loop, muted flags
data ItemContent
  = ContentImage ImageConfig                      -- ^ Image with configuration
  | ContentVideo VideoConfig                      -- ^ Video with configuration
  | ContentCard CardConfig                        -- ^ Card compound
  | ContentLottie String                          -- ^ Lottie animation URL
  | ContentPointCloud PointCloudConfig            -- ^ 3D point cloud
  | ContentCustom String                          -- ^ Custom element ID/type

-- | Image content configuration
type ImageConfig =
  { url :: String                   -- ^ Image URL
  , alt :: String                   -- ^ Alt text for accessibility
  , srcset :: Maybe String          -- ^ Responsive srcset
  , loading :: ImageLoading         -- ^ Loading strategy
  , objectFit :: ObjectFit          -- ^ How image fits container
  }

-- | Image loading strategy
data ImageLoading
  = LoadLazy                        -- ^ Lazy load when near viewport
  | LoadEager                       -- ^ Load immediately

derive instance eqImageLoading :: Eq ImageLoading

instance showImageLoading :: Show ImageLoading where
  show LoadLazy = "lazy"
  show LoadEager = "eager"

-- | Object fit mode
data ObjectFit
  = FitContain                      -- ^ Scale to fit, preserve aspect
  | FitCover                        -- ^ Scale to cover, may crop
  | FitFill                         -- ^ Stretch to fill
  | FitNone                         -- ^ No scaling
  | FitScaleDown                    -- ^ Scale down if needed

derive instance eqObjectFit :: Eq ObjectFit

instance showObjectFit :: Show ObjectFit where
  show FitContain = "contain"
  show FitCover = "cover"
  show FitFill = "fill"
  show FitNone = "none"
  show FitScaleDown = "scale-down"

-- | Video content configuration
type VideoConfig =
  { url :: String                   -- ^ Video URL
  , poster :: Maybe String          -- ^ Poster image URL
  , autoplay :: Boolean             -- ^ Autoplay on load
  , loop :: Boolean                 -- ^ Loop playback
  , muted :: Boolean                -- ^ Muted audio
  , controls :: Boolean             -- ^ Show video controls
  }

-- | Card content configuration
type CardConfig =
  { title :: Maybe String           -- ^ Card title
  , subtitle :: Maybe String        -- ^ Card subtitle
  , description :: Maybe String     -- ^ Card description
  , imageUrl :: Maybe String        -- ^ Card image
  , actionLabel :: Maybe String     -- ^ Action button label
  }

-- | Point cloud configuration
type PointCloudConfig =
  { dataUrl :: String               -- ^ Point cloud data URL (.ply, .pcd)
  , pointSize :: Number             -- ^ Point size in pixels
  , colorMode :: PointColorMode     -- ^ How points are colored
  }

-- | Point cloud coloring mode
data PointColorMode
  = ColorFromData                   -- ^ Use colors from data file
  | ColorUniform String             -- ^ Single color for all points
  | ColorByHeight                   -- ^ Color based on Y position
  | ColorByDepth                    -- ^ Color based on Z distance

derive instance eqPointColorMode :: Eq PointColorMode

instance showPointColorMode :: Show PointColorMode where
  show ColorFromData = "from-data"
  show (ColorUniform _) = "uniform"
  show ColorByHeight = "by-height"
  show ColorByDepth = "by-depth"

derive instance eqItemContent :: Eq ItemContent

instance showItemContent :: Show ItemContent where
  show (ContentImage _) = "image"
  show (ContentVideo _) = "video"
  show (ContentCard _) = "card"
  show (ContentLottie _) = "lottie"
  show (ContentPointCloud _) = "pointcloud"
  show (ContentCustom _) = "custom"

-- | Create image content with minimal config
imageContent :: String -> String -> ItemContent
imageContent url alt = ContentImage
  { url: url
  , alt: alt
  , srcset: Nothing
  , loading: LoadLazy
  , objectFit: FitCover
  }

-- | Create image with full configuration
imageContentWith :: ImageConfig -> ItemContent
imageContentWith = ContentImage

-- | Create video content with minimal config
videoContent :: String -> String -> ItemContent
videoContent url poster = ContentVideo
  { url: url
  , poster: Just poster
  , autoplay: false
  , loop: false
  , muted: true
  , controls: true
  }

-- | Create video with full configuration
videoContentWith :: VideoConfig -> ItemContent
videoContentWith = ContentVideo

-- | Create card content
cardContent :: ItemContent
cardContent = ContentCard
  { title: Nothing
  , subtitle: Nothing
  , description: Nothing
  , imageUrl: Nothing
  , actionLabel: Nothing
  }

-- | Create card with configuration
cardContentWith :: CardConfig -> ItemContent
cardContentWith = ContentCard

-- | Create Lottie content
lottieContent :: String -> ItemContent
lottieContent = ContentLottie

-- | Create point cloud content
pointCloudContent :: String -> ItemContent
pointCloudContent url = ContentPointCloud
  { dataUrl: url
  , pointSize: 2.0
  , colorMode: ColorFromData
  }

-- | Create custom element content
customContent :: String -> ItemContent
customContent = ContentCustom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // item config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete item configuration.
-- |
-- | Bundles all item styling options:
-- | - Shape clipping
-- | - Border styling
-- | - Hover effects
-- | - Sizing and spacing
-- |
-- | ## Sizing
-- |
-- | Items can have fixed or flexible sizing:
-- | - Fixed: Exact pixel dimensions
-- | - Flexible: Percentage or aspect ratio based
-- |
-- | ## Spacing
-- |
-- | Gap between items in the carousel is controlled at the carousel level,
-- | but items can have internal padding.
newtype ItemConfig = ItemConfig
  { shape :: ItemShape              -- ^ Shape clipping mask
  , border :: ItemBorder            -- ^ Border styling
  , hover :: ItemHover              -- ^ Hover effects
  , padding :: Number               -- ^ Internal padding (pixels)
  , aspectRatio :: Maybe Number     -- ^ Aspect ratio (width/height)
  , minWidth :: Maybe Number        -- ^ Minimum width (pixels)
  , maxWidth :: Maybe Number        -- ^ Maximum width (pixels)
  , className :: String             -- ^ Additional CSS class
  , ariaLabel :: String             -- ^ Accessibility label
  }

derive instance eqItemConfig :: Eq ItemConfig

instance showItemConfig :: Show ItemConfig where
  show (ItemConfig c) = 
    "ItemConfig(" <> show c.shape <> 
    ", " <> show c.border <> 
    ", " <> show c.hover <> ")"

-- | Create item config with all options
itemConfig
  :: { shape :: ItemShape
     , border :: ItemBorder
     , hover :: ItemHover
     , padding :: Number
     , aspectRatio :: Maybe Number
     , minWidth :: Maybe Number
     , maxWidth :: Maybe Number
     , className :: String
     , ariaLabel :: String
     }
  -> ItemConfig
itemConfig cfg = ItemConfig
  { shape: cfg.shape
  , border: cfg.border
  , hover: cfg.hover
  , padding: clampPadding cfg.padding
  , aspectRatio: cfg.aspectRatio
  , minWidth: cfg.minWidth
  , maxWidth: cfg.maxWidth
  , className: cfg.className
  , ariaLabel: cfg.ariaLabel
  }
  where
    clampPadding p
      | p < 0.0 = 0.0
      | p > 100.0 = 100.0
      | otherwise = p

-- | Default item config (no shape, no border, no hover)
defaultItemConfig :: ItemConfig
defaultItemConfig = ItemConfig
  { shape: ShapeNone
  , border: BorderNone
  , hover: HoverNone
  , padding: 0.0
  , aspectRatio: Nothing
  , minWidth: Nothing
  , maxWidth: Nothing
  , className: ""
  , ariaLabel: "Carousel item"
  }

-- | Image-optimized config (cover fit, subtle hover)
imageItemConfig :: ItemConfig
imageItemConfig = ItemConfig
  { shape: ShapeRectangle 8.0
  , border: BorderNone
  , hover: HoverScale 1.02 200.0
  , padding: 0.0
  , aspectRatio: Just 1.0
  , minWidth: Nothing
  , maxWidth: Nothing
  , className: "image-item"
  , ariaLabel: "Image"
  }

-- | Card-optimized config (padding, shadow feel)
cardItemConfig :: ItemConfig
cardItemConfig = ItemConfig
  { shape: ShapeRectangle 12.0
  , border: BorderSolid 1.0 "#E5E7EB"
  , hover: HoverLift 4.0 200.0
  , padding: 16.0
  , aspectRatio: Nothing
  , minWidth: Just 280.0
  , maxWidth: Just 400.0
  , className: "card-item"
  , ariaLabel: "Card"
  }

-- | Interactive config (audio + animation)
interactiveItemConfig :: String -> String -> ItemConfig
interactiveItemConfig audioUrl lottieUrl = ItemConfig
  { shape: ShapeRectangle 8.0
  , border: glowingBorder
  , hover: combinedHoverWith (Just audioUrl) (Just lottieUrl) 1.05
  , padding: 8.0
  , aspectRatio: Nothing
  , minWidth: Nothing
  , maxWidth: Nothing
  , className: "interactive-item"
  , ariaLabel: "Interactive item"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // item
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete carousel item.
-- |
-- | Combines content with configuration to create a fully-specified
-- | carousel item ready for rendering.
-- |
-- | ## Structure
-- |
-- | ```
-- | Item
-- |   ├─ content: ItemContent    (what to display)
-- |   └─ config: ItemConfig      (how to display it)
-- | ```
-- |
-- | ## Examples
-- |
-- | ```purescript
-- | -- Simple image item
-- | photoItem = simpleItem (imageContent "/photo.jpg" "Beach sunset")
-- |
-- | -- Interactive dog card
-- | dogItem = item
-- |   (imageContent "/dog.jpg" "Happy dog")
-- |   (interactiveItemConfig "/sounds/bark.mp3" "/animations/wag.json")
-- | ```
newtype Item = Item
  { content :: ItemContent          -- ^ What to display
  , config :: ItemConfig            -- ^ How to display it
  }

derive instance eqItem :: Eq Item

instance showItem :: Show Item where
  show (Item i) = 
    "Item(" <> show i.content <> ", " <> show i.config <> ")"

-- | Create complete item with content and config
item :: ItemContent -> ItemConfig -> Item
item content config = Item
  { content: content
  , config: config
  }

-- | Simple item (content only, default styling)
simpleItem :: ItemContent -> Item
simpleItem content = Item
  { content: content
  , config: defaultItemConfig
  }

-- | Image item with default image styling
imageItem :: String -> String -> Item
imageItem url alt = Item
  { content: imageContent url alt
  , config: imageItemConfig
  }

-- | Video item with default video styling
videoItem :: String -> String -> Item
videoItem url poster = Item
  { content: videoContent url poster
  , config: defaultItemConfig
  }

-- | Lottie item
lottieItem :: String -> Item
lottieItem url = Item
  { content: ContentLottie url
  , config: defaultItemConfig
  }

-- | Card item with title and image
cardItem :: String -> String -> Item
cardItem title imageUrl = Item
  { content: ContentCard
      { title: Just title
      , subtitle: Nothing
      , description: Nothing
      , imageUrl: Just imageUrl
      , actionLabel: Nothing
      }
  , config: cardItemConfig
  }

-- | Interactive item with audio and animation on hover
interactiveItem :: ItemContent -> String -> String -> Item
interactiveItem content audioUrl lottieUrl = Item
  { content: content
  , config: interactiveItemConfig audioUrl lottieUrl
  }
