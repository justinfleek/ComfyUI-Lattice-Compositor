-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // reactive // skeleton-config
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SkeletonConfig — Configuration atoms for skeleton loading states.
-- |
-- | ## Research Findings
-- |
-- | **Timing Constraints (Vercel, Linear, Frame.io):**
-- | - Skeletons should only appear for 1-3 seconds
-- | - If content loads in <200ms, skip skeleton entirely
-- | - If skeleton shows >3s, indicate slow connection
-- | - Never use skeletons on action components (buttons, inputs)
-- |
-- | **Content-Aware Shapes:**
-- | - Match skeleton shape to actual content
-- | - Use actual dimensions when known
-- | - Avoid layout shift when content loads
-- |
-- | **Animation Best Practices:**
-- | - Shimmer direction: left-to-right for LTR, right-to-left for RTL
-- | - Shimmer duration: 1.5-2 seconds per cycle
-- | - Pulse: 1-2 second cycle, ease-in-out
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Reactive.SkeletonConfig as Skeleton
-- |
-- | -- Configure skeleton timing
-- | config = Skeleton.defaultConfig
-- |   { minDisplayTime = 200.0   -- Always show at least 200ms
-- |   , maxDisplayTime = 3000.0  -- Warn after 3 seconds
-- |   }
-- | ```

module Hydrogen.Schema.Reactive.SkeletonConfig
  ( -- * Skeleton Timing
    SkeletonTiming(..)
  , skeletonTiming
  , defaultTiming
  , aggressiveTiming
  , patientTiming
  
  -- * Skeleton Shape
  , SkeletonShape(..)
  , rectangleShape
  , circleShape
  , textLineShape
  , paragraphShape
  , customShape
  
  -- * Content Type Validation
  , ContentType(..)
  , canShowSkeleton
  , skeletonWarning
  
  -- * Complete Skeleton Config
  , SkeletonConfig(..)
  , ShimmerDirection(..)
  , skeletonConfig
  , defaultConfig
  
  -- * Slow Connection Handling
  , SlowConnectionBehavior(..)
  , slowConnectionConfig
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (<=)
  , (>=)
  , (&&)
  )

import Data.Maybe (Maybe(Nothing, Just))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // skeleton timing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timing constraints for skeleton display
-- |
-- | ## Research-Based Constraints
-- |
-- | - **delayBeforeShow**: Skip skeleton if content loads faster than this
-- | - **minDisplayTime**: Once shown, display at least this long (prevents flash)
-- | - **maxDisplayTime**: Consider connection "slow" after this threshold
-- | - **animationDuration**: Single animation cycle duration
newtype SkeletonTiming = SkeletonTiming
  { delayBeforeShow :: Number    -- ^ Don't show if content loads within this time (ms)
  , minDisplayTime :: Number     -- ^ Minimum display time once shown (ms)
  , maxDisplayTime :: Number     -- ^ Threshold for slow connection warning (ms)
  , animationDuration :: Number  -- ^ Animation cycle duration (ms)
  }

derive instance eqSkeletonTiming :: Eq SkeletonTiming

instance showSkeletonTiming :: Show SkeletonTiming where
  show (SkeletonTiming t) = 
    "SkeletonTiming(delay:" <> show t.delayBeforeShow <> 
    "ms, min:" <> show t.minDisplayTime <> 
    "ms, max:" <> show t.maxDisplayTime <> "ms)"

-- | Create skeleton timing configuration
skeletonTiming 
  :: { delayBeforeShow :: Number
     , minDisplayTime :: Number
     , maxDisplayTime :: Number
     }
  -> SkeletonTiming
skeletonTiming cfg = SkeletonTiming
  { delayBeforeShow: cfg.delayBeforeShow
  , minDisplayTime: cfg.minDisplayTime
  , maxDisplayTime: cfg.maxDisplayTime
  , animationDuration: 1500.0  -- Default 1.5s cycle
  }

-- | Default timing (balanced UX)
-- |
-- | - 200ms delay (skip for fast loads)
-- | - 300ms minimum display (prevent flash)
-- | - 3000ms max before slow warning
defaultTiming :: SkeletonTiming
defaultTiming = SkeletonTiming
  { delayBeforeShow: 200.0
  , minDisplayTime: 300.0
  , maxDisplayTime: 3000.0
  , animationDuration: 1500.0
  }

-- | Aggressive timing (minimize perceived latency)
-- |
-- | - 100ms delay (show quickly)
-- | - 200ms minimum display
-- | - 2000ms max before warning
aggressiveTiming :: SkeletonTiming
aggressiveTiming = SkeletonTiming
  { delayBeforeShow: 100.0
  , minDisplayTime: 200.0
  , maxDisplayTime: 2000.0
  , animationDuration: 1200.0
  }

-- | Patient timing (tolerate slower connections)
-- |
-- | - 400ms delay (skip for most fast loads)
-- | - 500ms minimum display
-- | - 5000ms max before warning
patientTiming :: SkeletonTiming
patientTiming = SkeletonTiming
  { delayBeforeShow: 400.0
  , minDisplayTime: 500.0
  , maxDisplayTime: 5000.0
  , animationDuration: 2000.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // skeleton shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape of skeleton placeholder
-- |
-- | Matches skeleton shape to expected content to minimize layout shift.
data SkeletonShape
  = ShapeRectangle Number Number Number  -- ^ width, height, borderRadius (px)
  | ShapeCircle Number                   -- ^ diameter (px)
  | ShapeTextLine Number Number          -- ^ width, height (single line)
  | ShapeParagraph Int Number Number     -- ^ lines, lineHeight, lineGap
  | ShapeAvatar Number                   -- ^ Circle for user avatar
  | ShapeCard Number Number              -- ^ Card with header area
  | ShapeCustomPath String               -- ^ Custom SVG path

derive instance eqSkeletonShape :: Eq SkeletonShape

instance showSkeletonShape :: Show SkeletonShape where
  show (ShapeRectangle w h r) = 
    "Rectangle(" <> show w <> "x" <> show h <> ", r:" <> show r <> ")"
  show (ShapeCircle d) = "Circle(" <> show d <> ")"
  show (ShapeTextLine w h) = "TextLine(" <> show w <> "x" <> show h <> ")"
  show (ShapeParagraph lines _ _) = "Paragraph(" <> show lines <> " lines)"
  show (ShapeAvatar d) = "Avatar(" <> show d <> ")"
  show (ShapeCard w h) = "Card(" <> show w <> "x" <> show h <> ")"
  show (ShapeCustomPath _) = "CustomPath"

-- | Rectangle shape
rectangleShape :: Number -> Number -> Number -> SkeletonShape
rectangleShape = ShapeRectangle

-- | Circle shape
circleShape :: Number -> SkeletonShape
circleShape = ShapeCircle

-- | Text line shape (typical: 200x16 with 4px radius)
textLineShape :: Number -> SkeletonShape
textLineShape width = ShapeTextLine width 16.0

-- | Paragraph shape (multiple lines)
paragraphShape :: Int -> SkeletonShape
paragraphShape lines = ShapeParagraph lines 20.0 8.0

-- | Custom path shape (SVG path data)
customShape :: String -> SkeletonShape
customShape = ShapeCustomPath

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // content type validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content type classification for skeleton eligibility
-- |
-- | ## Research Finding
-- |
-- | Never show skeletons on:
-- | - Buttons (implies broken interaction)
-- | - Form inputs (confuses users)
-- | - Navigation (makes site feel broken)
-- |
-- | Always show skeletons on:
-- | - Content areas (articles, posts)
-- | - Media (images, videos)
-- | - Data displays (tables, charts)
data ContentType
  = ContentText        -- ^ Text content (articles, posts) - OK for skeleton
  | ContentMedia       -- ^ Images, videos - OK for skeleton
  | ContentData        -- ^ Tables, charts, lists - OK for skeleton
  | ContentCard        -- ^ Card components - OK for skeleton
  | ContentButton      -- ^ Interactive buttons - NO skeleton
  | ContentInput       -- ^ Form inputs - NO skeleton
  | ContentNavigation  -- ^ Navigation elements - NO skeleton
  | ContentAction      -- ^ Any action trigger - NO skeleton

derive instance eqContentType :: Eq ContentType

instance showContentType :: Show ContentType where
  show ContentText = "text"
  show ContentMedia = "media"
  show ContentData = "data"
  show ContentCard = "card"
  show ContentButton = "button"
  show ContentInput = "input"
  show ContentNavigation = "navigation"
  show ContentAction = "action"

-- | Check if content type is eligible for skeleton
canShowSkeleton :: ContentType -> Boolean
canShowSkeleton ContentText = true
canShowSkeleton ContentMedia = true
canShowSkeleton ContentData = true
canShowSkeleton ContentCard = true
canShowSkeleton ContentButton = false
canShowSkeleton ContentInput = false
canShowSkeleton ContentNavigation = false
canShowSkeleton ContentAction = false

-- | Get warning message if skeleton is inappropriate
skeletonWarning :: ContentType -> Maybe String
skeletonWarning ContentButton = 
  Just "Skeletons should not be used on buttons - use disabled state instead"
skeletonWarning ContentInput = 
  Just "Skeletons should not be used on inputs - use disabled state instead"
skeletonWarning ContentNavigation = 
  Just "Skeletons should not be used on navigation - show actual nav or nothing"
skeletonWarning ContentAction = 
  Just "Skeletons should not be used on action elements"
skeletonWarning _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // slow connection handling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Behavior when load time exceeds maxDisplayTime
data SlowConnectionBehavior
  = ShowWarningText String      -- ^ Display "Taking longer than expected..."
  | ShowProgressBar             -- ^ Switch to indeterminate progress bar
  | ShowRetryButton             -- ^ Offer retry option
  | KeepAnimating               -- ^ Continue skeleton animation (default)
  | FadeToStatic                -- ^ Stop animation, show static placeholder

derive instance eqSlowConnectionBehavior :: Eq SlowConnectionBehavior

instance showSlowConnectionBehavior :: Show SlowConnectionBehavior where
  show (ShowWarningText msg) = "warning:" <> msg
  show ShowProgressBar = "progress-bar"
  show ShowRetryButton = "retry"
  show KeepAnimating = "keep-animating"
  show FadeToStatic = "fade-static"

-- | Create slow connection config with warning text
slowConnectionConfig :: String -> SlowConnectionBehavior
slowConnectionConfig = ShowWarningText

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // skeleton config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete skeleton loading configuration
-- |
-- | Combines timing, shape, and behavior into a single composable type.
newtype SkeletonConfig = SkeletonConfig
  { timing :: SkeletonTiming
  , shape :: SkeletonShape
  , contentType :: ContentType
  , slowBehavior :: SlowConnectionBehavior
  , shimmerDirection :: ShimmerDirection
  , respectReducedMotion :: Boolean  -- ^ Honor prefers-reduced-motion
  }

-- | Shimmer animation direction
data ShimmerDirection
  = ShimmerLTR   -- ^ Left to right (default for LTR languages)
  | ShimmerRTL   -- ^ Right to left (for RTL languages)
  | ShimmerTTB   -- ^ Top to bottom
  | ShimmerBTT   -- ^ Bottom to top

derive instance eqShimmerDirection :: Eq ShimmerDirection

instance showShimmerDirection :: Show ShimmerDirection where
  show ShimmerLTR = "ltr"
  show ShimmerRTL = "rtl"
  show ShimmerTTB = "ttb"
  show ShimmerBTT = "btt"

derive instance eqSkeletonConfig :: Eq SkeletonConfig

instance showSkeletonConfig :: Show SkeletonConfig where
  show (SkeletonConfig c) = 
    "SkeletonConfig(" <> show c.timing <> ", " <> show c.shape <> ")"

-- | Create skeleton config
skeletonConfig 
  :: { shape :: SkeletonShape
     , contentType :: ContentType
     }
  -> SkeletonConfig
skeletonConfig cfg = SkeletonConfig
  { timing: defaultTiming
  , shape: cfg.shape
  , contentType: cfg.contentType
  , slowBehavior: ShowWarningText "Taking longer than expected..."
  , shimmerDirection: ShimmerLTR
  , respectReducedMotion: true
  }

-- | Default skeleton config (text line)
defaultConfig :: SkeletonConfig
defaultConfig = SkeletonConfig
  { timing: defaultTiming
  , shape: textLineShape 200.0
  , contentType: ContentText
  , slowBehavior: ShowWarningText "Taking longer than expected..."
  , shimmerDirection: ShimmerLTR
  , respectReducedMotion: true
  }
