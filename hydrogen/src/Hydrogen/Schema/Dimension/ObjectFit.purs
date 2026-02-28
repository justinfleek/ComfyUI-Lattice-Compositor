-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // dimension // objectfit
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ObjectFit — How replaced content (images, videos) fits within its container.
-- |
-- | ## Design Philosophy
-- |
-- | ObjectFit defines the behavior when content has a different aspect ratio
-- | than its container. This is a bounded enum (5 values) that maps directly
-- | to CSS object-fit.
-- |
-- | ## Values
-- |
-- | | Value     | Behavior                                       |
-- | |-----------|------------------------------------------------|
-- | | Fill      | Stretch to fill container (distorts aspect)    |
-- | | Contain   | Scale to fit inside, maintaining aspect ratio  |
-- | | Cover     | Scale to cover container, clipping overflow    |
-- | | None      | No scaling, content at natural size            |
-- | | ScaleDown | Like None, but shrink if larger than container |
-- |
-- | ## Use Cases
-- |
-- | - **Fill**: Background images where distortion is acceptable
-- | - **Contain**: Product images, thumbnails
-- | - **Cover**: Hero images, avatars, backgrounds
-- | - **None**: Icons at fixed size, pixel art
-- | - **ScaleDown**: Responsive images that shouldn't upscale
-- |
-- | ## At Billion-Agent Scale
-- |
-- | ObjectFit is a bounded enum (5 values). Agents can enumerate all possibilities.
-- | No strings, no invalid states.

module Hydrogen.Schema.Dimension.ObjectFit
  ( -- * ObjectFit Type
    ObjectFit
      ( Fill
      , Contain
      , Cover
      , None
      , ScaleDown
      )
  
  -- * Predicates
  , maintainsAspectRatio
  , canClip
  , canDistort
  
  -- * CSS Output
  , objectFitToCss
  , objectFitFromString
  
  -- * All Values
  , allObjectFits
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // objectfit
-- ═════════════════════════════════════════════════════════════════════════════

-- | How replaced content fits within its container.
-- |
-- | A bounded enum with exactly 5 values, matching CSS object-fit.
data ObjectFit
  = Fill           -- ^ Stretch to fill container (distorts aspect ratio)
  | Contain        -- ^ Scale to fit inside container, maintaining aspect ratio
  | Cover          -- ^ Scale to cover container, clipping overflow
  | None           -- ^ No scaling, content at natural size
  | ScaleDown      -- ^ Like None, but shrink if larger than container

derive instance eqObjectFit :: Eq ObjectFit
derive instance ordObjectFit :: Ord ObjectFit

instance showObjectFit :: Show ObjectFit where
  show Fill = "(ObjectFit Fill)"
  show Contain = "(ObjectFit Contain)"
  show Cover = "(ObjectFit Cover)"
  show None = "(ObjectFit None)"
  show ScaleDown = "(ObjectFit ScaleDown)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Does this fit mode maintain the content's aspect ratio?
-- |
-- | All modes except Fill maintain aspect ratio.
maintainsAspectRatio :: ObjectFit -> Boolean
maintainsAspectRatio Fill = false
maintainsAspectRatio _ = true

-- | Can this fit mode clip (hide) parts of the content?
-- |
-- | Cover mode clips overflow. None and ScaleDown can clip if content
-- | is larger than container and object-position isn't adjusted.
canClip :: ObjectFit -> Boolean
canClip Cover = true
canClip None = true
canClip ScaleDown = true
canClip _ = false

-- | Can this fit mode distort the content?
-- |
-- | Only Fill distorts (stretches) content.
canDistort :: ObjectFit -> Boolean
canDistort Fill = true
canDistort _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert ObjectFit to CSS object-fit value.
objectFitToCss :: ObjectFit -> String
objectFitToCss Fill = "fill"
objectFitToCss Contain = "contain"
objectFitToCss Cover = "cover"
objectFitToCss None = "none"
objectFitToCss ScaleDown = "scale-down"

-- | Parse ObjectFit from CSS string.
objectFitFromString :: String -> Maybe ObjectFit
objectFitFromString "fill" = Just Fill
objectFitFromString "contain" = Just Contain
objectFitFromString "cover" = Just Cover
objectFitFromString "none" = Just None
objectFitFromString "scale-down" = Just ScaleDown
objectFitFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // all values
-- ═════════════════════════════════════════════════════════════════════════════

-- | All ObjectFit values (for UI generation).
allObjectFits :: Array ObjectFit
allObjectFits = [Fill, Contain, Cover, None, ScaleDown]
