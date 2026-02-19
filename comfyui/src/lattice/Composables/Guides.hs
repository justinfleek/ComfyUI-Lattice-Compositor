-- |
-- Module      : Lattice.Composables.Guides
-- Description : Ruler/guide types and pure logic (add, remove, style)
--
-- Ported from ui/src/composables/useGuides.ts
-- Pure data and style computation; no Vue/DOM/events.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.Guides
  ( -- Types
    Guide(..)
  , GuideOrientation(..)
  , GuideContextMenu(..)
  , GuideStyle(..)
  -- Operations
  , addGuide
  , removeGuide
  , clearGuides
  , updateGuidePosition
  , getGuideStyle
  ) where

import Data.Text (Text)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

data GuideOrientation
  = Horizontal
  | Vertical
  deriving (Eq, Show)

-- | Single ruler guide (id, orientation, position in px)
data Guide = Guide
  { guideId :: Text
  , guideOrientation :: GuideOrientation
  , guidePosition :: Double
  }
  deriving (Eq, Show)

-- | Context menu state (UI uses this; we only define shape)
data GuideContextMenu = GuideContextMenu
  { guideContextMenuVisible :: Bool
  , guideContextMenuX :: Double
  , guideContextMenuY :: Double
  , guideContextMenuGuideId :: Maybe Text
  }
  deriving (Eq, Show)

-- | Style for rendering a guide (CSS-like; UI converts to actual CSS)
data GuideStyle
  = HorizontalStyle
      { gsLeft :: Double
      , gsRight :: Double
      , gsTop :: Double
      , gsHeight :: Double
      , gsCursor :: Text
      }
  | VerticalStyle
      { gsTop :: Double
      , gsBottom :: Double
      , gsLeft :: Double
      , gsWidth :: Double
      , gsCursor :: Text
      }
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Add a guide with the given id (id generation is impure; caller provides it)
addGuide :: Text -> GuideOrientation -> Double -> [Guide] -> [Guide]
addGuide gid orient pos gs =
  Guide { guideId = gid, guideOrientation = orient, guidePosition = pos } : gs

-- | Remove guide by id
removeGuide :: Text -> [Guide] -> [Guide]
removeGuide gid = filter (\g -> guideId g /= gid)

-- | Remove all guides
clearGuides :: [Guide] -> [Guide]
clearGuides _ = []

-- | Update position of guide by id. Returns Nothing if id not found.
updateGuidePosition :: Text -> Double -> [Guide] -> Maybe [Guide]
updateGuidePosition gid pos gs =
  let go [] = Nothing
      go (g : rest)
        | guideId g == gid =
            Just (g { guidePosition = pos } : rest)
        | otherwise =
            (g :) <$> go rest
  in go gs

-- | Hit area half-size (5px each side of line → 11px total height/width)
guideHitHalf :: Double
guideHitHalf = 5

-- | Build style for a guide (matches TS getGuideStyle)
getGuideStyle :: Guide -> GuideStyle
getGuideStyle g =
  let p = guidePosition g
      topPx = p - guideHitHalf
      heightPx = 11
  in case guideOrientation g of
    Horizontal ->
      HorizontalStyle
        { gsLeft = 0
        , gsRight = 0
        , gsTop = topPx
        , gsHeight = heightPx
        , gsCursor = "ns-resize"
        }
    Vertical ->
      VerticalStyle
        { gsTop = 0
        , gsBottom = 0
        , gsLeft = p - guideHitHalf
        , gsWidth = 11
        , gsCursor = "ew-resize"
        }
