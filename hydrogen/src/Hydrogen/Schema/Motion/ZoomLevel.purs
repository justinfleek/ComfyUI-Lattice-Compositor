-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // motion // zoomlevel
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Timeline zoom level for motion graphics editors.
-- |
-- | Represents the horizontal zoom of a timeline view, affecting how many
-- | frames are visible in the viewport and the pixel density of time.
-- |
-- | ## Scale
-- |
-- | - 1.0 = 100% (default, 1 frame per pixel at standard DPI)
-- | - 0.5 = 50% (zoomed out, more frames visible)
-- | - 2.0 = 200% (zoomed in, fewer frames visible)
-- |
-- | ## Constraints
-- |
-- | - Minimum: 0.01 (extremely zoomed out)
-- | - Maximum: 100.0 (extremely zoomed in)
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.ZoomLevel as Zoom
-- |
-- | -- Create zoom level
-- | zoom = Zoom.zoomLevel 1.5  -- 150%
-- |
-- | -- Zoom operations
-- | zoomedIn = Zoom.zoomIn zoom   -- 1.5 * 1.2 = 1.8
-- | zoomedOut = Zoom.zoomOut zoom -- 1.5 / 1.2 = 1.25
-- |
-- | -- Calculate pixels per frame
-- | ppf = Zoom.pixelsPerFrame zoom basePixelsPerFrame
-- | ```
module Hydrogen.Schema.Motion.ZoomLevel
  ( -- * Core Type
    ZoomLevel(..)
  
  -- * Constructors
  , zoomLevel
  , fromPercentage
  , default
  , fitToWidth
  
  -- * Accessors
  , toNumber
  , toPercentage
  
  -- * Operations
  , zoomIn
  , zoomOut
  , zoomTo
  , setZoom
  
  -- * Calculations
  , pixelsPerFrame
  , framesPerPixel
  , visibleFrames
  
  -- * Presets
  , zoomFit
  , zoom25
  , zoom50
  , zoom100
  , zoom200
  , zoom400
  
  -- * Constraints
  , minZoom
  , maxZoom
  , clamp
  
  -- * Bounds
  , bounds
  ) where

import Prelude hiding (clamp)

import Hydrogen.Schema.Bounded as Bounded
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // core type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Timeline zoom level
-- |
-- | Represents the scale factor for timeline display.
-- | Value of 1.0 means 100% (default zoom).
newtype ZoomLevel = ZoomLevel Number

derive instance eqZoomLevel :: Eq ZoomLevel
derive instance ordZoomLevel :: Ord ZoomLevel

instance showZoomLevel :: Show ZoomLevel where
  show (ZoomLevel n) = show (n * 100.0) <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Minimum allowed zoom level
minZoom :: ZoomLevel
minZoom = ZoomLevel 0.01

-- | Maximum allowed zoom level
maxZoom :: ZoomLevel
maxZoom = ZoomLevel 100.0

-- | Clamp zoom level to valid range
clamp :: ZoomLevel -> ZoomLevel
clamp (ZoomLevel z) = ZoomLevel (max 0.01 (min 100.0 z))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a zoom level from a scale factor
-- |
-- | Values are clamped to valid range [0.01, 100.0]
zoomLevel :: Number -> ZoomLevel
zoomLevel n = clamp (ZoomLevel n)

-- | Create zoom level from percentage (100 = 100% = 1.0)
fromPercentage :: Number -> ZoomLevel
fromPercentage pct = zoomLevel (pct / 100.0)

-- | Default zoom level (100%)
default :: ZoomLevel
default = ZoomLevel 1.0

-- | Calculate zoom level to fit given frames in given pixel width
-- |
-- | ```purescript
-- | zoom = fitToWidth (frames 1000.0) 800.0 10.0
-- | -- Returns zoom level where 1000 frames fit in 800 pixels
-- | -- with 10 pixels per frame at 100% zoom
-- | ```
fitToWidth :: Frames -> Number -> Number -> ZoomLevel
fitToWidth (Frames totalFrames) viewportWidth basePixelsPerFrame =
  let
    requiredZoom = viewportWidth / (totalFrames * basePixelsPerFrame)
  in
    zoomLevel requiredZoom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the numeric scale factor
toNumber :: ZoomLevel -> Number
toNumber (ZoomLevel n) = n

-- | Get zoom as percentage (1.0 -> 100.0)
toPercentage :: ZoomLevel -> Number
toPercentage (ZoomLevel n) = n * 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard zoom step multiplier
zoomStep :: Number
zoomStep = 1.2

-- | Zoom in by one step (multiply by 1.2)
zoomIn :: ZoomLevel -> ZoomLevel
zoomIn (ZoomLevel z) = zoomLevel (z * zoomStep)

-- | Zoom out by one step (divide by 1.2)
zoomOut :: ZoomLevel -> ZoomLevel
zoomOut (ZoomLevel z) = zoomLevel (z / zoomStep)

-- | Zoom to a specific percentage
zoomTo :: Number -> ZoomLevel -> ZoomLevel
zoomTo pct _ = fromPercentage pct

-- | Set zoom to exact value
setZoom :: Number -> ZoomLevel -> ZoomLevel
setZoom n _ = zoomLevel n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate pixels per frame at current zoom
-- |
-- | ```purescript
-- | ppf = pixelsPerFrame zoom 10.0
-- | -- At 200% zoom with base 10px/frame, returns 20px/frame
-- | ```
pixelsPerFrame :: ZoomLevel -> Number -> Number
pixelsPerFrame (ZoomLevel z) basePixelsPerFrame = z * basePixelsPerFrame

-- | Calculate frames per pixel at current zoom
-- |
-- | Inverse of pixelsPerFrame
framesPerPixel :: ZoomLevel -> Number -> Number
framesPerPixel (ZoomLevel z) basePixelsPerFrame = 1.0 / (z * basePixelsPerFrame)

-- | Calculate how many frames are visible in given viewport width
-- |
-- | ```purescript
-- | visible = visibleFrames zoom 800.0 10.0
-- | -- Returns number of frames visible in 800px wide viewport
-- | ```
visibleFrames :: ZoomLevel -> Number -> Number -> Frames
visibleFrames zoom viewportWidth basePixelsPerFrame =
  let
    ppf = pixelsPerFrame zoom basePixelsPerFrame
  in
    Frames (viewportWidth / ppf)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fit zoom (calculated per viewport)
zoomFit :: ZoomLevel
zoomFit = ZoomLevel 1.0

-- | 25% zoom
zoom25 :: ZoomLevel
zoom25 = ZoomLevel 0.25

-- | 50% zoom
zoom50 :: ZoomLevel
zoom50 = ZoomLevel 0.5

-- | 100% zoom (default)
zoom100 :: ZoomLevel
zoom100 = ZoomLevel 1.0

-- | 200% zoom
zoom200 :: ZoomLevel
zoom200 = ZoomLevel 2.0

-- | 400% zoom
zoom400 :: ZoomLevel
zoom400 = ZoomLevel 4.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for ZoomLevel
-- |
-- | Min: 0.01 (1%)
-- | Max: 100.0 (10000%)
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.01 100.0 "zoomLevel" "Timeline zoom scale (0.01-100.0)"
