-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // geometry // clip-path
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ClipPath — Clipping region defined by a shape.
-- |
-- | ## Purpose
-- |
-- | A ClipPath defines a binary visibility mask — pixels inside the path
-- | are visible, pixels outside are hidden. Unlike Mask (which supports
-- | partial transparency), ClipPath is strictly on/off.
-- |
-- | ## Use Cases
-- |
-- | - Circular avatar images
-- | - Non-rectangular UI elements
-- | - Revealing/hiding content with animation
-- | - Complex shape cutouts
-- |
-- | ## Clip Sources
-- |
-- | - **Path**: SVG-style path data
-- | - **Circle**: Circular clip
-- | - **Ellipse**: Elliptical clip
-- | - **Polygon**: Polygonal clip
-- | - **Inset**: Rectangular inset with optional corner radius
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Path (path-based clipping)
-- | - Schema.Geometry.Circle (circular clips)
-- | - Schema.Geometry.Ellipse (elliptical clips)
-- | - Schema.Geometry.Polygon (polygon clips)

module Hydrogen.Schema.Geometry.ClipPath
  ( -- * Point Type
    Point
    
  -- * ClipPath Type
  , ClipPath(..)
  
  -- * Construction
  , clipPath
  , clipCircle
  , clipEllipse
  , clipPolygon
  , clipInset
  , clipNone
  
  -- * Accessors
  , isCircle
  , isEllipse
  , isPath
  , isPolygon
  , isInset
  , isNone
  
  -- * Transformations
  , translateClip
  , scaleClip
  
  -- * Presets
  , clipCircleCenter
  , clipOval
  , clipTriangle
  , clipHexagon
  , clipStar5
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (*)
  , (+)
  , (/)
  , (>=)
  , (==)
  , mod
  , negate
  )

import Data.Array (length, snoc) as Array
import Data.Int (toNumber) as Int
import Data.Number (pi, sin, cos)
import Hydrogen.Schema.Geometry.Path (Path)
import Hydrogen.Schema.Geometry.Path as Path

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // clippath type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clipping region defined by a shape.
-- |
-- | Each variant represents a different clip shape. The runtime
-- | interprets these to create the appropriate clipping region.
data ClipPath
  = ClipNone                    -- ^ No clipping (everything visible)
  | ClipPath Path               -- ^ Clip by SVG-style path
  | ClipCircle                  -- ^ Clip by circle
      { centerX :: Number       -- ^ Center X (0.0-1.0 = percentage, or pixels)
      , centerY :: Number       -- ^ Center Y
      , radius :: Number        -- ^ Radius
      }
  | ClipEllipse                 -- ^ Clip by ellipse
      { centerX :: Number       -- ^ Center X
      , centerY :: Number       -- ^ Center Y
      , radiusX :: Number       -- ^ Horizontal radius
      , radiusY :: Number       -- ^ Vertical radius
      }
  | ClipPolygon (Array Point)   -- ^ Clip by polygon (array of points)
  | ClipInset                   -- ^ Clip by inset rectangle
      { top :: Number           -- ^ Top inset
      , right :: Number         -- ^ Right inset
      , bottom :: Number        -- ^ Bottom inset
      , left :: Number          -- ^ Left inset
      , cornerRadius :: Number  -- ^ Corner radius (0 for sharp)
      }

-- | Simple point for polygon vertices
type Point = { x :: Number, y :: Number }

derive instance eqClipPath :: Eq ClipPath

instance showClipPath :: Show ClipPath where
  show ClipNone = "ClipNone"
  show (ClipPath p) = "(ClipPath " <> show (Path.commandCount p) <> " commands)"
  show (ClipCircle c) = "(ClipCircle cx=" <> show c.centerX <> " cy=" <> show c.centerY <> " r=" <> show c.radius <> ")"
  show (ClipEllipse e) = "(ClipEllipse cx=" <> show e.centerX <> " cy=" <> show e.centerY <> " rx=" <> show e.radiusX <> " ry=" <> show e.radiusY <> ")"
  show (ClipPolygon pts) = "(ClipPolygon " <> show (Array.length pts) <> " points)"
  show (ClipInset i) = "(ClipInset " <> show i.top <> " " <> show i.right <> " " <> show i.bottom <> " " <> show i.left <> ")"



-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a clip path from an SVG-style path
clipPath :: Path -> ClipPath
clipPath = ClipPath

-- | Create a circular clip
clipCircle :: { centerX :: Number, centerY :: Number, radius :: Number } -> ClipPath
clipCircle = ClipCircle

-- | Create an elliptical clip
clipEllipse :: { centerX :: Number, centerY :: Number, radiusX :: Number, radiusY :: Number } -> ClipPath
clipEllipse = ClipEllipse

-- | Create a polygon clip from points
clipPolygon :: Array Point -> ClipPath
clipPolygon = ClipPolygon

-- | Create an inset rectangular clip
clipInset :: { top :: Number, right :: Number, bottom :: Number, left :: Number, cornerRadius :: Number } -> ClipPath
clipInset = ClipInset

-- | No clipping (everything visible)
clipNone :: ClipPath
clipNone = ClipNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if this is a circular clip
isCircle :: ClipPath -> Boolean
isCircle (ClipCircle _) = true
isCircle _ = false

-- | Check if this is an elliptical clip
isEllipse :: ClipPath -> Boolean
isEllipse (ClipEllipse _) = true
isEllipse _ = false

-- | Check if this is a path clip
isPath :: ClipPath -> Boolean
isPath (ClipPath _) = true
isPath _ = false

-- | Check if this is a polygon clip
isPolygon :: ClipPath -> Boolean
isPolygon (ClipPolygon _) = true
isPolygon _ = false

-- | Check if this is an inset clip
isInset :: ClipPath -> Boolean
isInset (ClipInset _) = true
isInset _ = false

-- | Check if this is no clip
isNone :: ClipPath -> Boolean
isNone ClipNone = true
isNone _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate a clip by offset
-- |
-- | Only affects center-based clips (circle, ellipse).
-- | Path and polygon clips require path-level translation.
translateClip :: Number -> Number -> ClipPath -> ClipPath
translateClip _ _ ClipNone = ClipNone
translateClip _ _ c@(ClipPath _) = c  -- Would need path translation
translateClip dx dy (ClipCircle c) = ClipCircle
  { centerX: c.centerX + dx
  , centerY: c.centerY + dy
  , radius: c.radius
  }
translateClip dx dy (ClipEllipse e) = ClipEllipse
  { centerX: e.centerX + dx
  , centerY: e.centerY + dy
  , radiusX: e.radiusX
  , radiusY: e.radiusY
  }
translateClip _ _ c@(ClipPolygon _) = c  -- Would need point translation
translateClip _ _ c@(ClipInset _) = c  -- Insets are relative to bounds

-- | Scale a clip by factor
-- |
-- | Scales radius/dimensions but not center position.
scaleClip :: Number -> ClipPath -> ClipPath
scaleClip _ ClipNone = ClipNone
scaleClip _ c@(ClipPath _) = c  -- Would need path scaling
scaleClip factor (ClipCircle c) = ClipCircle
  { centerX: c.centerX
  , centerY: c.centerY
  , radius: c.radius * factor
  }
scaleClip factor (ClipEllipse e) = ClipEllipse
  { centerX: e.centerX
  , centerY: e.centerY
  , radiusX: e.radiusX * factor
  , radiusY: e.radiusY * factor
  }
scaleClip _ c@(ClipPolygon _) = c  -- Would need point scaling
scaleClip factor (ClipInset i) = ClipInset
  { top: i.top * factor
  , right: i.right * factor
  , bottom: i.bottom * factor
  , left: i.left * factor
  , cornerRadius: i.cornerRadius * factor
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Centered circle clip (50% radius)
-- |
-- | Perfect for circular avatar images.
clipCircleCenter :: ClipPath
clipCircleCenter = ClipCircle
  { centerX: 0.5  -- 50%
  , centerY: 0.5  -- 50%
  , radius: 0.5   -- 50% = fills container
  }

-- | Oval clip (ellipse filling container)
clipOval :: ClipPath
clipOval = ClipEllipse
  { centerX: 0.5
  , centerY: 0.5
  , radiusX: 0.5
  , radiusY: 0.5
  }

-- | Triangle clip (pointing up)
clipTriangle :: ClipPath
clipTriangle = ClipPolygon
  [ { x: 0.5, y: 0.0 }   -- Top center
  , { x: 1.0, y: 1.0 }   -- Bottom right
  , { x: 0.0, y: 1.0 }   -- Bottom left
  ]

-- | Hexagon clip
clipHexagon :: ClipPath
clipHexagon = ClipPolygon
  [ { x: 0.5, y: 0.0 }
  , { x: 1.0, y: 0.25 }
  , { x: 1.0, y: 0.75 }
  , { x: 0.5, y: 1.0 }
  , { x: 0.0, y: 0.75 }
  , { x: 0.0, y: 0.25 }
  ]

-- | 5-point star clip
clipStar5 :: ClipPath
clipStar5 = 
  let 
    points = generateStarPoints 5 0.5 0.5 0.5 0.2
  in ClipPolygon points

-- | Generate star polygon points
-- |
-- | Creates alternating outer and inner points.
generateStarPoints :: Int -> Number -> Number -> Number -> Number -> Array Point
generateStarPoints numPoints cx cy outerR innerR =
  let
    angleStep = 2.0 * pi / (2.0 * Int.toNumber numPoints)
    startAngle = pi * (-0.5)  -- Start at top
  in
    generatePoints 0 (numPoints * 2) angleStep startAngle cx cy outerR innerR []

generatePoints :: Int -> Int -> Number -> Number -> Number -> Number -> Number -> Number -> Array Point -> Array Point
generatePoints i total step start cx cy outerR innerR acc =
  if i >= total
    then acc
    else
      let
        angle = start + Int.toNumber i * step
        r = if (i `mod` 2) == 0 then outerR else innerR
        x = cx + r * cos angle
        y = cy + r * sin angle
        newAcc = Array.snoc acc { x, y }
      in generatePoints (i + 1) total step start cx cy outerR innerR newAcc
