-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // elevation // perspective
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Perspective atoms — 3D perspective projection parameters.
-- |
-- | ## CSS Perspective Model
-- |
-- | CSS perspective simulates viewing a 2D plane from a distance in 3D space:
-- |
-- | - **Perspective distance**: How far the viewer is from the z=0 plane.
-- |   Smaller values = more extreme perspective distortion.
-- |   Larger values = flatter, more orthographic appearance.
-- |
-- | - **Perspective origin**: The vanishing point (center of projection).
-- |   Default is center (50%, 50%). Moving it shifts where parallel lines
-- |   appear to converge.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Elevation.Perspective as P
-- |
-- | -- Set perspective distance (in pixels)
-- | distance = P.perspective 1000.0
-- |
-- | -- Set perspective origin (percentages)
-- | origin = P.perspectiveOrigin 
-- |   { x: P.perspOrigX 50.0
-- |   , y: P.perspOrigY 25.0  -- vanishing point in upper half
-- |   }
-- |
-- | -- Convert to CSS
-- | css = P.toLegacyCss distance  -- "1000px"
-- | originCss = P.originToLegacyCss origin  -- "50% 25%"
-- | ```

module Hydrogen.Schema.Elevation.Perspective
  ( -- * Perspective Distance (Atom)
    Perspective
  , perspective
  , noPerspective
  , getPerspective
  , scalePerspective
  
  -- * Perspective Origin (Atoms)
  , PerspOrigX
  , PerspOrigY
  , perspOrigX
  , perspOrigY
  , centerOriginX
  , centerOriginY
  , getPerspOrigX
  , getPerspOrigY
  
  -- * Perspective Origin (Molecule)
  , PerspectiveOrigin
  , perspectiveOrigin
  , centerOrigin
  , getOriginX
  , getOriginY
  , withOriginX
  , withOriginY
  
  -- * Conversion (Legacy CSS, not FFI)
  , toLegacyCss
  , originToLegacyCss
  
  -- * Predicates
  , hasPerspective
  , isDefaultOrigin
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , (&&)
  , (==)
  , (<)
  , (>)
  , (*)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // perspective distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perspective distance in pixels.
-- |
-- | This is the distance from the viewer to the z=0 plane. Values are clamped
-- | to non-negative (negative perspective is physically meaningless).
-- |
-- | - 0 or "none": No perspective (flat projection)
-- | - 100-500: Extreme perspective (dramatic distortion)
-- | - 500-1500: Normal perspective (natural 3D appearance)
-- | - 1500+: Subtle perspective (nearly orthographic)
newtype Perspective = Perspective Number

derive instance eqPerspective :: Eq Perspective
derive instance ordPerspective :: Ord Perspective

instance showPerspective :: Show Perspective where
  show (Perspective n) = "Perspective " <> show n

-- | Create a perspective distance
-- |
-- | Value is clamped to >= 0. Use `noPerspective` for flat projection.
perspective :: Number -> Perspective
perspective n = Perspective (clampNonNegative n)

-- | No perspective (flat projection)
-- |
-- | Renders as "none" in CSS.
noPerspective :: Perspective
noPerspective = Perspective 0.0

-- | Extract the perspective distance value
getPerspective :: Perspective -> Number
getPerspective (Perspective n) = n

-- | Scale perspective by a factor
-- |
-- | Useful for responsive scaling. Result clamped to >= 0.
scalePerspective :: Number -> Perspective -> Perspective
scalePerspective factor (Perspective n) = Perspective (clampNonNegative (n * factor))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // perspective origin x
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perspective origin X coordinate (percentage, 0-100).
-- |
-- | Represents the horizontal position of the vanishing point:
-- | - 0%: Left edge
-- | - 50%: Center (default)
-- | - 100%: Right edge
newtype PerspOrigX = PerspOrigX Number

derive instance eqPerspOrigX :: Eq PerspOrigX
derive instance ordPerspOrigX :: Ord PerspOrigX

instance showPerspOrigX :: Show PerspOrigX where
  show (PerspOrigX n) = "PerspOrigX " <> show n

-- | Create perspective origin X coordinate
-- |
-- | Value is clamped to 0-100%.
perspOrigX :: Number -> PerspOrigX
perspOrigX n = PerspOrigX (clampPercentage n)

-- | Center origin X (50%)
centerOriginX :: PerspOrigX
centerOriginX = PerspOrigX 50.0

-- | Extract the X percentage
getPerspOrigX :: PerspOrigX -> Number
getPerspOrigX (PerspOrigX n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // perspective origin y
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perspective origin Y coordinate (percentage, 0-100).
-- |
-- | Represents the vertical position of the vanishing point:
-- | - 0%: Top edge
-- | - 50%: Center (default)
-- | - 100%: Bottom edge
newtype PerspOrigY = PerspOrigY Number

derive instance eqPerspOrigY :: Eq PerspOrigY
derive instance ordPerspOrigY :: Ord PerspOrigY

instance showPerspOrigY :: Show PerspOrigY where
  show (PerspOrigY n) = "PerspOrigY " <> show n

-- | Create perspective origin Y coordinate
-- |
-- | Value is clamped to 0-100%.
perspOrigY :: Number -> PerspOrigY
perspOrigY n = PerspOrigY (clampPercentage n)

-- | Center origin Y (50%)
centerOriginY :: PerspOrigY
centerOriginY = PerspOrigY 50.0

-- | Extract the Y percentage
getPerspOrigY :: PerspOrigY -> Number
getPerspOrigY (PerspOrigY n) = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // perspective origin molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perspective origin — combined X and Y coordinates.
-- |
-- | This molecule combines the two origin atoms into a single 2D point
-- | representing where parallel lines converge in perspective projection.
type PerspectiveOrigin =
  { x :: PerspOrigX
  , y :: PerspOrigY
  }

-- | Create a perspective origin from X and Y atoms
perspectiveOrigin :: { x :: PerspOrigX, y :: PerspOrigY } -> PerspectiveOrigin
perspectiveOrigin = identity

-- | Center origin (50%, 50%) — the default
centerOrigin :: PerspectiveOrigin
centerOrigin = 
  { x: centerOriginX
  , y: centerOriginY
  }

-- | Extract X coordinate from origin
getOriginX :: PerspectiveOrigin -> PerspOrigX
getOriginX o = o.x

-- | Extract Y coordinate from origin
getOriginY :: PerspectiveOrigin -> PerspOrigY
getOriginY o = o.y

-- | Update X coordinate of origin
withOriginX :: PerspOrigX -> PerspectiveOrigin -> PerspectiveOrigin
withOriginX x o = o { x = x }

-- | Update Y coordinate of origin
withOriginY :: PerspOrigY -> PerspectiveOrigin -> PerspectiveOrigin
withOriginY y o = o { y = y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert perspective distance to CSS string.
-- |
-- | Returns "none" for noPerspective, otherwise "<value>px".
-- | NOT an FFI boundary — pure string generation.
toLegacyCss :: Perspective -> String
toLegacyCss (Perspective 0.0) = "none"
toLegacyCss (Perspective n) = showNumber n <> "px"

-- | Convert perspective origin to CSS string.
-- |
-- | Format: "<x>% <y>%"
-- | NOT an FFI boundary — pure string generation.
originToLegacyCss :: PerspectiveOrigin -> String
originToLegacyCss o =
  let
    PerspOrigX x = o.x
    PerspOrigY y = o.y
  in
    showNumber x <> "% " <> showNumber y <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if perspective is set (not "none")
hasPerspective :: Perspective -> Boolean
hasPerspective (Perspective n) = n > 0.0

-- | Check if origin is the default center (50%, 50%)
isDefaultOrigin :: PerspectiveOrigin -> Boolean
isDefaultOrigin o =
  let
    PerspOrigX x = o.x
    PerspOrigY y = o.y
  in
    x == 50.0 && y == 50.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identity function (for record passthrough)
identity :: forall a. a -> a
identity x = x

-- | Clamp to non-negative
clampNonNegative :: Number -> Number
clampNonNegative n = if n < 0.0 then 0.0 else n

-- | Clamp to 0-100 percentage range
clampPercentage :: Number -> Number
clampPercentage n
  | n < 0.0 = 0.0
  | n > 100.0 = 100.0
  | true = n

-- | Show number cleanly for CSS output
showNumber :: Number -> String
showNumber n = show n
