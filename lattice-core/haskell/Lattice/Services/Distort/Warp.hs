{-|
  Lattice.Services.Distort.Warp - Warp Distortion Mathematics

  Pure mathematical functions for warp distortions:
  - Arc warp (bend along parabola)
  - Bulge warp (inflate/deflate)
  - Wave warp (sinusoidal displacement)
  - Fisheye warp (barrel/pincushion)
  - Twist warp (rotational distortion)

  Source: ui/src/services/effects/distortRenderer.ts (lines 273-407)
-}

module Lattice.Services.Distort.Warp
  ( WarpStyle(..)
  , WarpResult(..)
  , normalizeCoord
  , arcWarpX
  , bulgeWarp
  , waveWarp
  , fisheyeWarp
  , twistWarp
  , applyWarp
  , applyHVDistortion
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Warp style type
data WarpStyle
  = Arc       -- ^ Bend along parabolic curve
  | Bulge     -- ^ Inflate/deflate from center
  | Wave      -- ^ Sinusoidal displacement
  | Fisheye   -- ^ Barrel/pincushion distortion
  | Twist     -- ^ Rotational swirl
  deriving (Show, Eq, Enum, Bounded)

-- | Warp result: displaced source coordinates
data WarpResult = WarpResult
  { wrSrcX :: !Double
  , wrSrcY :: !Double
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Coordinate Normalization
-- ────────────────────────────────────────────────────────────────────────────

-- | Normalize pixel coordinate to -1 to 1 range.
--
--   @param coord Pixel coordinate (x or y)
--   @param center Center coordinate (width/2 or height/2)
--   @return Normalized coordinate in [-1, 1]
normalizeCoord :: Double -> Double -> Double
normalizeCoord coord center
  | center < 0.0001 = 0.0
  | otherwise = (coord - center) / center

-- ────────────────────────────────────────────────────────────────────────────
-- Arc Warp
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate arc warp displacement.
--
--   Arc warp bends the image along a parabolic curve.
--   Displacement is proportional to ny² (stronger at top/bottom).
--
--   @param x Pixel X
--   @param nx Normalized X (-1 to 1)
--   @param ny Normalized Y (-1 to 1)
--   @param centerX Image center X
--   @param bend Bend amount (-1 to 1, from -100 to 100 percent)
--   @return Displaced X coordinate
arcWarpX :: Double -> Double -> Double -> Double -> Double -> Double
arcWarpX x nx ny centerX bend =
  let arcBend = bend * ny * ny
  in x + arcBend * centerX * nx

-- ────────────────────────────────────────────────────────────────────────────
-- Bulge Warp
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate bulge warp displacement.
--
--   Bulge warp inflates or deflates the image from center.
--   Inside unit circle, pixels are scaled toward/away from center.
--
--   @param x Pixel X
--   @param y Pixel Y
--   @param centerX Center X
--   @param centerY Center Y
--   @param r Distance from center (normalized)
--   @param bend Bend amount (-1 to 1)
--   @return (srcX, srcY) displaced coordinates
bulgeWarp :: Double -> Double -> Double -> Double -> Double -> Double -> WarpResult
bulgeWarp x y centerX centerY r bend
  | r >= 1.0 = WarpResult { wrSrcX = x, wrSrcY = y }
  | otherwise =
      let factor = 1.0 + bend * (1.0 - r * r)
          -- Avoid division by zero
          safeFactor = if abs factor < 0.0001 then 0.0001 else factor
      in WarpResult
          { wrSrcX = centerX + (x - centerX) / safeFactor
          , wrSrcY = centerY + (y - centerY) / safeFactor
          }

-- ────────────────────────────────────────────────────────────────────────────
-- Wave Warp
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate wave warp displacement.
--
--   Wave warp applies sinusoidal displacement in both directions.
--
--   @param x Pixel X
--   @param y Pixel Y
--   @param nx Normalized X
--   @param ny Normalized Y
--   @param width Image width
--   @param height Image height
--   @param bend Wave amplitude (-1 to 1)
--   @return (srcX, srcY) displaced coordinates
waveWarp :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> WarpResult
waveWarp x y nx ny width height bend =
  let waveAmplitude = bend * 0.1  -- 10% of dimension at full bend
  in WarpResult
      { wrSrcX = x + sin (ny * pi * 2.0) * waveAmplitude * width
      , wrSrcY = y + sin (nx * pi * 2.0) * waveAmplitude * height
      }

-- ────────────────────────────────────────────────────────────────────────────
-- Fisheye Warp
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate fisheye warp displacement.
--
--   Fisheye applies barrel (bend > 0) or pincushion (bend < 0) distortion.
--   Uses polar coordinates with power function on radius.
--
--   @param x Pixel X
--   @param y Pixel Y
--   @param nx Normalized X
--   @param ny Normalized Y
--   @param centerX Center X
--   @param centerY Center Y
--   @param r Distance from center (normalized)
--   @param bend Bend amount (-1 to 1)
--   @return (srcX, srcY) displaced coordinates
fisheyeWarp :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double -> WarpResult
fisheyeWarp x y nx ny centerX centerY r bend
  | r <= 0.0 = WarpResult { wrSrcX = x, wrSrcY = y }
  | r >= 1.0 = WarpResult { wrSrcX = x, wrSrcY = y }
  | otherwise =
      let theta = atan2 ny nx
          -- Power distortion: r^(1 + bend)
          newR = r ** (1.0 + bend)
      in WarpResult
          { wrSrcX = centerX + newR * cos theta * centerX
          , wrSrcY = centerY + newR * sin theta * centerY
          }

-- ────────────────────────────────────────────────────────────────────────────
-- Twist Warp
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate twist warp displacement.
--
--   Twist warp rotates pixels around center, with rotation angle
--   decreasing with distance (stronger twist at center).
--
--   @param x Pixel X
--   @param y Pixel Y
--   @param nx Normalized X
--   @param ny Normalized Y
--   @param centerX Center X
--   @param centerY Center Y
--   @param r Distance from center (normalized)
--   @param bend Twist amount (-1 to 1, maps to rotation in radians)
--   @return (srcX, srcY) displaced coordinates
twistWarp :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double -> WarpResult
twistWarp _ _ nx ny centerX centerY r bend =
  let angle = bend * pi * (1.0 - r)
      cosA = cos angle
      sinA = sin angle
  in WarpResult
      { wrSrcX = centerX + (nx * cosA - ny * sinA) * centerX
      , wrSrcY = centerY + (nx * sinA + ny * cosA) * centerY
      }

-- ────────────────────────────────────────────────────────────────────────────
-- Combined Warp
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply warp distortion based on style.
--
--   @param style Warp style
--   @param x Pixel X
--   @param y Pixel Y
--   @param width Image width
--   @param height Image height
--   @param bend Bend amount (-1 to 1)
--   @return (srcX, srcY) displaced coordinates
applyWarp :: WarpStyle -> Double -> Double -> Double -> Double -> Double -> WarpResult
applyWarp style x y width height bend =
  let centerX = width / 2.0
      centerY = height / 2.0
      nx = normalizeCoord x centerX
      ny = normalizeCoord y centerY
      r = sqrt (nx * nx + ny * ny)
  in case style of
      Arc     -> WarpResult { wrSrcX = arcWarpX x nx ny centerX bend, wrSrcY = y }
      Bulge   -> bulgeWarp x y centerX centerY r bend
      Wave    -> waveWarp x y nx ny width height bend
      Fisheye -> fisheyeWarp x y nx ny centerX centerY r bend
      Twist   -> twistWarp x y nx ny centerX centerY r bend

-- ────────────────────────────────────────────────────────────────────────────
-- Horizontal/Vertical Distortion
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply additional horizontal and vertical distortion.
--
--   @param srcX Current source X
--   @param srcY Current source Y
--   @param nx Normalized X
--   @param ny Normalized Y
--   @param centerX Center X
--   @param centerY Center Y
--   @param hDistort Horizontal distortion (-1 to 1)
--   @param vDistort Vertical distortion (-1 to 1)
--   @return (srcX, srcY) with additional distortion
applyHVDistortion :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double -> WarpResult
applyHVDistortion srcX srcY nx ny centerX centerY hDistort vDistort =
  WarpResult
    { wrSrcX = srcX + hDistort * centerX * (1.0 - ny * ny)
    , wrSrcY = srcY + vDistort * centerY * (1.0 - nx * nx)
    }
