-- |
-- Module      : Lattice.Utils.Interpolation
-- Description : Pure interpolation functions for keyframe animation
-- 
-- Migrated from ui/src/services/interpolation.ts
-- Core pure functions for bezier curves, easing, and value interpolation
-- Note: Caching and expressions handled separately
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.Interpolation
  ( -- Bezier functions
    bezierPoint
  , bezierDerivative
  , cubicBezierEasing
  , normalizeBezierHandles
  -- Keyframe search
  , findKeyframeIndex
  -- Value interpolation
  , interpolateNumber
  , interpolateVec2
  , interpolateVec3
  -- Color interpolation
  , normalizeHexColor
  , parseHexComponent
  , interpolateColor
  -- Helper functions
  , getValueDelta
  , getValueDeltaVec2
  ) where

import Data.Bits ((.|.), shiftL)
import Data.Char (isHexDigit)
import Data.List (splitAt)
import Numeric (readHex, showHex)
import Lattice.Types.Animation
  ( BezierHandle(..)
  , Keyframe(..)
  )
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  )
import Lattice.Utils.NumericSafety
  ( safeLerp
  , clamp01
  , ensureFinite
  , safeSqrt
  )
import Data.Text (Text)
import qualified Data.Text as T

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // bezier // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Cubic bezier point calculation
-- Pure function: p(t) = (1-t)³p₀ + 3(1-t)²tp₁ + 3(1-t)t²p₂ + t³p₃
bezierPoint :: Double -> Double -> Double -> Double -> Double -> Double
bezierPoint t p0 p1 p2 p3 =
  let mt = 1 - t
  in mt * mt * mt * p0 +
     3 * mt * mt * t * p1 +
     3 * mt * t * t * p2 +
     t * t * t * p3

-- | Cubic bezier derivative
-- Pure function: p'(t) = 3(1-t)²(p₁-p₀) + 6(1-t)t(p₂-p₁) + 3t²(p₃-p₂)
bezierDerivative :: Double -> Double -> Double -> Double -> Double -> Double
bezierDerivative t p0 p1 p2 p3 =
  let mt = 1 - t
  in 3 * mt * mt * (p1 - p0) +
     6 * mt * t * (p2 - p1) +
     3 * t * t * (p3 - p2)

-- | Normalize bezier handles from absolute frame/value offsets to 0-1 space
-- Pure function (no caching - caller can cache if needed)
normalizeBezierHandles ::
  BezierHandle ->
  BezierHandle ->
  Double ->  -- frameDuration
  Double ->  -- valueDelta
  (Double, Double, Double, Double)  -- (x1, y1, x2, y2)
normalizeBezierHandles outHandle inHandle frameDuration valueDelta =
  let x1 = if frameDuration > 0
             then abs (bezierHandleFrame outHandle) / frameDuration
             else 0.33
      y1 = if valueDelta /= 0
             then bezierHandleValue outHandle / valueDelta
             else 0.33
      x2 = if frameDuration > 0
             then 1 - abs (bezierHandleFrame inHandle) / frameDuration
             else 0.67
      y2 = if valueDelta /= 0
             then 1 - bezierHandleValue inHandle / valueDelta
             else 0.67
  in (x1, y1, x2, y2)

-- | Cubic bezier easing function
-- Converts absolute frame/value handle offsets to normalized 0-1 space
-- Uses Newton-Raphson iteration to find t for given x
cubicBezierEasing ::
  Double ->  -- t (linear time 0-1)
  BezierHandle ->  -- outHandle
  BezierHandle ->  -- inHandle
  Double ->  -- frameDuration
  Double ->  -- valueDelta
  Double  -- Eased time (0-1, can overshoot)
cubicBezierEasing t outHandle inHandle frameDuration valueDelta
  | not (bezierHandleEnabled outHandle) && not (bezierHandleEnabled inHandle) = t
  | otherwise =
      let (x1, y1, x2, y2) = normalizeBezierHandles outHandle inHandle frameDuration valueDelta
          -- Find t value for given x using Newton-Raphson iteration
          epsilon = 1e-6
          maxIterations = 8
          newtonRaphson guess iter
            | iter >= maxIterations = guess
            | otherwise =
                let currentX = bezierPoint guess 0 x1 x2 1
                    error = currentX - t
                in if abs error < epsilon
                     then guess
                     else let currentSlope = bezierDerivative guess 0 x1 x2 1
                          in if abs currentSlope < epsilon
                               then guess
                               else let newGuess = guess - error / currentSlope
                                        clampedGuess = max 0 (min 1 newGuess)
                                    in newtonRaphson clampedGuess (iter + 1)
          guessT = newtonRaphson t 0
      in bezierPoint guessT 0 y1 y2 1

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // keyframe // search
-- ════════════════════════════════════════════════════════════════════════════

-- | Binary search to find the keyframe index where frame falls between [i] and [i+1]
-- Returns the index of the keyframe just before or at the given frame
-- Assumes keyframes are sorted by frame (ascending)
--
--                                                // proof // of // correctness
-- Given: length keyframes >= 2 (handled by case match above)
-- Given: l >= 0, h <= length keyframes - 2, l <= h
-- Prove: mid <= length keyframes - 2 AND mid + 1 <= length keyframes - 1
--
-- Proof:
--   1. mid = (l + h) div 2
--   2. Since l <= h, we have: l <= mid <= h
--   3. Since h <= length keyframes - 2, we have: mid <= length keyframes - 2
--   4. Therefore: mid + 1 <= length keyframes - 1
--   5. Therefore: drop mid keyframes has length >= 2 (at least elements at mid and mid+1)
--   6. Therefore: drop (mid + 1) keyframes has length >= 1 (at least element at mid+1)
--
-- Since we've proven both drops are non-empty, we can safely pattern match.
findKeyframeIndex :: [Keyframe a] -> Double -> Int
findKeyframeIndex keyframes frame =
  case keyframes of
    [] -> 0
    [_] -> 0
    (firstKf:_) ->
      let low = 0
          high = length keyframes - 2  -- -2 because we need i and i+1
          search l h
            | l > h = max 0 (min l (length keyframes - 2))
            | otherwise =
                let mid = (l + h) `div` 2
                    --                                                                     // proof
                    --                                                                     // proof
                    --                                                                     // proof
                    --                                                                     // proof
                    -- Therefore both drops are non-empty - extract elements directly
                    (beforeMid, fromMid) = splitAt mid keyframes
                    (_, fromNext) = splitAt (mid + 1) keyframes
                    -- Extract elements - proven to exist by bounds invariants
                    midKf = case fromMid of
                      (kf : _) -> kf
                      [] -> error ("PROOF VIOLATION: fromMid empty. mid=" <> show mid <> ", length=" <> show (length keyframes) <> ", l=" <> show l <> ", h=" <> show h <> ". Violates: mid <= length keyframes - 2")
                    nextKf = case fromNext of
                      (kf : _) -> kf
                      [] -> error ("PROOF VIOLATION: fromNext empty. mid=" <> show mid <> ", length=" <> show (length keyframes) <> ". Violates: mid + 1 <= length keyframes - 1")
                    midFrame = keyframeFrame midKf
                    nextFrame = keyframeFrame nextKf
                in if frame >= midFrame && frame <= nextFrame
                     then mid
                     else if frame < midFrame
                       then search l (mid - 1)
                       else search (mid + 1) h
      in search low high

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // value // interpolation
-- ════════════════════════════════════════════════════════════════════════════

-- | Calculate the scalar delta between two values for bezier normalization
-- For numbers: returns v2 - v1
-- For vectors: returns magnitude of difference
-- Default: returns 1 if types don't match
getValueDelta :: Double -> Double -> Double
getValueDelta v1 v2 = v2 - v1

-- | Calculate value delta for Vec2 (magnitude of difference)
getValueDeltaVec2 :: Vec2 -> Vec2 -> Double
getValueDeltaVec2 (Vec2 x1 y1) (Vec2 x2 y2) =
  let dx = x2 - x1
      dy = y2 - y1
      distance = safeSqrt (dx * dx + dy * dy)
  in if distance > 0 then distance else 1

-- | Interpolate between two numbers
interpolateNumber :: Double -> Double -> Double -> Double
interpolateNumber v1 v2 t = safeLerp v1 v2 t

-- | Interpolate between two Vec2 values
interpolateVec2 :: Vec2 -> Vec2 -> Double -> Vec2
interpolateVec2 (Vec2 x1 y1) (Vec2 x2 y2) t =
  Vec2 (safeLerp x1 x2 t) (safeLerp y1 y2 t)

-- | Interpolate between two Vec3 values
interpolateVec3 :: Vec3 -> Vec3 -> Double -> Vec3
interpolateVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) t =
  Vec3 (safeLerp x1 x2 t) (safeLerp y1 y2 t) (safeLerp z1 z2 t)

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // color // interpolation
-- ════════════════════════════════════════════════════════════════════════════

-- | Normalize a hex color to 6-digit format
-- Handles: #rgb → #rrggbb, #rgba → #rrggbbaa, #rrggbb → #rrggbb, #rrggbbaa → #rrggbbaa
normalizeHexColor :: Text -> Text
normalizeHexColor hex =
  if T.null hex || not (T.isPrefixOf "#" hex)
  then "#000000"
  else
    let h = T.drop 1 hex
    in case T.length h of
      3 -> T.cons '#' (T.concatMap (\c -> T.pack [c, c]) h)  -- #rgb → #rrggbb
      4 -> T.cons '#' (T.concatMap (\c -> T.pack [c, c]) h)  -- #rgba → #rrggbbaa
      6 -> hex  -- Already 6 chars
      8 -> hex  -- Already 8 chars
      _ -> "#000000"  -- Invalid format

-- | Parse a hex color component, returning 0 for invalid input
parseHexComponent :: Text -> Int -> Int -> Int
parseHexComponent hex start end =
  let component = T.take (end - start) (T.drop start hex)
      parsed = case T.unpack component of
        [] -> 0
        s -> case readHex s of
          [] -> 0
          [(val, _)] -> max 0 (min 255 val)
          _ -> 0
  in parsed

-- | Interpolate between two hex colors
-- Supports: #rgb, #rrggbb, #rgba, #rrggbbaa
-- Invalid colors are treated as black (#000000)
interpolateColor :: Text -> Text -> Double -> Text
interpolateColor c1 c2 t =
  let n1 = normalizeHexColor c1
      n2 = normalizeHexColor c2
      r1 = parseHexComponent n1 1 3
      g1 = parseHexComponent n1 3 5
      b1 = parseHexComponent n1 5 7
      a1 = if T.length n1 == 9 then parseHexComponent n1 7 9 else 255
      r2 = parseHexComponent n2 1 3
      g2 = parseHexComponent n2 3 5
      b2 = parseHexComponent n2 5 7
      a2 = if T.length n2 == 9 then parseHexComponent n2 7 9 else 255
      r = round (fromIntegral r1 + (fromIntegral r2 - fromIntegral r1) * t)
      g = round (fromIntegral g1 + (fromIntegral g2 - fromIntegral g1) * t)
      b = round (fromIntegral b1 + (fromIntegral b2 - fromIntegral b1) * t)
      -- Format as hex string with padding
      formatHexPadded val =
        let hexStr = showHex val ""
            padded = if length hexStr < 2
                     then T.justifyRight 2 '0' (T.pack hexStr)
                     else T.pack hexStr
        in padded
      -- Only include alpha if either input had alpha
      result = if T.length n1 == 9 || T.length n2 == 9
               then
                 let a = round (fromIntegral a1 + (fromIntegral a2 - fromIntegral a1) * t)
                 in T.cons '#' (formatHexPadded r <> formatHexPadded g <> formatHexPadded b <> formatHexPadded a)
               else T.cons '#' (formatHexPadded r <> formatHexPadded g <> formatHexPadded b)
  in result
