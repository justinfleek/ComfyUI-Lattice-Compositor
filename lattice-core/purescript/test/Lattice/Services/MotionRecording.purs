-- | Port of ui/src/__tests__/services/motionRecording.test.ts
-- |
-- | Tests motion recording service: smoothing, path analysis,
-- | keyframe simplification (Douglas-Peucker), bounds calculation.
-- | Pure math portions only — no MotionRecorder class or timers.

module Test.Lattice.Services.MotionRecording (spec) where

import Prelude

import Data.Array (drop, filter, length, mapWithIndex, range, reverse, snoc, zipWith, (!!))
import Data.Foldable (foldl, for_, sum)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Math (abs, cos, pi, sin, sqrt)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)
import Test.Lattice.TestHelpers (assertCloseTo, assertInRange)

-- ---------------------------------------------------------------------------
-- Types
-- ---------------------------------------------------------------------------

type MotionSample = { time :: Number, x :: Number, y :: Number }

type RecordedMotion =
  { pinId :: String
  , samples :: Array MotionSample
  , recordingSpeed :: Number
  }

-- ---------------------------------------------------------------------------
-- Pure functions (port of motionRecording service)
-- ---------------------------------------------------------------------------

-- | Create a linear motion from start to end
createLinearMotion :: String -> { x :: Number, y :: Number } -> { x :: Number, y :: Number }
                   -> Number -> Int -> RecordedMotion
createLinearMotion pinId start end durationMs sampleCount =
  let
    samples = map (\i ->
      let t = toNumber i / toNumber (sampleCount - 1)
      in { time: t * durationMs
         , x: start.x + (end.x - start.x) * t
         , y: start.y + (end.y - start.y) * t
         }
    ) (range 0 (sampleCount - 1))
  in { pinId, samples, recordingSpeed: 1.0 }

-- | Create circular motion around a center point
createCircularMotion :: String -> { x :: Number, y :: Number } -> Number
                     -> Number -> Int -> RecordedMotion
createCircularMotion pinId center radius durationMs sampleCount =
  let
    samples = map (\i ->
      let t = toNumber i / toNumber (sampleCount - 1)
          angle = t * 2.0 * pi
      in { time: t * durationMs
         , x: center.x + cos angle * radius
         , y: center.y + sin angle * radius
         }
    ) (range 0 (sampleCount - 1))
  in { pinId, samples, recordingSpeed: 1.0 }

-- | Smooth motion using moving average with window size
smoothMotionMovingAverage :: RecordedMotion -> Int -> RecordedMotion
smoothMotionMovingAverage motion windowSize =
  let
    n = length motion.samples
    half = windowSize / 2
    smoothSample i sample =
      let
        lo = max 0 (i - half)
        hi = min (n - 1) (i + half)
        windowIndices = range lo hi
        windowCount = length windowIndices
        sumX = foldl (\acc j -> acc + fromMaybe 0.0 (map _.x (motion.samples !! j))) 0.0 windowIndices
        sumY = foldl (\acc j -> acc + fromMaybe 0.0 (map _.y (motion.samples !! j))) 0.0 windowIndices
      in { time: sample.time
         , x: sumX / toNumber windowCount
         , y: sumY / toNumber windowCount
         }
    smoothed = mapWithIndex smoothSample motion.samples
  in motion { samples = smoothed }

-- | Calculate distance between two points
dist :: Number -> Number -> Number -> Number -> Number
dist x1 y1 x2 y2 =
  let dx = x2 - x1
      dy = y2 - y1
  in sqrt (dx * dx + dy * dy)

-- | Get the total path length of recorded motion
getMotionPathLength :: RecordedMotion -> Number
getMotionPathLength motion =
  let segments = zipWith (\a b -> dist a.x a.y b.x b.y) motion.samples (drop 1 motion.samples)
  in sum segments

-- | Get motion bounds (bounding box)
getMotionBounds :: RecordedMotion -> { minX :: Number, maxX :: Number, minY :: Number, maxY :: Number, width :: Number, height :: Number }
getMotionBounds motion =
  case motion.samples of
    [] -> { minX: 0.0, maxX: 0.0, minY: 0.0, maxY: 0.0, width: 0.0, height: 0.0 }
    _ ->
      let
        xs = map _.x motion.samples
        ys = map _.y motion.samples
        minX = foldl min 1.0e99 xs
        maxX = foldl max (-1.0e99) xs
        minY = foldl min 1.0e99 ys
        maxY = foldl max (-1.0e99) ys
      in { minX, maxX, minY, maxY, width: maxX - minX, height: maxY - minY }

-- | Get average speed in pixels per second
getMotionAverageSpeed :: RecordedMotion -> Number
getMotionAverageSpeed motion =
  let n = length motion.samples
  in if n < 2
    then 0.0
    else
      let
        pathLength = getMotionPathLength motion
        firstTime = fromMaybe 0.0 (map _.time (motion.samples !! 0))
        lastTime = fromMaybe 0.0 (map _.time (motion.samples !! (n - 1)))
        durationSec = (lastTime - firstTime) / 1000.0
      in if durationSec <= 0.0
           then 0.0
           else pathLength / durationSec

-- | Perpendicular distance from point to line (for Douglas-Peucker)
perpendicularDistance :: MotionSample -> MotionSample -> MotionSample -> Number
perpendicularDistance point lineStart lineEnd =
  let
    dx = lineEnd.x - lineStart.x
    dy = lineEnd.y - lineStart.y
    lineLenSq = dx * dx + dy * dy
  in if lineLenSq == 0.0
       then dist point.x point.y lineStart.x lineStart.y
       else
         let
           -- Project point onto line
           t = ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) / lineLenSq
           projX = lineStart.x + t * dx
           projY = lineStart.y + t * dy
         in dist point.x point.y projX projY

-- | Douglas-Peucker simplification on motion samples
simplifyDouglasPeucker :: Array MotionSample -> Number -> Array MotionSample
simplifyDouglasPeucker samples tolerance =
  let n = length samples
  in if n <= 2
       then samples
       else
         let
           first = fromMaybe { time: 0.0, x: 0.0, y: 0.0 } (samples !! 0)
           last = fromMaybe { time: 0.0, x: 0.0, y: 0.0 } (samples !! (n - 1))
           -- Find point with maximum distance from line
           findMax = foldl (\acc i ->
             case samples !! i of
               Nothing -> acc
               Just s ->
                 let d = perpendicularDistance s first last
                 in if d > acc.maxDist
                      then { maxDist: d, maxIdx: i }
                      else acc
           ) { maxDist: 0.0, maxIdx: 0 } (range 1 (n - 2))
         in if findMax.maxDist > tolerance
              then
                -- Recursively simplify both halves
                let
                  leftSlice = takeN (findMax.maxIdx + 1) samples
                  rightSlice = dropN findMax.maxIdx samples
                  leftSimplified = simplifyDouglasPeucker leftSlice tolerance
                  rightSimplified = simplifyDouglasPeucker rightSlice tolerance
                in leftSimplified <> drop 1 rightSimplified
              else [first, last]

-- | Take first n elements of array
takeN :: Int -> Array MotionSample -> Array MotionSample
takeN n arr = map (\i -> fromMaybe { time: 0.0, x: 0.0, y: 0.0 } (arr !! i)) (range 0 (min (n - 1) (length arr - 1)))

-- | Drop first n elements of array
dropN :: Int -> Array MotionSample -> Array MotionSample
dropN n arr =
  let len = length arr
  in if n >= len
       then []
       else map (\i -> fromMaybe { time: 0.0, x: 0.0, y: 0.0 } (arr !! i)) (range n (len - 1))

-- ---------------------------------------------------------------------------
-- Spec
-- ---------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "MotionRecording" do
    movingAverageTests
    pathLengthTests
    boundsTests
    averageSpeedTests
    douglasPeuckerTests

-- ---------------------------------------------------------------------------
-- Moving Average Tests
-- ---------------------------------------------------------------------------

movingAverageTests :: Spec Unit
movingAverageTests = do
  describe "smoothMotionMovingAverage" do
    it "applies moving average correctly" do
      let motion =
            { pinId: "pin1"
            , samples:
                [ { time: 0.0, x: 0.0, y: 0.0 }
                , { time: 100.0, x: 10.0, y: 10.0 }
                , { time: 200.0, x: 20.0, y: 20.0 }
                , { time: 300.0, x: 30.0, y: 30.0 }
                , { time: 400.0, x: 40.0, y: 40.0 }
                ]
            , recordingSpeed: 1.0
            }
      let smoothed = smoothMotionMovingAverage motion 3
      -- Middle sample (index 2) should be average of neighbors
      case smoothed.samples !! 2 of
        Nothing -> fail "Expected sample at index 2"
        Just s -> do
          -- (10 + 20 + 30) / 3 = 20
          assertCloseTo 1.0 20.0 s.x
          assertCloseTo 1.0 20.0 s.y

    it "preserves sample count after smoothing" do
      let motion = createLinearMotion "pin1" { x: 0.0, y: 0.0 } { x: 100.0, y: 100.0 } 1000.0 20
      let smoothed = smoothMotionMovingAverage motion 5
      length smoothed.samples `shouldEqual` length motion.samples

    it "preserves timestamps after smoothing" do
      let motion = createLinearMotion "pin1" { x: 0.0, y: 0.0 } { x: 100.0, y: 100.0 } 1000.0 10
      let smoothed = smoothMotionMovingAverage motion 3
      for_ (range 0 (length motion.samples - 1)) \i ->
        case { orig: motion.samples !! i, sm: smoothed.samples !! i } of
          { orig: Just o, sm: Just s } -> s.time `shouldEqual` o.time
          _ -> pure unit

-- ---------------------------------------------------------------------------
-- Path Length Tests
-- ---------------------------------------------------------------------------

pathLengthTests :: Spec Unit
pathLengthTests = do
  describe "getMotionPathLength" do
    it "calculates correct path length for straight horizontal line" do
      let motion = createLinearMotion "pin1" { x: 0.0, y: 0.0 } { x: 100.0, y: 0.0 } 1000.0 10
      assertCloseTo 1.0 100.0 (getMotionPathLength motion)

    it "calculates correct path length for diagonal (3-4-5)" do
      let motion = createLinearMotion "pin1" { x: 0.0, y: 0.0 } { x: 30.0, y: 40.0 } 1000.0 10
      assertCloseTo 1.0 50.0 (getMotionPathLength motion)

    it "handles single sample" do
      let motion = { pinId: "pin1", samples: [{ time: 0.0, x: 0.0, y: 0.0 }], recordingSpeed: 1.0 }
      getMotionPathLength motion `shouldEqual` 0.0

    it "handles empty motion" do
      let motion = { pinId: "pin1", samples: [] :: Array MotionSample, recordingSpeed: 1.0 }
      getMotionPathLength motion `shouldEqual` 0.0

-- ---------------------------------------------------------------------------
-- Bounds Tests
-- ---------------------------------------------------------------------------

boundsTests :: Spec Unit
boundsTests = do
  describe "getMotionBounds" do
    it "calculates correct bounds" do
      let motion =
            { pinId: "pin1"
            , samples:
                [ { time: 0.0, x: 10.0, y: 20.0 }
                , { time: 100.0, x: 50.0, y: 60.0 }
                , { time: 200.0, x: 30.0, y: 40.0 }
                ]
            , recordingSpeed: 1.0
            }
      let bounds = getMotionBounds motion
      bounds.minX `shouldEqual` 10.0
      bounds.maxX `shouldEqual` 50.0
      bounds.minY `shouldEqual` 20.0
      bounds.maxY `shouldEqual` 60.0
      bounds.width `shouldEqual` 40.0
      bounds.height `shouldEqual` 40.0

    it "handles empty motion" do
      let motion = { pinId: "pin1", samples: [] :: Array MotionSample, recordingSpeed: 1.0 }
      let bounds = getMotionBounds motion
      bounds.width `shouldEqual` 0.0
      bounds.height `shouldEqual` 0.0

    it "handles single point" do
      let motion = { pinId: "pin1", samples: [{ time: 0.0, x: 50.0, y: 75.0 }], recordingSpeed: 1.0 }
      let bounds = getMotionBounds motion
      bounds.minX `shouldEqual` 50.0
      bounds.maxX `shouldEqual` 50.0
      bounds.width `shouldEqual` 0.0
      bounds.height `shouldEqual` 0.0

-- ---------------------------------------------------------------------------
-- Average Speed Tests
-- ---------------------------------------------------------------------------

averageSpeedTests :: Spec Unit
averageSpeedTests = do
  describe "getMotionAverageSpeed" do
    it "calculates correct average speed" do
      -- 100 pixels over 1000ms = 100 pixels/second
      let motion = createLinearMotion "pin1" { x: 0.0, y: 0.0 } { x: 100.0, y: 0.0 } 1000.0 10
      assertCloseTo 1.0 100.0 (getMotionAverageSpeed motion)

    it "handles empty motion" do
      let motion = { pinId: "pin1", samples: [] :: Array MotionSample, recordingSpeed: 1.0 }
      getMotionAverageSpeed motion `shouldEqual` 0.0

    it "handles diagonal motion (3-4-5)" do
      -- 50 pixels over 1000ms = 50 pixels/second
      let motion = createLinearMotion "pin1" { x: 0.0, y: 0.0 } { x: 30.0, y: 40.0 } 1000.0 10
      assertCloseTo 1.0 50.0 (getMotionAverageSpeed motion)

-- ---------------------------------------------------------------------------
-- Douglas-Peucker Simplification Tests
-- ---------------------------------------------------------------------------

douglasPeuckerTests :: Spec Unit
douglasPeuckerTests = do
  describe "simplifyDouglasPeucker" do
    it "reduces linear motion to 2 points" do
      let motion = createLinearMotion "pin1" { x: 0.0, y: 0.0 } { x: 100.0, y: 100.0 } 1000.0 50
      let simplified = simplifyDouglasPeucker motion.samples 1.0
      -- Perfectly linear motion should reduce to just start and end
      length simplified `shouldEqual` 2

    it "preserves endpoints" do
      let motion = createLinearMotion "pin1" { x: 0.0, y: 0.0 } { x: 100.0, y: 100.0 } 1000.0 20
      let simplified = simplifyDouglasPeucker motion.samples 5.0
      case { first: simplified !! 0, last: simplified !! (length simplified - 1) } of
        { first: Just f, last: Just l } -> do
          assertCloseTo 0.01 0.0 f.x
          assertCloseTo 0.01 0.0 f.y
          assertCloseTo 0.01 100.0 l.x
          assertCloseTo 0.01 100.0 l.y
        _ -> fail "Expected at least 2 points"

    it "preserves sharp turns" do
      -- Motion with a sharp right-angle turn
      let samples =
            [ { time: 0.0, x: 0.0, y: 0.0 }
            , { time: 100.0, x: 25.0, y: 0.0 }
            , { time: 200.0, x: 50.0, y: 0.0 }   -- Turn point
            , { time: 300.0, x: 50.0, y: 25.0 }
            , { time: 400.0, x: 50.0, y: 50.0 }
            ]
      let simplified = simplifyDouglasPeucker samples 1.0
      -- Should keep the turn point (50, 0)
      if length simplified > 2
        then pure unit
        else fail "Expected turn point to be preserved"

    it "handles 2 points unchanged" do
      let samples =
            [ { time: 0.0, x: 0.0, y: 0.0 }
            , { time: 100.0, x: 100.0, y: 100.0 }
            ]
      let simplified = simplifyDouglasPeucker samples 5.0
      length simplified `shouldEqual` 2

    it "circular motion keeps multiple points" do
      let motion = createCircularMotion "pin1" { x: 50.0, y: 50.0 } 30.0 1000.0 50
      let simplified = simplifyDouglasPeucker motion.samples 2.0
      -- Circle needs many points to approximate
      if length simplified > 4
        then pure unit
        else fail ("Expected >4 points for circle, got " <> show (length simplified))

    it "higher tolerance produces fewer points" do
      let motion = createCircularMotion "pin1" { x: 50.0, y: 50.0 } 30.0 1000.0 50
      let lowTol = simplifyDouglasPeucker motion.samples 1.0
      let highTol = simplifyDouglasPeucker motion.samples 10.0
      if length highTol <= length lowTol
        then pure unit
        else fail ("Expected high tolerance to produce fewer points: " <> show (length highTol) <> " vs " <> show (length lowTol))
