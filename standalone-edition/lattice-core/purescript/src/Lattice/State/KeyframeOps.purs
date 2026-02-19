-- | Lattice.State.KeyframeOps - Pure keyframe CRUD operations
-- |
-- | Port of ui/src/stores/keyframeStore/crud.ts, query.ts, timing.ts
-- | All functions are pure - no state/effect needed.

module Lattice.State.KeyframeOps
  ( addKeyframe
  , removeKeyframe
  , clearKeyframes
  , moveKeyframe
  , moveKeyframes
  , setKeyframeValue
  , setKeyframeInterpolation
  , getKeyframesAtFrame
  , getAllKeyframeFrames
  , findNextKeyframeFrame
  , findPrevKeyframeFrame
  , findSurroundingKeyframes
  , scaleKeyframeTiming
  , timeReverseKeyframes
  , sortKeyframes
  ) where

import Prelude

import Data.Array (filter, findIndex, foldl, head, index, length, nub, reverse, snoc, sort, sortBy, updateAt, zip)
import Data.Int (round, toNumber) as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Lattice.Primitives (FiniteFloat(..), FrameNumber(..), NonEmptyString, unNonEmptyString)
import Lattice.Entities (Keyframe, ControlMode(..))
import Lattice.Enums (InterpolationType(..))

-- ────────────────────────────────────────────────────────────────────────────
-- Sort
-- ────────────────────────────────────────────────────────────────────────────

-- | Sort keyframes by frame number (ascending)
sortKeyframes :: Array Keyframe -> Array Keyframe
sortKeyframes = sortBy compareFrames
  where
    compareFrames a b = compare a.frame b.frame

-- ────────────────────────────────────────────────────────────────────────────
--                                                                      // crud
-- ────────────────────────────────────────────────────────────────────────────

-- | Add a keyframe to the array. If a keyframe at the same frame exists, replace it.
-- | Returns the new sorted array.
addKeyframe :: Keyframe -> Array Keyframe -> Array Keyframe
addKeyframe kf kfs =
  let
    filtered = filter (\k -> k.frame /= kf.frame) kfs
  in sortKeyframes (snoc filtered kf)

-- | Remove a keyframe by ID. Returns Nothing if ID not found.
removeKeyframe :: NonEmptyString -> Array Keyframe -> Maybe (Array Keyframe)
removeKeyframe kfId kfs =
  let filtered = filter (\k -> unNonEmptyString k.id /= unNonEmptyString kfId) kfs
  in if length filtered == length kfs
    then Nothing
    else Just filtered

-- | Remove all keyframes
clearKeyframes :: Array Keyframe -> Array Keyframe
clearKeyframes _ = []

-- | Move a keyframe to a new frame. Clamps to frame 0 minimum.
moveKeyframe :: NonEmptyString -> FrameNumber -> Array Keyframe -> Array Keyframe
moveKeyframe kfId (FrameNumber newFrame) kfs =
  let clampedFrame = FrameNumber (max 0 newFrame)
  in case findIndex (\k -> unNonEmptyString k.id == unNonEmptyString kfId) kfs of
    Nothing -> kfs
    Just _ ->
      let
        -- Remove any existing keyframe at target frame (other than this one)
        withoutTarget = filter (\k ->
          k.frame /= clampedFrame || unNonEmptyString k.id == unNonEmptyString kfId
        ) kfs
      in case findIndex (\k -> unNonEmptyString k.id == unNonEmptyString kfId) withoutTarget of
        Nothing -> kfs
        Just idx2 ->
          let kf = fromMaybe defaultKf (index withoutTarget idx2)
          in case updateAt idx2 (kf { frame = clampedFrame }) withoutTarget of
            Just updated -> sortKeyframes updated
            Nothing -> kfs
  where
    defaultKf =
      { id: kfId
      , frame: FrameNumber 0
      , value: ""
      , interpolation: ITLinear
      , inHandle: { frame: FiniteFloat 0.0, value: FiniteFloat 0.0, enabled: true }
      , outHandle: { frame: FiniteFloat 0.0, value: FiniteFloat 0.0, enabled: true }
      , controlMode: CMSmooth
      }

-- | Batch move keyframes by a delta. Clamps each to frame 0 minimum.
moveKeyframes :: Array { id :: NonEmptyString, delta :: Int } -> Array Keyframe -> Array Keyframe
moveKeyframes moves kfs =
  let
    applyMove arr { id: kfId, delta } =
      case findIndex (\k -> unNonEmptyString k.id == unNonEmptyString kfId) arr of
        Nothing -> arr
        Just idx ->
          case index arr idx of
            Just kf ->
              let FrameNumber f = kf.frame
                  newFrame = FrameNumber (max 0 (f + delta))
              in fromMaybe arr (updateAt idx (kf { frame = newFrame }) arr)
            Nothing -> arr
  in sortKeyframes (foldl applyMove kfs moves)

-- | Update a keyframe's value
setKeyframeValue :: NonEmptyString -> String -> Array Keyframe -> Array Keyframe
setKeyframeValue kfId newValue kfs =
  map (\k -> if unNonEmptyString k.id == unNonEmptyString kfId
             then k { value = newValue }
             else k) kfs

-- | Update a keyframe's interpolation type
setKeyframeInterpolation :: NonEmptyString -> InterpolationType -> Array Keyframe -> Array Keyframe
setKeyframeInterpolation kfId newInterp kfs =
  map (\k -> if unNonEmptyString k.id == unNonEmptyString kfId
             then k { interpolation = newInterp }
             else k) kfs

-- ────────────────────────────────────────────────────────────────────────────
-- Queries
-- ────────────────────────────────────────────────────────────────────────────

-- | Get all keyframes at a specific frame
getKeyframesAtFrame :: FrameNumber -> Array Keyframe -> Array Keyframe
getKeyframesAtFrame frame kfs = filter (\k -> k.frame == frame) kfs

-- | Get all unique keyframe frames, sorted ascending
getAllKeyframeFrames :: Array Keyframe -> Array FrameNumber
getAllKeyframeFrames kfs = sort (nub (map _.frame kfs))

-- | Find the next keyframe frame after the given frame
findNextKeyframeFrame :: FrameNumber -> Array Keyframe -> Maybe FrameNumber
findNextKeyframeFrame frame kfs =
  head (sort (filter (_ > frame) (map _.frame kfs)))

-- | Find the previous keyframe frame before the given frame
findPrevKeyframeFrame :: FrameNumber -> Array Keyframe -> Maybe FrameNumber
findPrevKeyframeFrame frame kfs =
  head (reverse (sort (filter (_ < frame) (map _.frame kfs))))

-- | Find the surrounding keyframes for interpolation
findSurroundingKeyframes :: FrameNumber -> Array Keyframe
  -> { before :: Maybe Keyframe, after :: Maybe Keyframe }
findSurroundingKeyframes frame kfs =
  let
    sorted = sortKeyframes kfs
    before = head (reverse (filter (\k -> k.frame < frame) sorted))
    after = head (filter (\k -> k.frame > frame) sorted)
  in { before, after }

-- ────────────────────────────────────────────────────────────────────────────
-- Timing
-- ────────────────────────────────────────────────────────────────────────────

-- | Scale keyframe timing by a factor around an anchor frame
scaleKeyframeTiming :: Number -> FrameNumber -> Array Keyframe -> Array Keyframe
scaleKeyframeTiming factor (FrameNumber anchor) kfs =
  sortKeyframes (map scaleKf kfs)
  where
    scaleKf kf =
      let FrameNumber f = kf.frame
          scaled = anchor + Int.round (Int.toNumber (f - anchor) * factor)
      in kf { frame = FrameNumber (max 0 scaled) }

-- | Reverse the values of keyframes while keeping frames in place
timeReverseKeyframes :: Array Keyframe -> Array Keyframe
timeReverseKeyframes kfs =
  let
    sorted = sortKeyframes kfs
    reversedValues = reverse (map _.value sorted)
  in map (\(Tuple kf val) -> kf { value = val }) (zip sorted reversedValues)
