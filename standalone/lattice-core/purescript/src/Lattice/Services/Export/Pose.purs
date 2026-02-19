-- | Lattice.Services.Export.Pose - ControlNet pose export
-- |
-- | Pure types and request builders for pose data export.
-- | Rendering operations are done by the Haskell backend via Bridge.
-- |
-- | Exports pose data for ControlNet conditioning:
-- | - OpenPose JSON format
-- | - Pose image sequences (black background, colored skeleton)
-- | - DWPose/RTMW format support
-- | - Multi-person batch export
-- |
-- | Source: ui/src/services/export/poseExport.ts

module Lattice.Services.Export.Pose
  ( -- * Types
    PoseKeypoint
  , Pose
  , PoseFormat(..)
  , PoseOutputFormat(..)
  , PoseExportConfig
  , PoseFrame
  , PoseSequence
  , OpenPoseJSON
  , OpenPosePerson
  , PoseExportResult
    -- * Request Types
  , PoseRenderRequest(..)
    -- * Constants
  , cocoBones
  , openposeColors
  , getBoneColor
    -- * Animation (Pure)
  , createPoseSequence
  , interpolatePoses
  , interpolateKeypoint
  , interpolateAtFrame
    -- * Export (Pure)
  , exportToOpenPoseJSON
  , poseToOpenPosePerson
    -- * Import (Pure)
  , importFromOpenPoseJSON
  , importPerson
  , importPoseSequence
    -- * Request Builders
  , mkRenderPoseFrameRequest
  , mkExportPoseSequenceRequest
    -- * Defaults
  , defaultPoseExportConfig
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Int (toNumber)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)
import Data.Foldable (foldl)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Pose keypoint with x, y, confidence
type PoseKeypoint =
  { x :: Number          -- 0-1 normalized
  , y :: Number          -- 0-1 normalized
  , confidence :: Number -- 0-1
  }

-- | A single pose (one person)
type Pose =
  { id :: String
  , keypoints :: Array PoseKeypoint
  , format :: PoseFormat
  }

-- | Pose format variants
data PoseFormat
  = FormatCOCO18       -- Standard COCO 18 keypoints
  | FormatOpenPose25   -- OpenPose 25 body keypoints
  | FormatDWPose       -- DWPose format
  | FormatMediaPipe    -- MediaPipe format

derive instance Generic PoseFormat _
instance Show PoseFormat where show = genericShow
instance Eq PoseFormat where eq = genericEq
instance EncodeJson PoseFormat where
  encodeJson = genericEncodeJson

-- | Pose export configuration
type PoseExportConfig =
  { width :: Int
  , height :: Int
  , startFrame :: Int
  , endFrame :: Int
  , boneWidth :: Number
  , keypointRadius :: Number
  , showKeypoints :: Boolean
  , showBones :: Boolean
  , useOpenPoseColors :: Boolean
  , customColor :: Maybe String
  , backgroundColor :: String
  , outputFormat :: PoseOutputFormat
  }

-- | Output format options
data PoseOutputFormat
  = OutputImages
  | OutputJSON
  | OutputBoth

derive instance Generic PoseOutputFormat _
instance Show PoseOutputFormat where show = genericShow
instance Eq PoseOutputFormat where eq = genericEq
instance EncodeJson PoseOutputFormat where
  encodeJson = genericEncodeJson

-- | A single frame with poses
type PoseFrame =
  { frameNumber :: Int
  , poses :: Array Pose
  }

-- | Complete pose sequence
type PoseSequence =
  { frames :: Array PoseFrame
  , format :: PoseFormat
  , fps :: Int
  }

-- | OpenPose person data
type OpenPosePerson =
  { person_id :: Array Int
  , pose_keypoints_2d :: Array Number
  , face_keypoints_2d :: Array Number
  , hand_left_keypoints_2d :: Array Number
  , hand_right_keypoints_2d :: Array Number
  , pose_keypoints_3d :: Array Number
  , face_keypoints_3d :: Array Number
  , hand_left_keypoints_3d :: Array Number
  , hand_right_keypoints_3d :: Array Number
  }

-- | OpenPose JSON format
type OpenPoseJSON =
  { version :: Number
  , people :: Array OpenPosePerson
  }

-- | Pose export result
type PoseExportResult =
  { imagePaths :: Maybe (Array String)
  , jsonFrames :: Maybe (Array OpenPoseJSON)
  , sequenceJson :: Maybe
      { frames :: Array OpenPoseJSON
      , metadata ::
          { frameCount :: Int
          , fps :: Int
          , width :: Int
          , height :: Int
          }
      }
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Request Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Pose render request - sent to Haskell backend
data PoseRenderRequest
  = RenderPoseFrameRequest
      { poses :: Array Pose
      , config :: PoseExportConfig
      }
  | ExportPoseSequenceRequest
      { sequence :: PoseSequence
      , config :: PoseExportConfig
      }
  | ExportPoseForControlNetRequest
      { poses :: Array Pose
      , width :: Int
      , height :: Int
      }

derive instance Generic PoseRenderRequest _
instance Show PoseRenderRequest where show = genericShow
instance EncodeJson PoseRenderRequest where
  encodeJson = genericEncodeJson

-- ────────────────────────────────────────────────────────────────────────────
-- Request Builders
-- ────────────────────────────────────────────────────────────────────────────

-- | Create pose frame render request
mkRenderPoseFrameRequest :: Array Pose -> PoseExportConfig -> PoseRenderRequest
mkRenderPoseFrameRequest poses config =
  RenderPoseFrameRequest { poses, config }

-- | Create pose sequence export request
mkExportPoseSequenceRequest :: PoseSequence -> PoseExportConfig -> PoseRenderRequest
mkExportPoseSequenceRequest sequence config =
  ExportPoseSequenceRequest { sequence, config }

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | COCO bone connections (pairs of keypoint indices)
cocoBones :: Array (Array Int)
cocoBones =
  [ [0, 1], [0, 2], [1, 3], [2, 4]     -- Head
  , [5, 6], [5, 7], [7, 9], [6, 8], [8, 10]  -- Arms
  , [5, 11], [6, 12], [11, 12]        -- Torso
  , [11, 13], [13, 15], [12, 14], [14, 16]  -- Legs
  ]

-- | OpenPose colors by body part
openposeColors ::
  { head :: String
  , right_arm :: String
  , left_arm :: String
  , right_leg :: String
  , left_leg :: String
  , torso :: String
  }
openposeColors =
  { head: "#FF0000"
  , right_arm: "#FF7F00"
  , left_arm: "#00FF00"
  , right_leg: "#0000FF"
  , left_leg: "#FF00FF"
  , torso: "#00FFFF"
  }

-- | Get bone color by index
getBoneColor :: Int -> String
getBoneColor idx
  | idx < 4 = openposeColors.head
  | idx < 9 = if idx `mod` 2 == 0 then openposeColors.right_arm else openposeColors.left_arm
  | idx < 12 = openposeColors.torso
  | idx < 14 = openposeColors.right_leg
  | otherwise = openposeColors.left_leg

-- ────────────────────────────────────────────────────────────────────────────
-- Animation (Pure)
-- ────────────────────────────────────────────────────────────────────────────

-- | Interpolate between two poses
interpolatePoses :: Pose -> Pose -> Number -> Pose
interpolatePoses poseA poseB t =
  let
    interpolatedKeypoints = Array.zipWith (\a b -> interpolateKeypoint a b t) poseA.keypoints poseB.keypoints
  in
    { id: poseA.id
    , keypoints: interpolatedKeypoints
    , format: poseA.format
    }

-- | Interpolate single keypoint
interpolateKeypoint :: PoseKeypoint -> PoseKeypoint -> Number -> PoseKeypoint
interpolateKeypoint a b t =
  { x: a.x + (b.x - a.x) * t
  , y: a.y + (b.y - a.y) * t
  , confidence: a.confidence + (b.confidence - a.confidence) * t
  }

-- | Create animated pose sequence from keyframes
createPoseSequence
  :: Array { frame :: Int, poses :: Array Pose }
  -> Int
  -> Int
  -> PoseSequence
createPoseSequence keyframePoses totalFrames fps =
  let
    sortedKeyframes = Array.sortWith _.frame keyframePoses

    frames = Array.range 0 (totalFrames - 1) # map \frameNum ->
      { frameNumber: frameNum
      , poses: interpolateAtFrame sortedKeyframes frameNum
      }
  in
    { frames
    , format: FormatCOCO18
    , fps
    }

-- | Interpolate poses at a specific frame
interpolateAtFrame
  :: Array { frame :: Int, poses :: Array Pose }
  -> Int
  -> Array Pose
interpolateAtFrame keyframes frameNum =
  case Array.head keyframes, Array.last keyframes of
    Nothing, _ -> []
    _, Nothing -> []
    Just first, Just last ->
      let
        -- Find surrounding keyframes
        { prev, next } = findSurroundingKeyframes keyframes frameNum first last
      in
        if prev.frame == next.frame || frameNum <= prev.frame then
          prev.poses
        else if frameNum >= next.frame then
          next.poses
        else
          let
            t = toNumber (frameNum - prev.frame) / toNumber (next.frame - prev.frame)
            numPoses = min (Array.length prev.poses) (Array.length next.poses)
          in
            Array.range 0 (numPoses - 1) # Array.mapMaybe \i -> do
              pA <- Array.index prev.poses i
              pB <- Array.index next.poses i
              pure (interpolatePoses pA pB t)

-- | Find surrounding keyframes
findSurroundingKeyframes
  :: Array { frame :: Int, poses :: Array Pose }
  -> Int
  -> { frame :: Int, poses :: Array Pose }
  -> { frame :: Int, poses :: Array Pose }
  -> { prev :: { frame :: Int, poses :: Array Pose }
     , next :: { frame :: Int, poses :: Array Pose }
     }
findSurroundingKeyframes keyframes frameNum defaultFirst defaultLast =
  foldl (\acc kf ->
    if kf.frame <= frameNum then
      acc { prev = kf }
    else if acc.next.frame > frameNum || acc.next.frame < kf.frame then
      acc
    else
      acc { next = kf }
  ) { prev: defaultFirst, next: defaultLast } keyframes

-- ────────────────────────────────────────────────────────────────────────────
-- Export Functions (Pure)
-- ────────────────────────────────────────────────────────────────────────────

-- | Export poses to OpenPose JSON format
exportToOpenPoseJSON :: Array Pose -> OpenPoseJSON
exportToOpenPoseJSON poses =
  let
    people = map poseToOpenPosePerson poses
  in
    { version: 1.3
    , people
    }

-- | Convert single pose to OpenPose person
poseToOpenPosePerson :: Pose -> OpenPosePerson
poseToOpenPosePerson pose =
  let
    pose_keypoints_2d = pose.keypoints # Array.concatMap \kp ->
      [kp.x, kp.y, kp.confidence]
  in
    { person_id: [-1]
    , pose_keypoints_2d
    , face_keypoints_2d: []
    , hand_left_keypoints_2d: []
    , hand_right_keypoints_2d: []
    , pose_keypoints_3d: []
    , face_keypoints_3d: []
    , hand_left_keypoints_3d: []
    , hand_right_keypoints_3d: []
    }

-- ────────────────────────────────────────────────────────────────────────────
-- Import Functions (Pure)
-- ────────────────────────────────────────────────────────────────────────────

-- | Import poses from OpenPose JSON
importFromOpenPoseJSON :: OpenPoseJSON -> Array Pose
importFromOpenPoseJSON json =
  Array.mapWithIndex importPerson json.people

-- | Import single person
importPerson :: Int -> OpenPosePerson -> Pose
importPerson idx person =
  let
    kp = person.pose_keypoints_2d
    keypoints = parseKeypoints kp
  in
    { id: "imported_" <> show idx
    , keypoints
    , format: FormatCOCO18
    }

-- | Parse keypoints from flat array
parseKeypoints :: Array Number -> Array PoseKeypoint
parseKeypoints arr = go arr []
  where
    go remaining acc =
      let chunk = Array.take 3 remaining
      in if Array.length chunk == 3
        then case Array.index chunk 0, Array.index chunk 1, Array.index chunk 2 of
          Just x, Just y, Just confidence ->
            go (Array.drop 3 remaining) (Array.snoc acc { x, y, confidence })
          _, _, _ -> acc
        else acc

-- | Import pose sequence from array of OpenPose JSON
importPoseSequence :: Array OpenPoseJSON -> Int -> PoseSequence
importPoseSequence jsonFrames fps =
  let
    frames = Array.mapWithIndex (\idx json ->
      { frameNumber: idx
      , poses: importFromOpenPoseJSON json
      }) jsonFrames
  in
    { frames
    , format: FormatCOCO18
    , fps
    }

-- ────────────────────────────────────────────────────────────────────────────
-- Defaults
-- ────────────────────────────────────────────────────────────────────────────

-- | Default pose export configuration
defaultPoseExportConfig :: PoseExportConfig
defaultPoseExportConfig =
  { width: 512
  , height: 512
  , startFrame: 0
  , endFrame: 80
  , boneWidth: 4.0
  , keypointRadius: 4.0
  , showKeypoints: true
  , showBones: true
  , useOpenPoseColors: true
  , customColor: Nothing
  , backgroundColor: "#000000"
  , outputFormat: OutputBoth
  }
