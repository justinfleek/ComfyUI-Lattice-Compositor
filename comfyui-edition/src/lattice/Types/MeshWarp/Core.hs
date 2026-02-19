-- |
-- Module      : Lattice.Types.MeshWarp.Core
-- Description : Core types for mesh deformation using control pins
-- 
-- Migrated from ui/src/types/meshWarp.ts
-- Supports position, rotation, and stiffness pin types for vector skinning-style deformation
-- Allows organic animation by manipulating control pins
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.MeshWarp.Core
  ( -- Pin types
    WarpPinType (..),
    WarpPin (..),
    WarpPinRestState (..),
    -- Mesh types
    WarpMesh (..),
    WarpDeformationResult (..),
    WarpControlPoint (..),
    -- Weight calculation
    WarpWeightMethod (..),
    WarpWeightOptions (..),
    defaultWarpWeightOptions,
  )
where

import Data.Aeson
  ( ToJSON (..),
    FromJSON (..),
    withObject,
    withText,
    object,
    (.=),
    (.:),
    (.:?),
    Value (..),
  )
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Types.Animation
  ( AnimatableProperty (..),
    PropertyType (..),
  )
import Lattice.Types.Primitives
  ( Vec2 (..),
    validateFinite,
    validateNonNegative,
    validateNormalized01,
  )
import Lattice.Schema.SharedValidation (validateBoundedArray)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                              // pin // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Type of warp pin
data WarpPinType
  = WarpPinTypePosition -- Deform pin: Move mesh vertices by animating position
  | WarpPinTypeRotation -- Rotation pin: Rotate around fixed point (legacy, use 'bend' for new code)
  | WarpPinTypeStarch -- Stiffness pin: Define rigid areas that resist deformation
  | WarpPinTypeOverlap -- Overlap pin: Control depth/z-order during deformation
  | WarpPinTypeBend -- Bend pin: Rotation + scale at joints (position is fixed reference)
  | WarpPinTypeAdvanced -- Advanced pin: Full transform control (position + rotation + scale)
  deriving (Eq, Show, Generic)

instance ToJSON WarpPinType where
  toJSON WarpPinTypePosition = "position"
  toJSON WarpPinTypeRotation = "rotation"
  toJSON WarpPinTypeStarch = "starch"
  toJSON WarpPinTypeOverlap = "overlap"
  toJSON WarpPinTypeBend = "bend"
  toJSON WarpPinTypeAdvanced = "advanced"

instance FromJSON WarpPinType where
  parseJSON = withText "WarpPinType" $ \s ->
    case s of
      t | t == T.pack "position" -> return WarpPinTypePosition
      t | t == T.pack "rotation" -> return WarpPinTypeRotation
      t | t == T.pack "starch" -> return WarpPinTypeStarch
      t | t == T.pack "overlap" -> return WarpPinTypeOverlap
      t | t == T.pack "bend" -> return WarpPinTypeBend
      t | t == T.pack "advanced" -> return WarpPinTypeAdvanced
      _ -> fail "Invalid WarpPinType"

-- | A control pin for mesh warp deformation
-- Pin type determines which properties are actively used:
-- - position: Animates position only (standard deform pin)
-- - rotation: Animates rotation only (legacy, prefer 'bend')
-- - starch: No animation, uses stiffness to define rigid areas
-- - overlap: No position animation, uses inFront for depth control
-- - bend: Animates rotation + scale at fixed position (joint pin)
-- - advanced: Animates position + rotation + scale (full transform)
data WarpPin = WarpPin
  { warpPinId :: Text, -- Unique identifier
    warpPinName :: Text, -- Display name
    warpPinType :: WarpPinType, -- Pin type determines deformation behavior
    warpPinPosition :: AnimatableProperty Vec2, -- Pin position (animatable for position/advanced types)
    warpPinRadius :: Double, -- Influence radius in pixels (also used as extent for overlap pins)
    warpPinStiffness :: Double, -- Stiffness/rigidity of the pin area (0-1, used by starch type)
    warpPinRotation :: AnimatableProperty Double, -- Rotation at this pin in degrees (animatable for rotation/bend/advanced types)
    warpPinScale :: AnimatableProperty Double, -- Scale factor at this pin (animatable for bend/advanced types)
    warpPinDepth :: Double, -- Pin depth/priority (higher = processed first)
    warpPinSelected :: Maybe Bool, -- Is this pin selected in the UI
    warpPinInFront :: Maybe (AnimatableProperty Double) -- Overlap depth value (animatable, used by overlap type)
    -- Positive = in front of other mesh areas, Negative = behind
    -- Range: -100 to +100
  }
  deriving (Eq, Show, Generic)

instance ToJSON WarpPin where
  toJSON (WarpPin id_ name pinType position radius stiffness rotation scale depth selected inFront) =
    object $
      concat
        [ [ "id" .= id_,
            "name" .= name,
            "type" .= pinType,
            "position" .= position,
            "radius" .= radius,
            "stiffness" .= stiffness,
            "rotation" .= rotation,
            "scale" .= scale,
            "depth" .= depth
          ],
          maybe [] (\s -> ["selected" .= s]) selected,
          maybe [] (\inf -> ["inFront" .= inf]) inFront
        ]

instance FromJSON WarpPin where
  parseJSON = withObject "WarpPin" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    pinType <- o .: "type"
    position <- o .: "position"
    radius <- o .: "radius"
    stiffness <- o .: "stiffness"
    rotation <- o .: "rotation"
    scale <- o .: "scale"
    depth <- o .: "depth"
    selected <- o .:? "selected"
    inFront <- o .:? "inFront"
    -- Validate numeric ranges
    if validateFinite radius && validateNonNegative radius &&
       validateFinite stiffness && validateNormalized01 stiffness &&
       validateFinite depth
      then return (WarpPin id_ name pinType position radius stiffness rotation scale depth selected inFront)
      else fail "WarpPin: radius, stiffness, and depth must be finite and within valid ranges"

-- | Initial/rest state of a pin (before animation)
-- Used for calculating animation deltas
data WarpPinRestState = WarpPinRestState
  { warpPinRestStatePinId :: Text,
    warpPinRestStatePosition :: Vec2,
    warpPinRestStateRotation :: Double,
    warpPinRestStateScale :: Double,
    warpPinRestStateInFront :: Maybe Double -- Rest state for overlap depth (for overlap pins)
  }
  deriving (Eq, Show, Generic)

instance ToJSON WarpPinRestState where
  toJSON (WarpPinRestState pinId position rotation scale inFront) =
    object $
      concat
        [ [ "pinId" .= pinId,
            "position" .= position,
            "rotation" .= rotation,
            "scale" .= scale
          ],
          maybe [] (\inf -> ["inFront" .= inf]) inFront
        ]

instance FromJSON WarpPinRestState where
  parseJSON = withObject "WarpPinRestState" $ \o -> do
    pinId <- o .: "pinId"
    position <- o .: "position"
    rotation <- o .: "rotation"
    scale <- o .: "scale"
    inFront <- o .:? "inFront"
    if validateFinite rotation && validateFinite scale &&
       maybe True (\inf -> validateFinite inf && inf >= -100.0 && inf <= 100.0) inFront
      then return (WarpPinRestState pinId position rotation scale inFront)
      else fail "WarpPinRestState: rotation, scale, and inFront must be finite and within valid ranges"

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // mesh // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Control point for path reconstruction after deformation
data WarpControlPoint = WarpControlPoint
  { warpControlPointX :: Double,
    warpControlPointY :: Double,
    warpControlPointInHandle :: Vec2,
    warpControlPointOutHandle :: Vec2
  }
  deriving (Eq, Show, Generic)

instance ToJSON WarpControlPoint where
  toJSON (WarpControlPoint x y inHandle outHandle) =
    object
      [ "x" .= x,
        "y" .= y,
        "inHandle" .= inHandle,
        "outHandle" .= outHandle
      ]

instance FromJSON WarpControlPoint where
  parseJSON = withObject "WarpControlPoint" $ \o -> do
    x <- o .: "x"
    y <- o .: "y"
    inHandle <- o .: "inHandle"
    outHandle <- o .: "outHandle"
    if validateFinite x && validateFinite y
      then return (WarpControlPoint x y inHandle outHandle)
      else fail "WarpControlPoint: x and y must be finite numbers"

-- | Result of deforming a mesh
data WarpDeformationResult = WarpDeformationResult
  { warpDeformationResultVertices :: [Vec2], -- Deformed vertex positions
    warpDeformationResultControlPoints :: [WarpControlPoint] -- Deformed control point positions (for path reconstruction)
  }
  deriving (Eq, Show, Generic)

instance ToJSON WarpDeformationResult where
  toJSON (WarpDeformationResult vertices controlPoints) =
    object
      [ "vertices" .= vertices,
        "controlPoints" .= controlPoints
      ]

instance FromJSON WarpDeformationResult where
  parseJSON = withObject "WarpDeformationResult" $ \o -> do
    verticesRaw <- o .: "vertices"
    controlPoints <- o .: "controlPoints"
    -- Validate max 1,000,000 vertices per deformation result
    vertices <- case validateBoundedArray 1000000 verticesRaw of
      Left err -> fail (T.unpack err)
      Right vs -> return vs
    return (WarpDeformationResult vertices controlPoints)

-- | A triangulated mesh for warp deformation
--                                                                      // note
-- The weights array stores pinCount weights per vertex
data WarpMesh = WarpMesh
  { warpMeshLayerId :: Text, -- Layer this mesh belongs to
    warpMeshPins :: [WarpPin], -- Control pins for deformation
    warpMeshTriangulation :: [Int], -- Triangle indices (triplets of vertex indices)
    warpMeshWeights :: [Double], -- Pin influence weights per vertex (pinCount weights per vertex)
    warpMeshOriginalVertices :: [Vec2], -- Original (undeformed) vertex positions
    warpMeshPinRestStates :: [WarpPinRestState], -- Rest state of pins (for calculating deltas)
    warpMeshVertexCount :: Int, -- Number of vertices in the mesh
    warpMeshDirty :: Bool -- Whether mesh needs rebuild
  }
  deriving (Eq, Show, Generic)

instance ToJSON WarpMesh where
  toJSON (WarpMesh layerId pins triangulation weights originalVertices pinRestStates vertexCount dirty) =
    object
      [ "layerId" .= layerId,
        "pins" .= pins,
        "triangulation" .= triangulation,
        "weights" .= weights,
        "originalVertices" .= originalVertices,
        "pinRestStates" .= pinRestStates,
        "vertexCount" .= vertexCount,
        "dirty" .= dirty
      ]

instance FromJSON WarpMesh where
  parseJSON = withObject "WarpMesh" $ \o -> do
    layerId <- o .: "layerId"
    pins <- o .: "pins"
    triangulationRaw <- o .: "triangulation"
    weightsRaw <- o .: "weights"
    originalVertices <- o .: "originalVertices"
    pinRestStates <- o .: "pinRestStates"
    vertexCount <- o .: "vertexCount"
    dirty <- o .: "dirty"
    -- Validate max 10,000,000 triangle indices and weights
    triangulation <- case validateBoundedArray 10000000 triangulationRaw of
      Left err -> fail (T.unpack err)
      Right ts -> return ts
    weights <- case validateBoundedArray 10000000 weightsRaw of
      Left err -> fail (T.unpack err)
      Right ws -> return ws
    return (WarpMesh layerId pins triangulation weights originalVertices pinRestStates vertexCount dirty)

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // weight // calculation
-- ════════════════════════════════════════════════════════════════════════════

-- | Method for calculating pin influence weights
data WarpWeightMethod
  = WarpWeightMethodInverseDistance -- Standard 1/d^n falloff
  | WarpWeightMethodHeatDiffusion -- Heat equation simulation
  | WarpWeightMethodRadialBasis -- RBF interpolation
  | WarpWeightMethodBounded -- Bounded biharmonic weights
  deriving (Eq, Show, Generic)

instance ToJSON WarpWeightMethod where
  toJSON WarpWeightMethodInverseDistance = "inverse-distance"
  toJSON WarpWeightMethodHeatDiffusion = "heat-diffusion"
  toJSON WarpWeightMethodRadialBasis = "radial-basis"
  toJSON WarpWeightMethodBounded = "bounded"

instance FromJSON WarpWeightMethod where
  parseJSON = withText "WarpWeightMethod" $ \s ->
    case s of
      t | t == T.pack "inverse-distance" -> return WarpWeightMethodInverseDistance
      t | t == T.pack "heat-diffusion" -> return WarpWeightMethodHeatDiffusion
      t | t == T.pack "radial-basis" -> return WarpWeightMethodRadialBasis
      t | t == T.pack "bounded" -> return WarpWeightMethodBounded
      _ -> fail "Invalid WarpWeightMethod"

-- | Options for weight calculation
data WarpWeightOptions = WarpWeightOptions
  { warpWeightOptionsMethod :: WarpWeightMethod, -- Weight calculation method
    warpWeightOptionsFalloffPower :: Double, -- Falloff power for inverse-distance (typically 2)
    warpWeightOptionsNormalize :: Bool, -- Whether to normalize weights to sum to 1
    warpWeightOptionsMinWeight :: Double -- Minimum weight threshold (weights below this are set to 0)
  }
  deriving (Eq, Show, Generic)

instance ToJSON WarpWeightOptions where
  toJSON (WarpWeightOptions method falloffPower normalize minWeight) =
    object
      [ "method" .= method,
        "falloffPower" .= falloffPower,
        "normalize" .= normalize,
        "minWeight" .= minWeight
      ]

instance FromJSON WarpWeightOptions where
  parseJSON = withObject "WarpWeightOptions" $ \o -> do
    method <- o .: "method"
    falloffPower <- o .: "falloffPower"
    normalize <- o .: "normalize"
    minWeight <- o .: "minWeight"
    if validateFinite falloffPower && validateNonNegative falloffPower &&
       validateFinite minWeight && validateNonNegative minWeight && minWeight <= 1.0
      then return (WarpWeightOptions method falloffPower normalize minWeight)
      else fail "WarpWeightOptions: falloffPower and minWeight must be finite, non-negative, and minWeight <= 1.0"

-- | Default weight calculation options
defaultWarpWeightOptions :: WarpWeightOptions
defaultWarpWeightOptions =
  WarpWeightOptions
    { warpWeightOptionsMethod = WarpWeightMethodInverseDistance,
      warpWeightOptionsFalloffPower = 2.0,
      warpWeightOptionsNormalize = True,
      warpWeightOptionsMinWeight = 0.001
    }
