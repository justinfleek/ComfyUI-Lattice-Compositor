-- | Lattice.Schemas.MeshWarp.MeshWarpSchema - Mesh deformation pin types and weight methods
-- |
-- | Mesh deformation pin types and weight methods.
-- |
-- | Source: ui/src/schemas/meshWarp/meshWarp-schema.ts

module Lattice.Schemas.MeshWarp.MeshWarpSchema
  ( -- Warp Pin Type
    WarpPinType(..)
  , warpPinTypeFromString
  , warpPinTypeToString
    -- Warp Weight Method
  , WarpWeightMethod(..)
  , warpWeightMethodFromString
  , warpWeightMethodToString
    -- Structures
  , Position2D
  , WarpWeightOptions
    -- Constants
  , maxPins
  , maxRadius
  , maxDepth
  , maxScale
  , maxFalloffPower
  , maxVertices
  , maxControlPoints
  , maxWeights
  , maxTriangles
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Warp Pin Type
--------------------------------------------------------------------------------

-- | Warp pin type options
data WarpPinType
  = PinPosition
  | PinRotation
  | PinStarch
  | PinOverlap
  | PinBend
  | PinAdvanced

derive instance Eq WarpPinType
derive instance Generic WarpPinType _

instance Show WarpPinType where
  show = genericShow

warpPinTypeFromString :: String -> Maybe WarpPinType
warpPinTypeFromString = case _ of
  "position" -> Just PinPosition
  "rotation" -> Just PinRotation
  "starch" -> Just PinStarch
  "overlap" -> Just PinOverlap
  "bend" -> Just PinBend
  "advanced" -> Just PinAdvanced
  _ -> Nothing

warpPinTypeToString :: WarpPinType -> String
warpPinTypeToString = case _ of
  PinPosition -> "position"
  PinRotation -> "rotation"
  PinStarch -> "starch"
  PinOverlap -> "overlap"
  PinBend -> "bend"
  PinAdvanced -> "advanced"

--------------------------------------------------------------------------------
-- Warp Weight Method
--------------------------------------------------------------------------------

-- | Warp weight method options
data WarpWeightMethod
  = WeightInverseDistance
  | WeightHeatDiffusion
  | WeightRadialBasis
  | WeightBounded

derive instance Eq WarpWeightMethod
derive instance Generic WarpWeightMethod _

instance Show WarpWeightMethod where
  show = genericShow

warpWeightMethodFromString :: String -> Maybe WarpWeightMethod
warpWeightMethodFromString = case _ of
  "inverse-distance" -> Just WeightInverseDistance
  "heat-diffusion" -> Just WeightHeatDiffusion
  "radial-basis" -> Just WeightRadialBasis
  "bounded" -> Just WeightBounded
  _ -> Nothing

warpWeightMethodToString :: WarpWeightMethod -> String
warpWeightMethodToString = case _ of
  WeightInverseDistance -> "inverse-distance"
  WeightHeatDiffusion -> "heat-diffusion"
  WeightRadialBasis -> "radial-basis"
  WeightBounded -> "bounded"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | 2D position
type Position2D =
  { x :: Number
  , y :: Number
  }

-- | Warp weight options
type WarpWeightOptions =
  { method :: WarpWeightMethod
  , falloffPower :: Number
  , normalize :: Boolean
  , minWeight :: Number
  }

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxPins :: Int
maxPins = 10000

maxRadius :: Number
maxRadius = 10000.0

maxDepth :: Number
maxDepth = 10000.0

maxScale :: Number
maxScale = 100.0

maxFalloffPower :: Number
maxFalloffPower = 100.0

maxVertices :: Int
maxVertices = 10000000

maxControlPoints :: Int
maxControlPoints = 100000

maxWeights :: Int
maxWeights = 100000000

maxTriangles :: Int
maxTriangles = 10000000
