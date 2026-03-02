{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.MeshWarp.MeshWarpSchema
Description : Mesh deformation pin types and weight methods
Copyright   : (c) Lattice, 2026
License     : MIT

Mesh deformation pin types and weight methods.

Source: ui/src/schemas/meshWarp/meshWarp-schema.ts
-}

module Lattice.Schemas.MeshWarp.MeshWarpSchema
  ( -- * Warp Pin Type
    WarpPinType(..)
  , warpPinTypeFromText
  , warpPinTypeToText
    -- * Warp Weight Method
  , WarpWeightMethod(..)
  , warpWeightMethodFromText
  , warpWeightMethodToText
    -- * Structures
  , Position2D(..)
  , WarpWeightOptions(..)
    -- * Constants
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

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Warp Pin Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Warp pin type options
data WarpPinType
  = PinPosition
  | PinRotation
  | PinStarch
  | PinOverlap
  | PinBend
  | PinAdvanced
  deriving stock (Eq, Show, Generic, Enum, Bounded)

warpPinTypeFromText :: Text -> Maybe WarpPinType
warpPinTypeFromText "position" = Just PinPosition
warpPinTypeFromText "rotation" = Just PinRotation
warpPinTypeFromText "starch" = Just PinStarch
warpPinTypeFromText "overlap" = Just PinOverlap
warpPinTypeFromText "bend" = Just PinBend
warpPinTypeFromText "advanced" = Just PinAdvanced
warpPinTypeFromText _ = Nothing

warpPinTypeToText :: WarpPinType -> Text
warpPinTypeToText PinPosition = "position"
warpPinTypeToText PinRotation = "rotation"
warpPinTypeToText PinStarch = "starch"
warpPinTypeToText PinOverlap = "overlap"
warpPinTypeToText PinBend = "bend"
warpPinTypeToText PinAdvanced = "advanced"

-- ────────────────────────────────────────────────────────────────────────────
-- Warp Weight Method
-- ────────────────────────────────────────────────────────────────────────────

-- | Warp weight method options
data WarpWeightMethod
  = WeightInverseDistance
  | WeightHeatDiffusion
  | WeightRadialBasis
  | WeightBounded
  deriving stock (Eq, Show, Generic, Enum, Bounded)

warpWeightMethodFromText :: Text -> Maybe WarpWeightMethod
warpWeightMethodFromText "inverse-distance" = Just WeightInverseDistance
warpWeightMethodFromText "heat-diffusion" = Just WeightHeatDiffusion
warpWeightMethodFromText "radial-basis" = Just WeightRadialBasis
warpWeightMethodFromText "bounded" = Just WeightBounded
warpWeightMethodFromText _ = Nothing

warpWeightMethodToText :: WarpWeightMethod -> Text
warpWeightMethodToText WeightInverseDistance = "inverse-distance"
warpWeightMethodToText WeightHeatDiffusion = "heat-diffusion"
warpWeightMethodToText WeightRadialBasis = "radial-basis"
warpWeightMethodToText WeightBounded = "bounded"

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D position
data Position2D = Position2D
  { posX :: !Double
  , posY :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Warp weight options
data WarpWeightOptions = WarpWeightOptions
  { wwoMethod :: !WarpWeightMethod
  , wwoFalloffPower :: !Double
  , wwoNormalize :: !Bool
  , wwoMinWeight :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxPins :: Int
maxPins = 10000

maxRadius :: Double
maxRadius = 10000.0

maxDepth :: Double
maxDepth = 10000.0

maxScale :: Double
maxScale = 100.0

maxFalloffPower :: Double
maxFalloffPower = 100.0

maxVertices :: Int
maxVertices = 10000000

maxControlPoints :: Int
maxControlPoints = 100000

maxWeights :: Int
maxWeights = 100000000

maxTriangles :: Int
maxTriangles = 10000000
