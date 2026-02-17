-- |
-- Module      : Lattice.Types.MeshWarp.Helpers
-- Description : Helper functions for creating default mesh warp instances
-- 
-- Migrated from ui/src/types/meshWarp.ts factory functions
-- Pure functions for creating default mesh warp configurations
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.MeshWarp.Helpers
  ( createDefaultWarpPin,
    createEmptyWarpMesh,
    getPinDefaultName,
  )
where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Animation
  ( AnimatableProperty (..),
    PropertyType (..),
    createAnimatableProperty,
  )
import Lattice.Types.MeshWarp.Core
  ( WarpMesh (..),
    WarpPin (..),
    WarpPinRestState (..),
    WarpPinType (..),
  )
import Lattice.Types.Primitives (Vec2 (..))

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Get default name based on pin type
-- Uses last 4 characters of ID as suffix
getPinDefaultName :: WarpPinType -> Text -> Text
getPinDefaultName pinType id_ =
  let suffix = T.takeEnd 4 id_
      baseName = case pinType of
        WarpPinTypePosition -> "Deform"
        WarpPinTypeStarch -> "Stiffness"
        WarpPinTypeOverlap -> "Overlap"
        WarpPinTypeBend -> "Bend"
        WarpPinTypeAdvanced -> "Advanced"
        _ -> "Pin"
   in baseName <> " " <> suffix

-- ============================================================================
-- MESH WARP FACTORIES
-- ============================================================================

-- | Create a default warp pin
-- NOTE: ID generation should be handled by caller (no IO in pure functions)
createDefaultWarpPin ::
  Text -> -- id
  Double -> -- x
  Double -> -- y
  WarpPinType -> -- type (defaults to position)
  WarpPin
createDefaultWarpPin id_ x y pinType =
  let pin =
        WarpPin
          { warpPinId = id_,
            warpPinName = getPinDefaultName pinType id_,
            warpPinType = pinType,
            warpPinPosition =
              createAnimatableProperty
                ("pin_pos_" <> id_)
                "Position"
                (Vec2 x y)
                PropertyTypePosition
                Nothing,
            warpPinRadius = 50.0,
            warpPinStiffness = if pinType == WarpPinTypeStarch then 1.0 else 0.0,
            warpPinRotation =
              createAnimatableProperty
                ("pin_rot_" <> id_)
                "Rotation"
                0.0
                PropertyTypeNumber
                Nothing,
            warpPinScale =
              createAnimatableProperty
                ("pin_scale_" <> id_)
                "Scale"
                1.0
                PropertyTypeNumber
                Nothing,
            warpPinDepth = 0.0,
            warpPinSelected = Just False,
            warpPinInFront = Nothing
          }
   in -- Add inFront property for overlap pins
      if pinType == WarpPinTypeOverlap
        then
          pin
            { warpPinInFront =
                Just
                  ( createAnimatableProperty
                      ("pin_infront_" <> id_)
                      "In Front"
                      0.0
                      PropertyTypeNumber
                      Nothing
                  )
            }
        else pin

-- | Create an empty warp mesh
-- NOTE: Float32Array in TypeScript is represented as [Double] in Haskell
createEmptyWarpMesh :: Text -> WarpMesh
createEmptyWarpMesh layerId =
  WarpMesh
    { warpMeshLayerId = layerId,
      warpMeshPins = [],
      warpMeshTriangulation = [],
      warpMeshWeights = [], -- Float32Array(0) in TypeScript
      warpMeshOriginalVertices = [], -- Float32Array(0) in TypeScript
      warpMeshPinRestStates = [],
      warpMeshVertexCount = 0,
      warpMeshDirty = True
    }
