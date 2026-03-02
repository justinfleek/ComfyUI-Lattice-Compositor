-- |
-- Module      : Lattice.Types.Masks.Helpers
-- Description : Helper functions for creating default mask instances
-- 
-- Migrated from ui/src/types/masks.ts factory functions
-- Pure functions for creating default mask configurations
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.Masks.Helpers
  ( createDefaultMask,
    createEllipseMask,
  )
where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Animation
  ( AnimatableProperty (..),
    PropertyType (..),
    createAnimatableProperty,
  )
import Lattice.Types.Masks.Core
  ( LayerMask (..),
    MaskMode (..),
    MaskPath (..),
    MaskVertex (..),
  )

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Create a mask AnimatableProperty
-- NOTE: ID generation should be handled by caller (no IO in pure functions)
createMaskAnimatableProperty ::
  Text ->
  a ->
  PropertyType ->
  AnimatableProperty a
createMaskAnimatableProperty name value propType =
  createAnimatableProperty
    ("mask_prop_" <> name <> "_prop")
    name
    value
    propType
    Nothing

-- ============================================================================
-- MASK FACTORIES
-- ============================================================================

-- | Create a default rectangular mask covering the full layer
createDefaultMask :: Text -> Double -> Double -> LayerMask
createDefaultMask id_ width height =
  LayerMask
    { layerMaskId = id_,
      layerMaskName = "Mask 1",
      layerMaskEnabled = True,
      layerMaskLocked = False,
      layerMaskMode = MaskModeAdd,
      layerMaskInverted = False,
      layerMaskPath =
        createMaskAnimatableProperty
          "Mask Path"
          ( MaskPath
              True
              [ MaskVertex 0.0 0.0 0.0 0.0 0.0 0.0,
                MaskVertex width 0.0 0.0 0.0 0.0 0.0,
                MaskVertex width height 0.0 0.0 0.0 0.0,
                MaskVertex 0.0 height 0.0 0.0 0.0 0.0
              ]
          )
          PropertyTypePosition,
      layerMaskOpacity = createMaskAnimatableProperty "Mask Opacity" 100.0 PropertyTypeNumber,
      layerMaskFeather = createMaskAnimatableProperty "Mask Feather" 0.0 PropertyTypeNumber,
      layerMaskFeatherX = Nothing,
      layerMaskFeatherY = Nothing,
      layerMaskExpansion = createMaskAnimatableProperty "Mask Expansion" 0.0 PropertyTypeNumber,
      layerMaskColor = "#FFFF00" -- Yellow default
    }

-- | Create an elliptical mask
-- Uses bezier approximation of ellipse (kappa = 4 * (sqrt(2) - 1) / 3)
createEllipseMask ::
  Text ->
  Double -> -- centerX
  Double -> -- centerY
  Double -> -- radiusX
  Double -> -- radiusY
  LayerMask
createEllipseMask id_ centerX centerY radiusX radiusY =
  let kappa = 0.5522847498 -- Bezier approximation constant
      ox = radiusX * kappa -- Control point offset horizontal
      oy = radiusY * kappa -- Control point offset vertical
   in LayerMask
        { layerMaskId = id_,
          layerMaskName = "Mask 1",
          layerMaskEnabled = True,
          layerMaskLocked = False,
          layerMaskMode = MaskModeAdd,
          layerMaskInverted = False,
          layerMaskPath =
            createMaskAnimatableProperty
              "Mask Path"
              ( MaskPath
                  True
                  [ MaskVertex
                      centerX
                      (centerY - radiusY)
                      (-ox)
                      0.0
                      ox
                      0.0,
                    MaskVertex
                      (centerX + radiusX)
                      centerY
                      0.0
                      (-oy)
                      0.0
                      oy,
                    MaskVertex
                      centerX
                      (centerY + radiusY)
                      ox
                      0.0
                      (-ox)
                      0.0,
                    MaskVertex
                      (centerX - radiusX)
                      centerY
                      0.0
                      oy
                      0.0
                      (-oy)
                  ]
              )
              PropertyTypePosition,
          layerMaskOpacity = createMaskAnimatableProperty "Mask Opacity" 100.0 PropertyTypeNumber,
          layerMaskFeather = createMaskAnimatableProperty "Mask Feather" 0.0 PropertyTypeNumber,
          layerMaskFeatherX = Nothing,
          layerMaskFeatherY = Nothing,
          layerMaskExpansion = createMaskAnimatableProperty "Mask Expansion" 0.0 PropertyTypeNumber,
          layerMaskColor = "#00FFFF" -- Cyan
        }
