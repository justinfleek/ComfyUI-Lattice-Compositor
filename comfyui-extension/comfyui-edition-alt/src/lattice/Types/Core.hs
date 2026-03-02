-- |
-- Module      : Lattice.Types.Core
-- Description : Core types for Lattice Compositor
-- 
-- Basic types used throughout the system
-- Migrated from ui/src/types/project.ts (core types only)
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Core
  ( Point(..)
  , BoundingBox(..)
  , ColorSpace(..)
  , ViewTransform(..)
  ) where

import Data.Aeson (ToJSON, FromJSON)
import GHC.Generics (Generic)
import Lattice.Types.Primitives (BlendMode)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // utility // types
-- ════════════════════════════════════════════════════════════════════════════

data Point = Point
  { pointX :: Double
  , pointY :: Double
  }
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

data BoundingBox = BoundingBox
  { boundingBoxX :: Double
  , boundingBoxY :: Double
  , boundingBoxWidth :: Double
  , boundingBoxHeight :: Double
  }
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- BlendMode is now in Lattice.Types.Primitives (re-exported above)

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // color // space // types
-- ════════════════════════════════════════════════════════════════════════════

data ColorSpace
  = ColorSpaceSRGB
  | ColorSpaceLinearSRGB
  | ColorSpaceWideGamutRGB
  | ColorSpaceDisplayP3
  | ColorSpaceProPhotoRGB
  | ColorSpaceACEScg
  | ColorSpaceRec709
  | ColorSpaceRec2020
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

data ViewTransform
  = ViewTransformSRGB
  | ViewTransformDisplayP3
  | ViewTransformRec709
  | ViewTransformACES_SRGB
  | ViewTransformFilmic
  deriving (Eq, Show, Generic, ToJSON, FromJSON)
