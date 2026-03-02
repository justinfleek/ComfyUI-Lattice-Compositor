{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Masks.MasksSchema
Description : Layer masks and track matte types
Copyright   : (c) Lattice, 2026
License     : MIT

Layer masks and track matte type enums.

Source: ui/src/schemas/masks/masks-schema.ts
-}

module Lattice.Schemas.Masks.MasksSchema
  ( -- * Matte Type
    MatteType(..)
  , matteTypeFromText
  , matteTypeToText
    -- * Mask Mode
  , MaskMode(..)
  , maskModeFromText
  , maskModeToText
    -- * Mask Vertex
  , MaskVertex(..)
    -- * Mask Path
  , MaskPath(..)
    -- * Constants
  , maxVertices
  , minClosedVertices
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Matte Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Track matte type options
data MatteType
  = MatteNone
  | MatteAlpha
  | MatteAlphaInverted
  | MatteLuma
  | MatteLumaInverted
  deriving stock (Eq, Show, Generic, Enum, Bounded)

matteTypeFromText :: Text -> Maybe MatteType
matteTypeFromText "none" = Just MatteNone
matteTypeFromText "alpha" = Just MatteAlpha
matteTypeFromText "alpha_inverted" = Just MatteAlphaInverted
matteTypeFromText "luma" = Just MatteLuma
matteTypeFromText "luma_inverted" = Just MatteLumaInverted
matteTypeFromText _ = Nothing

matteTypeToText :: MatteType -> Text
matteTypeToText MatteNone = "none"
matteTypeToText MatteAlpha = "alpha"
matteTypeToText MatteAlphaInverted = "alpha_inverted"
matteTypeToText MatteLuma = "luma"
matteTypeToText MatteLumaInverted = "luma_inverted"

-- ────────────────────────────────────────────────────────────────────────────
-- Mask Mode
-- ────────────────────────────────────────────────────────────────────────────

-- | Mask mode options
data MaskMode
  = MaskAdd
  | MaskSubtract
  | MaskIntersect
  | MaskLighten
  | MaskDarken
  | MaskDifference
  | MaskNone
  deriving stock (Eq, Show, Generic, Enum, Bounded)

maskModeFromText :: Text -> Maybe MaskMode
maskModeFromText "add" = Just MaskAdd
maskModeFromText "subtract" = Just MaskSubtract
maskModeFromText "intersect" = Just MaskIntersect
maskModeFromText "lighten" = Just MaskLighten
maskModeFromText "darken" = Just MaskDarken
maskModeFromText "difference" = Just MaskDifference
maskModeFromText "none" = Just MaskNone
maskModeFromText _ = Nothing

maskModeToText :: MaskMode -> Text
maskModeToText MaskAdd = "add"
maskModeToText MaskSubtract = "subtract"
maskModeToText MaskIntersect = "intersect"
maskModeToText MaskLighten = "lighten"
maskModeToText MaskDarken = "darken"
maskModeToText MaskDifference = "difference"
maskModeToText MaskNone = "none"

-- ────────────────────────────────────────────────────────────────────────────
-- Mask Vertex
-- ────────────────────────────────────────────────────────────────────────────

-- | Mask vertex with bezier tangents
data MaskVertex = MaskVertex
  { mvX :: !Double
  , mvY :: !Double
  , mvInTangentX :: !Double
  , mvInTangentY :: !Double
  , mvOutTangentX :: !Double
  , mvOutTangentY :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Mask Path
-- ────────────────────────────────────────────────────────────────────────────

-- | Mask path structure
data MaskPath = MaskPath
  { mpClosed :: !Bool
  , mpVertices :: ![MaskVertex]
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxVertices :: Int
maxVertices = 10000

minClosedVertices :: Int
minClosedVertices = 3
