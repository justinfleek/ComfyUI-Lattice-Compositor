-- | Lattice.Schemas.Masks.MasksSchema - Layer masks and track matte types
-- |
-- | Layer masks and track matte type enums.
-- |
-- | Source: ui/src/schemas/masks/masks-schema.ts

module Lattice.Schemas.Masks.MasksSchema
  ( -- Matte Type
    MatteType(..)
  , matteTypeFromString
  , matteTypeToString
    -- Mask Mode
  , MaskMode(..)
  , maskModeFromString
  , maskModeToString
    -- Mask Vertex
  , MaskVertex
    -- Mask Path
  , MaskPath
    -- Constants
  , maxVertices
  , minClosedVertices
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Matte Type
--------------------------------------------------------------------------------

-- | Track matte type options
data MatteType
  = MatteNone
  | MatteAlpha
  | MatteAlphaInverted
  | MatteLuma
  | MatteLumaInverted

derive instance Eq MatteType
derive instance Generic MatteType _

instance Show MatteType where
  show = genericShow

matteTypeFromString :: String -> Maybe MatteType
matteTypeFromString = case _ of
  "none" -> Just MatteNone
  "alpha" -> Just MatteAlpha
  "alpha_inverted" -> Just MatteAlphaInverted
  "luma" -> Just MatteLuma
  "luma_inverted" -> Just MatteLumaInverted
  _ -> Nothing

matteTypeToString :: MatteType -> String
matteTypeToString = case _ of
  MatteNone -> "none"
  MatteAlpha -> "alpha"
  MatteAlphaInverted -> "alpha_inverted"
  MatteLuma -> "luma"
  MatteLumaInverted -> "luma_inverted"

--------------------------------------------------------------------------------
-- Mask Mode
--------------------------------------------------------------------------------

-- | Mask mode options
data MaskMode
  = MaskAdd
  | MaskSubtract
  | MaskIntersect
  | MaskLighten
  | MaskDarken
  | MaskDifference
  | MaskNone

derive instance Eq MaskMode
derive instance Generic MaskMode _

instance Show MaskMode where
  show = genericShow

maskModeFromString :: String -> Maybe MaskMode
maskModeFromString = case _ of
  "add" -> Just MaskAdd
  "subtract" -> Just MaskSubtract
  "intersect" -> Just MaskIntersect
  "lighten" -> Just MaskLighten
  "darken" -> Just MaskDarken
  "difference" -> Just MaskDifference
  "none" -> Just MaskNone
  _ -> Nothing

maskModeToString :: MaskMode -> String
maskModeToString = case _ of
  MaskAdd -> "add"
  MaskSubtract -> "subtract"
  MaskIntersect -> "intersect"
  MaskLighten -> "lighten"
  MaskDarken -> "darken"
  MaskDifference -> "difference"
  MaskNone -> "none"

--------------------------------------------------------------------------------
-- Mask Vertex
--------------------------------------------------------------------------------

-- | Mask vertex with bezier tangents
type MaskVertex =
  { x :: Number
  , y :: Number
  , inTangentX :: Number
  , inTangentY :: Number
  , outTangentX :: Number
  , outTangentY :: Number
  }

--------------------------------------------------------------------------------
-- Mask Path
--------------------------------------------------------------------------------

-- | Mask path structure
type MaskPath =
  { closed :: Boolean
  , vertices :: Array MaskVertex
  }

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxVertices :: Int
maxVertices = 10000

minClosedVertices :: Int
minClosedVertices = 3
