-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Layer Factory Types
-- |
-- | Types for generated assets and layers.
-- | Separated to avoid circular dependencies.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.Services.LayerFactory.Types
  ( GeneratedAsset
  , GeneratedLayer
  ) where

import Lattice.Primitives (NonEmptyString)
import Lattice.Project (LayerBase)

-- | Asset created from generation (frames stored as base64)
type GeneratedAsset =
  { id :: NonEmptyString
  , frames :: Array String    -- Base64 encoded frames
  , isVideo :: Boolean        -- true if multiple frames
  , width :: Int
  , height :: Int
  , model :: String           -- Model used for generation
  , prompt :: String          -- Prompt used
  , seed :: Int               -- Seed used
  }

-- | Result of layer creation
type GeneratedLayer =
  { layer :: LayerBase
  , asset :: GeneratedAsset
  }
