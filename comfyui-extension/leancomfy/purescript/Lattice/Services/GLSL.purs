-- | Lattice.Services.GLSL - GLSL shader services re-exports
-- |
-- | GPU-accelerated image processing using WebGL shaders.
-- | Shadertoy-compatible uniform system for easy shader authoring.
-- |
-- | Acknowledgement: Inspired by Jovi/Amorano's Jovi_GLSL
-- |
-- | Source: ui/src/services/glsl/

module Lattice.Services.GLSL
  ( module Types
  , module Library
  , module Engine
  ) where

import Lattice.Services.GLSL.Types as Types
import Lattice.Services.GLSL.Library as Library
import Lattice.Services.GLSL.Engine as Engine
