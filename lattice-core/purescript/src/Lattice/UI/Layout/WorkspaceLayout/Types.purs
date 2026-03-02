-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | WorkspaceLayout Types
-- |
-- | Shared types for the workspace layout module.
-- | Extracted to allow imports without circular dependencies.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Layout.WorkspaceLayout.Types
  ( GenerationMode(..)
  ) where

import Prelude

-- | Generation mode - determines which models are available in the UI
-- |
-- | Each mode presents different model options in the right sidebar:
-- | - TextToImage: Stable Diffusion, SDXL, Flux
-- | - ImageEdit: Inpainting models with mask support
-- | - ImageToVideo: Wan 2.2 I2V, CogVideoX, AnimateDiff
-- | - TextToVideo: Wan 2.2 T2V, direct video generation
-- | - TextTo3D: Triplane Gaussian, 3D generation models
data GenerationMode
  = TextToImage   -- T2I - Generate still image from prompt
  | ImageEdit     -- Edit - Inpaint/outpaint with mask
  | ImageToVideo  -- I2V - Animate an image with prompt
  | TextToVideo   -- T2V - Generate video from prompt
  | TextTo3D      -- 3D  - Generate 3D model from prompt/image

derive instance eqGenerationMode :: Eq GenerationMode
