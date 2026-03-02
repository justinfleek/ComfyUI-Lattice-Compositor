-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // worldmodel // anchorweave
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AnchorWeave - Local Spatial Memory for World-Consistent Video Generation
-- |
-- | Reference: arXiv 2602.14941 (UNC Chapel Hill, 2026)
-- |
-- | ## Key Insight
-- |
-- | Replace single noisy global 3D memory with multiple clean local
-- | geometric memories, then reconcile via multi-anchor weaving.
-- |
-- | ## Architecture
-- |
-- | ```
-- | Per-frame Local Point Clouds → Coverage-driven Retrieval
-- |                                        ↓
-- |                              Multiple Clean Anchors
-- |                                        ↓
-- |                          Multi-Anchor Weaving Controller
-- |                                        ↓
-- |                              Consistent Generation
-- | ```

module Hydrogen.WorldModel.AnchorWeave
  ( -- * Local Memory
    LocalMemory(..)
  , MemoryId(..)
  
  -- * Anchor System
  , Anchor(..)
  , AnchorSet(..)
  , emptyAnchorSet
  
  -- * Weaving Controller
  , WeavingController(..)
  , createController
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude (class Eq, class Show, show, (<>))

import Data.Array (length) as Array

import Hydrogen.Schema.Attestation.UUID5 (UUID5)
import Hydrogen.WorldModel.Types (Tensor, CameraPose)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // local // memory
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Unique memory identifier.
newtype MemoryId = MemoryId UUID5

derive instance eqMemoryId :: Eq MemoryId
instance showMemoryId :: Show MemoryId where
  show (MemoryId uuid) = "MemId(" <> show uuid <> ")"

-- | Per-frame local geometric memory.
-- |
-- | Unlike global point cloud memory, local memories don't accumulate
-- | cross-view misalignment errors.
data LocalMemory = LocalMemory
  { id :: MemoryId
  , pointCloud :: Tensor     -- Local 3D point cloud
  , cameraPose :: CameraPose -- Pose when captured
  , frameIndex :: Int        -- Source frame
  }

derive instance eqLocalMemory :: Eq LocalMemory
instance showLocalMemory :: Show LocalMemory where
  show (LocalMemory lm) = "LocalMemory{frame=" <> show lm.frameIndex <> "}"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // anchor // system
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Retrieved anchor from memory bank.
-- |
-- | Anchors are selected via coverage-driven retrieval to maximize
-- | visibility along the target camera trajectory.
data Anchor = Anchor
  { memory :: LocalMemory
  , coverage :: Number       -- How much of trajectory this covers
  , rendered :: Tensor       -- Rendered anchor video
  }

derive instance eqAnchor :: Eq Anchor
instance showAnchor :: Show Anchor where
  show (Anchor a) = "Anchor{coverage=" <> show a.coverage <> "}"

-- | Set of anchors for multi-anchor weaving.
newtype AnchorSet = AnchorSet (Array Anchor)

derive instance eqAnchorSet :: Eq AnchorSet
instance showAnchorSet :: Show AnchorSet where
  show (AnchorSet anchors) = 
    "AnchorSet[" <> show (Array.length anchors) <> "]"

-- | Create empty anchor set.
emptyAnchorSet :: AnchorSet
emptyAnchorSet = AnchorSet []

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // weaving // controller
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Multi-anchor weaving controller.
-- |
-- | Reconciles multiple anchor views through:
-- | 1. Shared cross-anchor attention
-- | 2. Pose-guided fusion
-- | 3. Learned reconciliation
data WeavingController = WeavingController

derive instance eqWeavingController :: Eq WeavingController
instance showWeavingController :: Show WeavingController where
  show WeavingController = "WeavingController"

-- | Create a weaving controller.
createController :: WeavingController
createController = WeavingController
