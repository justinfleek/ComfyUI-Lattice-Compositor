-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // matroid // partition
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Partition Matroid for Render Tier Constraints
-- |
-- | A partition matroid is defined by:
-- | - A partition of the ground set E = P₁ ∪ P₂ ∪ ... ∪ Pₘ
-- | - Cardinality bounds k₁, k₂, ..., kₘ for each partition
-- | - A set S is independent iff |S ∩ Pᵢ| ≤ kᵢ for all i
-- |
-- | ## Render Tier Application
-- |
-- | For adaptive rendering, we partition regions into three tiers:
-- | - **Foveal** (P₁): High-priority gaze-centered regions, k₁ = 8
-- | - **Peripheral** (P₂): Medium-priority context regions, k₂ = 16
-- | - **Background** (P₃): Low-priority ambient regions, k₃ = 32
-- |
-- | Total budget: 56 regions per frame
-- |
-- | This partition reflects the human visual system: highest quality where
-- | the user is looking (fovea), moderate quality in peripheral vision,
-- | and minimum quality in the background.

module Hydrogen.Render.Online.Matroid.Partition
  ( -- * Tiered Partition Matroid
    TieredPartitionMatroid(..)
  , mkTieredPartitionMatroid
  , defaultTierBounds
  
  -- * Tier Counts
  , TierCounts(..)
  , countByTier
  , emptyTierCounts
  
  -- * Bounds Configuration
  , TierBounds(..)
  , mkTierBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , otherwise
  , show
  , ($)
  , (+)
  , (&&)
  , (<=)
  , (<>)
  , (>=)
  )

import Data.Foldable (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set (Set)
import Data.Set as Set

import Hydrogen.Render.Online.Core
  ( Region(..)
  , RegionSelection(..)
  , RenderTier(Foveal, Peripheral, Background)
  )
import Hydrogen.Render.Online.Matroid.Class (class Matroid, independent)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // tier // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for each render tier
-- |
-- | Specifies the maximum number of regions that can be selected from each tier.
-- | All bounds are strictly positive and have sensible upper limits.
newtype TierBounds = TierBounds
  { fovealBound :: Int       -- Max selections from foveal tier [1, 16]
  , peripheralBound :: Int   -- Max selections from peripheral tier [1, 32]
  , backgroundBound :: Int   -- Max selections from background tier [1, 64]
  }

derive instance eqTierBounds :: Eq TierBounds

instance showTierBounds :: Show TierBounds where
  show (TierBounds b) = 
    "TierBounds(foveal=" <> show b.fovealBound <> 
    ", peripheral=" <> show b.peripheralBound <> 
    ", background=" <> show b.backgroundBound <> ")"

-- | Construct tier bounds with validation
-- |
-- | Returns Nothing if any bound is out of valid range.
mkTierBounds :: Int -> Int -> Int -> Maybe TierBounds
mkTierBounds foveal peripheral background
  | foveal >= 1 && foveal <= 16
  , peripheral >= 1 && peripheral <= 32
  , background >= 1 && background <= 64
  = Just (TierBounds
      { fovealBound: foveal
      , peripheralBound: peripheral
      , backgroundBound: background
      })
  | otherwise = Nothing

-- | Default tier bounds from ML expert analysis
-- |
-- | - Foveal: 8 (high quality, ~14% of budget)
-- | - Peripheral: 16 (medium quality, ~29% of budget)  
-- | - Background: 32 (low quality, ~57% of budget)
-- |
-- | Total: 56 regions per frame
defaultTierBounds :: TierBounds
defaultTierBounds = TierBounds
  { fovealBound: 8
  , peripheralBound: 16
  , backgroundBound: 32
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // tier // counts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Count of selections per tier
newtype TierCounts = TierCounts
  { fovealCount :: Int
  , peripheralCount :: Int
  , backgroundCount :: Int
  }

derive instance eqTierCounts :: Eq TierCounts

instance showTierCounts :: Show TierCounts where
  show (TierCounts c) =
    "TierCounts(foveal=" <> show c.fovealCount <>
    ", peripheral=" <> show c.peripheralCount <>
    ", background=" <> show c.backgroundCount <> ")"

-- | Empty tier counts (all zeros)
emptyTierCounts :: TierCounts
emptyTierCounts = TierCounts
  { fovealCount: 0
  , peripheralCount: 0
  , backgroundCount: 0
  }

-- | Count selections by their tier assignment
-- |
-- | Iterates through selections and tallies by tier.
countByTier :: Set RegionSelection -> TierCounts
countByTier selections =
  foldl addToCount emptyTierCounts (Set.toUnfoldable selections :: Array RegionSelection)

-- | Add a selection to the appropriate tier count
addToCount :: TierCounts -> RegionSelection -> TierCounts
addToCount (TierCounts counts) (RegionSelection { region: Region r }) =
  case r.tier of
    Foveal -> TierCounts counts { fovealCount = counts.fovealCount + 1 }
    Peripheral -> TierCounts counts { peripheralCount = counts.peripheralCount + 1 }
    Background -> TierCounts counts { backgroundCount = counts.backgroundCount + 1 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // tiered // partition // matroid
-- ═════════════════════════════════════════════════════════════════════════════

-- | Partition matroid over render tiers
-- |
-- | The ground set is partitioned into three tiers based on render priority.
-- | A selection is independent (feasible) if the count from each tier does
-- | not exceed the tier's bound.
-- |
-- | This encodes the constraint: "At most k₁ foveal, k₂ peripheral, k₃ background"
newtype TieredPartitionMatroid = TieredPartitionMatroid TierBounds

derive instance eqTieredPartitionMatroid :: Eq TieredPartitionMatroid

instance showTieredPartitionMatroid :: Show TieredPartitionMatroid where
  show (TieredPartitionMatroid bounds) = 
    "TieredPartitionMatroid(" <> show bounds <> ")"

-- | Construct a tiered partition matroid with bounds
mkTieredPartitionMatroid :: TierBounds -> TieredPartitionMatroid
mkTieredPartitionMatroid = TieredPartitionMatroid

-- | Matroid instance for region selection
-- |
-- | A set of selections is independent iff:
-- | - foveal count ≤ foveal bound
-- | - peripheral count ≤ peripheral bound
-- | - background count ≤ background bound
instance matroidTieredPartition :: Matroid TieredPartitionMatroid RegionSelection where
  independent (TieredPartitionMatroid (TierBounds bounds)) selections =
    let TierCounts counts = countByTier selections
    in counts.fovealCount <= bounds.fovealBound
       && counts.peripheralCount <= bounds.peripheralBound
       && counts.backgroundCount <= bounds.backgroundBound
  
  rank (TieredPartitionMatroid (TierBounds bounds)) =
    bounds.fovealBound + bounds.peripheralBound + bounds.backgroundBound
  
  extend matroid current candidate =
    let extended = Set.insert candidate current
    in if independent matroid extended
         then Just extended
         else Nothing
