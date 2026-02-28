-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // gpu // framestate // allocation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FrameState.Allocation — Viewport Allocation via Submodular Optimization
-- |
-- | ## Purpose
-- |
-- | This module bridges GPU FrameState infrastructure with submodular optimization,
-- | enabling intelligent allocation of rendering resources across viewport regions.
-- |
-- | ## Integration Points
-- |
-- | - ViewportState → GroundSet Region (map latent grid to optimization elements)
-- | - PerformanceState → UtilityFeedback (convert GPU timing to learning signal)
-- | - OnlineState → RegionSelection[] (output allocation decisions)
-- |
-- | ## Architecture
-- |
-- | ```
-- | ViewportTensor (latent grid)
-- |        ↓
-- | viewportToGroundSet
-- |        ↓
-- | GroundSet Region
-- |        ↓
-- | onlineStep (from Optimize.Submodular.Online)
-- |        ↓
-- | RegionSelection[]
-- |        ↓
-- | GPU Render (external)
-- |        ↓
-- | performanceToFeedback
-- |        ↓
-- | UtilityFeedback
-- |        ↓
-- | onlineStep (next frame)
-- | ```
-- |
-- | ## Council Decision (2026-02-25)
-- |
-- | This module implements P0 from the FAA Council Deliberation:
-- | "Integration before optimization" — wire existing infrastructure before
-- | adding algorithmic enhancements.

module Hydrogen.GPU.FrameState.Allocation
  ( -- * Viewport to Ground Set Conversion
    viewportToRegions
  , viewportToGroundSet
  , selectGridLevel
  
  -- * Performance to Feedback Conversion
  , performanceToFeedback
  , qualityFromPerformance
  , mkQuality
  , mkUtility
  
  -- * Region Queries
  , regionCoord
  , adjacentRegions
  , regionsInTier
  
  -- * Safe Step Construction
  , safeSteps
  
  -- * Allocation State
  , AllocationState
  , mkAllocationState
  , allocationEpoch
  , allocationRegions
  
  -- * Frame Allocation
  , allocateFrame
  , AllocationResult
  
  -- * FAA-Enhanced Allocation (P2)
  , FAAAllocationConfig(FAAAllocationConfig)
  , mkFAAAllocationConfig
  , allocateFrameFAA
  , regionsToGroundSetFAA
  , regionUtilityOracle
  , RegionIndex
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , map
  , max
  , min
  , show
  , ($)
  , (*)
  , (+)
  , (-)
  , (/)
  , (<)
  , (<>)
  , (==)
  , (/=)
  , (>)
  , (>=)
  , (&&)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set as Set

-- FrameState types
import Hydrogen.GPU.FrameState
  ( ViewportState
  , PerformanceState
  , viewportLatentWidth
  , viewportLatentHeight
  , gpuBudgetMs
  , gpuUsedMs
  )

-- Render.Online types (rendering-specific)
import Hydrogen.Render.Online.Core
  ( GridLevel(Coarse, Medium, Fine)
  , GridCoord(GridCoord)
  , mkGridCoord
  , gridLevelSize
  , RenderTier(Foveal, Peripheral, Background)
  , RegionId(RegionId)
  , Region(Region)
  , RegionSelection(RegionSelection)
  , DiffusionSteps(DiffusionSteps)
  , mkDiffusionSteps
  , tierDefaultSteps
  , Quality(Quality)
  , Utility(Utility)
  , EpochId(EpochId)
  , nextEpoch
  , clampToBounds
  )

-- Submodular Optimization Types
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , ElementSet
  , GroundSet(GroundSet)
  , SubmodularOracle(SubmodularOracle)
  , SetValue(SetValue)
  , MarginalGain(MarginalGain)
  , CardinalityMatroid(CardinalityMatroid)
  )

-- FAA-Enhanced Continuous Greedy
import Hydrogen.Optimize.Submodular.Continuous
  ( mkFAAConfig
  , continuousGreedyFAA
  , FractionalSolution
  , solutionCoord
  )

-- Min-Energy Rounding
import Hydrogen.Optimize.Submodular.Rounding
  ( mkMinEnergyConfig
  , minEnergyRound
  )

-- Dimension type
import Hydrogen.Schema.Tensor.Dimension (Dim(Dim))

-- Math functions
import Hydrogen.Math.Core (sqrt) as Math

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // viewport // to // regions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Select appropriate grid level based on viewport latent dimensions.
-- |
-- | Heuristic:
-- | - Fine (32×32) for large viewports (latent >= 64 in both dimensions)
-- | - Medium (16×16) for standard viewports (latent >= 32)
-- | - Coarse (8×8) for small viewports or constrained rendering
-- |
-- | This ensures reasonable region sizes: ~4-8 latent pixels per region.
selectGridLevel :: Int -> Int -> GridLevel
selectGridLevel latentWidth latentHeight =
  let
    minDim = min latentWidth latentHeight
  in
    if minDim >= 64 then Fine
    else if minDim >= 32 then Medium
    else Coarse

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // region // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate all regions for a viewport at given grid level.
-- |
-- | Returns Array Region with deterministic RegionIds.
-- | Regions are assigned tiers based on distance from center:
-- | - Foveal: inner 25% of grid
-- | - Peripheral: middle 50% of grid
-- | - Background: outer 25% of grid
viewportToRegions :: ViewportState -> Array Region
viewportToRegions vs =
  let
    lw = viewportLatentWidth vs
    lh = viewportLatentHeight vs
    level = selectGridLevel lw lh
    size = gridLevelSize level
    
    -- Generate all coordinates
    coords = generateGridCoords level size
    
    -- Convert to regions with tier assignment
    regions = Array.mapMaybe (coordToRegion level size) coords
  in
    regions

-- | Generate all grid coordinates for a level.
generateGridCoords :: GridLevel -> Int -> Array { x :: Int, y :: Int }
generateGridCoords _level size =
  Array.concat $ map (\y -> map (\x -> { x, y }) (Array.range 0 (size - 1)))
                     (Array.range 0 (size - 1))

-- | Convert a coordinate to a Region with tier assignment.
coordToRegion :: GridLevel -> Int -> { x :: Int, y :: Int } -> Maybe Region
coordToRegion level size coord =
  case mkGridCoord level coord.x coord.y of
    Nothing -> Nothing
    Just gridCoord ->
      let
        tier = assignTier size coord.x coord.y
        regionId = mkRegionId level coord.x coord.y
      in
        Just (Region { id: regionId, coord: gridCoord, tier })

-- | Assign render tier based on distance from center.
-- |
-- | Uses Manhattan distance normalized by grid size:
-- | - Foveal: center 25% (distance < 0.25 * size)
-- | - Peripheral: middle ring (distance < 0.5 * size)
-- | - Background: outer ring
assignTier :: Int -> Int -> Int -> RenderTier
assignTier size x y =
  let
    -- Center of grid
    centerX = (size - 1) / 2
    centerY = (size - 1) / 2
    
    -- Manhattan distance from center (normalized)
    dx = if x > centerX then x - centerX else centerX - x
    dy = if y > centerY then y - centerY else centerY - y
    distNorm = (intToNum (dx + dy)) / (intToNum size)
  in
    if distNorm < 0.25 then Foveal
    else if distNorm < 0.5 then Peripheral
    else Background

-- | Create deterministic region ID from grid position.
-- |
-- | Format: "region-{level}-{x}-{y}"
-- | This is deterministic but not UUID5 (UUID5 would require crypto).
mkRegionId :: GridLevel -> Int -> Int -> RegionId
mkRegionId level x y =
  let
    levelStr = case level of
      Coarse -> "c"
      Medium -> "m"
      Fine -> "f"
  in
    RegionId (levelStr <> "-" <> show x <> "-" <> show y)

-- | Convert Int to Number.
intToNum :: Int -> Number
intToNum = Int.toNumber

-- | Convert viewport to a ground set for submodular optimization.
-- |
-- | Returns the regions as a Set for use with optimization algorithms.
viewportToGroundSet :: ViewportState -> Set.Set Region
viewportToGroundSet vs = Set.fromFoldable (viewportToRegions vs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                              // performance // to // feedback
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute quality metric from performance state.
-- |
-- | Quality = (budget - used) / budget, clamped to [0, 1].
-- | Higher quality means more headroom remaining.
qualityFromPerformance :: PerformanceState -> Number
qualityFromPerformance perf =
  let
    budget = gpuBudgetMs perf
    used = gpuUsedMs perf
    raw = if budget > 0.0 then (budget - used) / budget else 0.0
  in
    max 0.0 (min 1.0 raw)

-- | Convert performance metrics to utility feedback for a selection.
-- |
-- | This is the learning signal for online optimization:
-- | - High quality (lots of headroom) → can allocate more
-- | - Low quality (near budget) → should allocate less
performanceToFeedback :: PerformanceState -> RegionSelection -> Number
performanceToFeedback perf _sel =
  qualityFromPerformance perf

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // allocation // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State for allocation across frames.
-- |
-- | Tracks current epoch and cached region grid.
type AllocationState =
  { epoch :: EpochId
  , regions :: Array Region
  , gridLevel :: GridLevel
  }

-- | Create initial allocation state for a viewport.
mkAllocationState :: ViewportState -> AllocationState
mkAllocationState vs =
  let
    lw = viewportLatentWidth vs
    lh = viewportLatentHeight vs
    level = selectGridLevel lw lh
    regions = viewportToRegions vs
  in
    { epoch: EpochId 0
    , regions
    , gridLevel: level
    }

-- | Get current epoch.
allocationEpoch :: AllocationState -> EpochId
allocationEpoch state = state.epoch

-- | Get cached regions.
allocationRegions :: AllocationState -> Array Region
allocationRegions state = state.regions

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // frame // allocation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of allocating a frame.
type AllocationResult =
  { selections :: Array RegionSelection
  , nextState :: AllocationState
  }

-- | Allocate rendering resources for a frame.
-- |
-- | Adapts allocation based on performance feedback:
-- | - If quality headroom is high (>0.7): use tier defaults
-- | - If quality headroom is medium (0.3-0.7): reduce background quality
-- | - If quality headroom is low (<0.3): reduce peripheral and background
-- |
-- | Will be enhanced with full submodular optimization in P2.
allocateFrame :: ViewportState -> PerformanceState -> AllocationState -> AllocationResult
allocateFrame vs perf state =
  let
    -- Check if viewport changed (need to regenerate regions)
    currentLevel = selectGridLevel (viewportLatentWidth vs) (viewportLatentHeight vs)
    regionsChanged = currentLevel /= state.gridLevel
    
    -- Regenerate regions if viewport changed
    regions = if regionsChanged 
              then viewportToRegions vs 
              else state.regions
    
    -- Advance epoch
    newEpoch = nextEpoch state.epoch
    
    -- Compute quality headroom
    quality = qualityFromPerformance perf
    
    -- Adaptive allocation based on performance
    selections = map (adaptiveSelection quality) regions
    
    newState = 
      { epoch: newEpoch
      , regions
      , gridLevel: currentLevel
      }
  in
    { selections
    , nextState: newState
    }

-- | Adaptive selection: adjust diffusion steps based on quality headroom.
adaptiveSelection :: Number -> Region -> RegionSelection
adaptiveSelection quality region@(Region r) =
  let
    baseSteps = tierDefaultSteps r.tier
    adjustedSteps = adjustStepsForQuality quality r.tier baseSteps
  in
    RegionSelection { region, steps: adjustedSteps }

-- | Adjust diffusion steps based on quality headroom and tier.
-- |
-- | - Foveal: always gets full steps (highest priority)
-- | - Peripheral: reduced when quality < 0.5
-- | - Background: reduced when quality < 0.7
adjustStepsForQuality :: Number -> RenderTier -> DiffusionSteps -> DiffusionSteps
adjustStepsForQuality quality tier (DiffusionSteps steps) =
  let
    factor = case tier of
      Foveal -> 1.0  -- Never reduce foveal
      Peripheral -> if quality < 0.5 then 0.7 else 1.0
      Background -> if quality < 0.7 then 0.5 else if quality < 0.3 then 0.3 else 1.0
    
    adjusted = Int.floor (Int.toNumber steps * factor)
    clamped = max 1 (min 50 adjusted)
  in
    -- Use unsafe constructor since we've clamped to valid range
    DiffusionSteps clamped

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // quality // and // utility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Quality value from a raw number.
-- |
-- | Quality is bounded [0, 1]. Values outside this range are clamped.
mkQuality :: Number -> Quality
mkQuality n = Quality (clampToBounds 0.0 1.0 n)

-- | Create a Utility value from a raw number.
-- |
-- | Utility is bounded [0, 1e12]. Values outside this range are clamped.
mkUtility :: Number -> Utility
mkUtility n = Utility (clampToBounds 0.0 1.0e12 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // region // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the grid coordinate from a region.
regionCoord :: Region -> GridCoord
regionCoord (Region r) = r.coord

-- | Find all regions adjacent to a given region (4-connected).
-- |
-- | Returns regions sharing an edge (not diagonal).
-- | Useful for spatial smoothing or quality propagation.
adjacentRegions :: Region -> Array Region -> Array Region
adjacentRegions (Region target) allRegions =
  let
    (GridCoord tc) = target.coord
    targetLevel = tc.level
    targetX = tc.x
    targetY = tc.y
    
    -- Check if a region is adjacent (Manhattan distance = 1)
    isAdjacent :: Region -> Boolean
    isAdjacent (Region r) =
      let
        (GridCoord rc) = r.coord
        dx = if rc.x > targetX then rc.x - targetX else targetX - rc.x
        dy = if rc.y > targetY then rc.y - targetY else targetY - rc.y
      in
        rc.level == targetLevel && (dx + dy) == 1
  in
    Array.filter isAdjacent allRegions

-- | Filter regions by render tier.
-- |
-- | Returns all regions in the specified tier.
regionsInTier :: RenderTier -> Array Region -> Array Region
regionsInTier tier = Array.filter (\(Region r) -> r.tier == tier)

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // safe // step // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safely construct DiffusionSteps with validation.
-- |
-- | Returns Nothing if steps are outside [1, 50].
-- | Prefer this over raw constructor for external input.
safeSteps :: Int -> Maybe DiffusionSteps
safeSteps = mkDiffusionSteps

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // faa-enhanced allocation (p2)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Index type for mapping between Regions and submodular Elements.
-- |
-- | Regions are identified by position in the region array.
type RegionIndex = Int

-- | Configuration for FAA-enhanced allocation.
-- |
-- | ## Theoretical Foundation
-- |
-- | Uses FAA (Floquet Adiabatic Algorithm) for √T speedup over standard
-- | continuous greedy, then min-energy rounding for noise-resilient
-- | discretization.
-- |
-- | ## Parameters
-- |
-- | - `targetIterations`: Controls precision (actual iterations = √targetIterations)
-- | - `maxRegions`: Maximum regions to select (cardinality constraint k)
-- | - `roundingCandidates`: Number of rounding candidates for min-energy selection
-- | - `qualityWeight`: Weight for quality-based utility
-- | - `coverageWeight`: Weight for spatial coverage utility
-- |
-- | ## Proven Properties (FAA.lean, ContinuousGreedy.lean)
-- |
-- | - Achieves (1 - 1/e - O(1/√T)) approximation
-- | - In √T iterations instead of T
-- | - Min-energy rounding is deterministic and noise-resilient
newtype FAAAllocationConfig = FAAAllocationConfig
  { targetIterations :: Int      -- ^ T: precision target (actual = √T iterations)
  , maxRegions :: Int            -- ^ k: cardinality constraint
  , roundingCandidates :: Int    -- ^ Number of rounding candidates
  , qualityWeight :: Number      -- ^ Weight for quality utility
  , coverageWeight :: Number     -- ^ Weight for coverage utility
  , seed :: Number               -- ^ Random seed for reproducibility
  }

derive instance eqFAAAllocationConfig :: Eq FAAAllocationConfig

instance showFAAAllocationConfig :: Show FAAAllocationConfig where
  show (FAAAllocationConfig c) = 
    "FAAConfig{T=" <> show c.targetIterations <> 
    ",k=" <> show c.maxRegions <> "}"

-- | Create FAA allocation config with sensible defaults.
-- |
-- | ## Real-Time Defaults (60fps target)
-- |
-- | - targetIterations: 100 → √100 = 10 actual iterations
-- | - roundingCandidates: 20 → fast min-energy selection
-- | - qualityWeight: 0.7 → prioritize render quality
-- | - coverageWeight: 0.3 → secondary coverage objective
mkFAAAllocationConfig :: Int -> Int -> FAAAllocationConfig
mkFAAAllocationConfig maxRegions targetIterations = FAAAllocationConfig
  { targetIterations
  , maxRegions
  , roundingCandidates: 20
  , qualityWeight: 0.7
  , coverageWeight: 0.3
  , seed: 42.0
  }

-- | Convert regions to a ground set for submodular optimization.
-- |
-- | Each region becomes an Element indexed by position in the array.
-- | Returns (groundSet, indexToRegion) for mapping back after optimization.
regionsToGroundSetFAA :: Array Region -> { groundSet :: GroundSet RegionIndex, indexToRegion :: Array Region }
regionsToGroundSetFAA regions =
  let n = Array.length regions
      elements = map Element (Array.range 0 (n - 1))
      groundSet = GroundSet { size: Dim n, elements }
  in { groundSet, indexToRegion: regions }

-- | Create a submodular oracle for region allocation.
-- |
-- | ## Utility Function
-- |
-- | The utility of selecting a set of regions S is:
-- |
-- |   f(S) = qualityWeight · Σ_{r ∈ S} tierQuality(r)
-- |        + coverageWeight · coverage(S)
-- |
-- | Where:
-- | - tierQuality(r) = 1.0 for Foveal, 0.6 for Peripheral, 0.3 for Background
-- | - coverage(S) = √|S| (concave, encouraging spread)
-- |
-- | ## Submodularity
-- |
-- | The function is submodular because:
-- | - Linear sum is modular (trivially submodular)
-- | - √|S| is concave in |S| (submodular)
-- | - Non-negative sum of submodular functions is submodular
regionUtilityOracle 
  :: FAAAllocationConfig 
  -> Array Region 
  -> GroundSet RegionIndex 
  -> SubmodularOracle RegionIndex
regionUtilityOracle (FAAAllocationConfig config) regions groundSet =
  SubmodularOracle
    { eval: evalUtility
    , marginal: marginalUtility
    , groundSet
    , fMax: Nothing  -- Unknown upper bound
    }
  where
    -- | Evaluate utility of a region set.
    evalUtility :: ElementSet RegionIndex -> SetValue
    evalUtility selected =
      let selectedIndices = Set.toUnfoldable selected :: Array (Element RegionIndex)
          qualitySum = foldl (\acc (Element i) -> 
            acc + regionQuality (Array.index regions i)) 0.0 selectedIndices
          coverageVal = intToNumSafe (Set.size selected)
          -- Coverage utility: √|S| (concave, submodular)
          coverageUtility = Math.sqrt coverageVal
          totalUtility = config.qualityWeight * qualitySum 
                       + config.coverageWeight * coverageUtility
      in SetValue totalUtility
    
    -- | Marginal gain from adding a region.
    marginalUtility :: Element RegionIndex -> ElementSet RegionIndex -> MarginalGain
    marginalUtility e@(Element i) currentSet =
      if Set.member e currentSet
        then MarginalGain 0.0  -- Already included
        else
          let -- Quality gain (modular)
              qualityGain = regionQuality (Array.index regions i)
              -- Coverage gain: √(|S|+1) - √|S| (diminishing returns)
              currentSize = Set.size currentSet
              currentCoverage = Math.sqrt (intToNumSafe currentSize)
              newCoverage = Math.sqrt (intToNumSafe (currentSize + 1))
              coverageGain = newCoverage - currentCoverage
              totalGain = config.qualityWeight * qualityGain 
                        + config.coverageWeight * coverageGain
          in MarginalGain totalGain
    
    -- | Get quality value for a region based on tier.
    regionQuality :: Maybe Region -> Number
    regionQuality maybeRegion = case maybeRegion of
      Nothing -> 0.0  -- Invalid index
      Just (Region r) -> case r.tier of
        Foveal -> 1.0       -- Highest priority
        Peripheral -> 0.6   -- Medium priority
        Background -> 0.3   -- Lower priority

-- | Allocate frame using FAA-enhanced submodular optimization.
-- |
-- | ## Algorithm
-- |
-- | 1. Convert regions to ground set
-- | 2. Create utility oracle (quality + coverage)
-- | 3. Create cardinality matroid (k = maxRegions)
-- | 4. Run FAA-enhanced continuous greedy (√T iterations)
-- | 5. Round using min-energy selection (deterministic)
-- | 6. Convert selected elements back to RegionSelections
-- |
-- | ## Guarantees (Proven in proofs/Hydrogen/Optimize/Submodular/)
-- |
-- | - (1 - 1/e - O(1/√T)) approximation to optimal k-region selection
-- | - √T iterations instead of T (FAA speedup)
-- | - Deterministic rounding (min-energy)
allocateFrameFAA 
  :: ViewportState 
  -> PerformanceState 
  -> AllocationState 
  -> FAAAllocationConfig 
  -> AllocationResult
allocateFrameFAA vs perf state config@(FAAAllocationConfig c) =
  let 
    -- Check if viewport changed (need to regenerate regions)
    currentLevel = selectGridLevel (viewportLatentWidth vs) (viewportLatentHeight vs)
    regionsChanged = currentLevel /= state.gridLevel
    
    -- Regenerate regions if viewport changed
    regions = if regionsChanged 
              then viewportToRegions vs 
              else state.regions
    
    -- Advance epoch
    newEpoch = nextEpoch state.epoch
    
    -- Convert regions to ground set
    { groundSet, indexToRegion } = regionsToGroundSetFAA regions
    
    -- Create utility oracle
    oracle = regionUtilityOracle config indexToRegion groundSet
    
    -- Create cardinality matroid: select at most k regions
    matroid = CardinalityMatroid 
      { k: Dim (min c.maxRegions (Array.length regions))
      , groundSet
      }
    
    -- Create FAA config
    faaConfig = mkFAAConfig c.targetIterations
    
    -- Run FAA-enhanced continuous greedy
    fractionalSolution = continuousGreedyFAA matroid oracle faaConfig
    
    -- Round using min-energy selection
    minEnergyConfig = mkMinEnergyConfig c.roundingCandidates
    selectedElements = minEnergyRound fractionalSolution minEnergyConfig
    
    -- Convert selected elements back to regions
    selectedIndices = Set.toUnfoldable selectedElements :: Array (Element RegionIndex)
    selectedRegions = Array.mapMaybe (\(Element i) -> Array.index indexToRegion i) selectedIndices
    
    -- Create selections with quality-adjusted steps
    quality = qualityFromPerformance perf
    selections = map (adaptiveSelectionFAA quality fractionalSolution) 
                     (Array.mapWithIndex Tuple selectedRegions)
    
    newState = 
      { epoch: newEpoch
      , regions
      , gridLevel: currentLevel
      }
  in
    { selections
    , nextState: newState
    }

-- | Adaptive selection for FAA: use fractional value to modulate steps.
-- |
-- | Regions with higher fractional values in the continuous solution
-- | get more diffusion steps, as they were "more selected" by the optimizer.
-- |
-- | ## Fractional Value Modulation
-- |
-- | The continuous greedy produces fractional values x_e ∈ [0, 1] for each
-- | element. After rounding, we use these values to modulate quality:
-- | - x_e close to 1.0: strong selection → more diffusion steps
-- | - x_e close to 0.5: marginal selection → baseline diffusion steps
-- | - x_e close to 0.0: weak selection (shouldn't happen after rounding)
-- |
-- | The fractional value acts as a "confidence" weight from the optimizer.
adaptiveSelectionFAA 
  :: Number 
  -> FractionalSolution RegionIndex 
  -> Tuple Int Region 
  -> RegionSelection
adaptiveSelectionFAA quality fractionalSol (Tuple idx region@(Region r)) =
  let baseSteps = tierDefaultSteps r.tier
      -- Get fractional value for this element (confidence from optimizer)
      fractionalValue = solutionCoord fractionalSol (Element idx)
      -- Modulate quality by fractional confidence
      -- Higher fractional value = more confident → boost quality
      -- fractionalValue in [0, 1], typically > 0.5 for selected elements
      confidenceBoost = 0.5 + fractionalValue * 0.5  -- Maps [0,1] → [0.5, 1.0]
      modulatedQuality = min 1.0 (quality * confidenceBoost)
      -- Apply standard quality adjustment with boosted quality
      adjustedSteps = adjustStepsForQuality modulatedQuality r.tier baseSteps
  in RegionSelection { region, steps: adjustedSteps }

-- | Safe Int to Number conversion without FFI.
intToNumSafe :: Int -> Number
intToNumSafe i = foldl (\acc _ -> acc + 1.0) 0.0 (Array.range 1 i)

-- | Tuple type for indexed mapping.
data Tuple a b = Tuple a b

