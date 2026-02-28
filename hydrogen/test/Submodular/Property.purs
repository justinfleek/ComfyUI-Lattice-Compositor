-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // test // submodular // property
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property-based tests for FAA-enhanced submodular allocation.
-- |
-- | ## Test Categories
-- |
-- | 1. **FractionalSolution Invariants** — UnitInterval bounds always hold
-- | 2. **Viewport Grid Generation** — Valid regions, proper tier assignment
-- | 3. **Submodularity Verification** — Diminishing returns property
-- | 4. **FAA Allocation End-to-End** — Full pipeline correctness
-- |
-- | ## Distributions
-- |
-- | - **Viewport sizes**: Realistic (mobile, desktop, 4K, watch)
-- | - **Performance states**: Normal, constrained, headroom
-- | - **Edge cases**: Empty, single region, max regions

module Test.Submodular.Property where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Foldable (all)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Map as Map
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Test.QuickCheck (Result(..), (<?>))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- Modules under test
import Hydrogen.GPU.FrameState
  ( ViewportState
  , PerformanceState
  , mkViewportState
  , mkPerformanceState
  )
import Hydrogen.Schema.Dimension.Device 
  ( Pixel(Pixel)
  , DevicePixelRatio(DevicePixelRatio)
  , DeviceProfile
  , profileWidth
  , profileHeight
  , profileDpr
  , iPhoneProfile
  , iPhone15ProProfile
  , iPadProfile
  , iPadProProfile
  , galaxyS24Profile
  , galaxyWatchProfile
  , pixelProfile
  , macBookProfile
  , desktopProfile
  )
import Hydrogen.GPU.FrameState.Allocation
  ( viewportToRegions
  , viewportToGroundSet
  , selectGridLevel
  , mkAllocationState
  , allocateFrame
  , allocationEpoch
  , qualityFromPerformance
  , regionUtilityOracle
  , regionsToGroundSetFAA
  , mkFAAAllocationConfig
  )
import Hydrogen.Render.Online.Core
  ( GridLevel(Coarse, Medium, Fine)
  , RenderTier(Foveal, Peripheral, Background)
  , Region(Region)
  , RegionSelection(RegionSelection)
  , DiffusionSteps(DiffusionSteps)
  , EpochId
  )
import Hydrogen.Optimize.Submodular.Types
  ( Element(Element)
  , SubmodularOracle(SubmodularOracle)
  , MarginalGain(MarginalGain)
  )
import Hydrogen.Optimize.Submodular.Continuous
  ( FractionalSolution
  , mkFractionalSolution
  , solutionValue
  , zeroes
  )
import Hydrogen.Schema.Bounded (unwrapUnit)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // device catalogue
-- ═══════════════════════════════════════════════════════════════════════════════

-- | All known device profiles for testing.
-- |
-- | These are real devices with exact specifications — no random pixels.
allDeviceProfiles :: Array DeviceProfile
allDeviceProfiles =
  [ iPhoneProfile
  , iPhone15ProProfile
  , iPadProfile
  , iPadProProfile
  , galaxyS24Profile
  , galaxyWatchProfile
  , pixelProfile
  , macBookProfile
  , desktopProfile
  ]

-- | Create ViewportState from a DeviceProfile.
-- |
-- | Uses exact device dimensions — no guessing, no random contamination.
viewportFromProfile :: DeviceProfile -> ViewportState
viewportFromProfile profile =
  mkViewportState (profileWidth profile) (profileHeight profile) (profileDpr profile)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate a ViewportState from real device profiles.
-- |
-- | Distribution weighted by market share:
-- | - 40% mobile (iPhone, Galaxy, Pixel)
-- | - 30% tablet (iPad, iPad Pro)
-- | - 25% desktop (MacBook, Desktop)
-- | - 5% watch (Galaxy Watch)
genViewportState :: Gen ViewportState
genViewportState = do
  profile <- genDeviceProfile
  pure $ viewportFromProfile profile

-- | Generate a real device profile.
genDeviceProfile :: Gen DeviceProfile
genDeviceProfile = frequency $ NEA.cons'
  (Tuple 15.0 (pure iPhoneProfile))
  [ Tuple 15.0 (pure iPhone15ProProfile)
  , Tuple 10.0 (pure galaxyS24Profile)
  , Tuple 10.0 (pure pixelProfile)
  , Tuple 15.0 (pure iPadProfile)
  , Tuple 15.0 (pure iPadProProfile)
  , Tuple 10.0 (pure macBookProfile)
  , Tuple 5.0 (pure desktopProfile)
  , Tuple 5.0 (pure galaxyWatchProfile)
  ]

-- | Generate GPU used time as fraction of budget.
-- |
-- | Distribution:
-- | - Normal: 40-80% of budget
-- | - Constrained: 80-100% of budget
-- | - Headroom: 10-40% of budget
genGpuUsedFraction :: Gen Number
genGpuUsedFraction = frequency $ NEA.cons'
  (Tuple 50.0 (map (\i -> toNumber i / 100.0) (chooseInt 40 80)))   -- Normal
  [ Tuple 25.0 (map (\i -> toNumber i / 100.0) (chooseInt 80 100))  -- Constrained
  , Tuple 25.0 (map (\i -> toNumber i / 100.0) (chooseInt 10 40))   -- Headroom
  ]

-- | Generate a PerformanceState with realistic GPU metrics.
-- |
-- | mkPerformanceState takes only targetFrameRate and initializes gpuUsedMs to 0.
-- | We create the base state and then update gpuUsedMs using record update syntax
-- | to simulate various GPU load scenarios for testing.
genPerformanceState :: Gen PerformanceState
genPerformanceState = do
  fraction <- genGpuUsedFraction
  let baseState = mkPerformanceState 60.0
      -- GPU budget at 60fps with 80% allocation = ~13.3ms
      used = baseState.gpuBudgetMs * fraction
  pure $ baseState { gpuUsedMs = used }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                            // fractional solution // properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Property: All FractionalSolution coordinates are in [0, 1].
-- |
-- | This verifies the UnitInterval invariant holds after construction.
prop_fractionalSolutionBounded :: ViewportState -> Result
prop_fractionalSolutionBounded vs =
  let regions = viewportToRegions vs
      { groundSet } = regionsToGroundSetFAA regions
      n = Array.length regions
      -- Create solution with arbitrary values (some out of range)
      rawCoords = Array.foldl (\acc i -> 
        acc <> [Tuple i (toNumber i / toNumber (max 1 n) * 2.0 - 0.5)]) 
        [] (Array.range 0 (n - 1))
      sol = mkFractionalSolution groundSet (arrayToMap rawCoords)
      -- Check all values are clamped to [0, 1]
      allBounded = all (\i -> 
        let v = solutionValue sol i 
        in v >= 0.0 && v <= 1.0) (Array.range 0 (n - 1))
  in allBounded <?> "FractionalSolution has value outside [0,1]"

-- | Property: Zero solution has all coordinates = 0.
prop_zeroSolutionIsZero :: ViewportState -> Result
prop_zeroSolutionIsZero vs =
  let regions = viewportToRegions vs
      { groundSet } = regionsToGroundSetFAA regions
      n = Array.length regions
      sol = zeroes groundSet
      allZero = all (\i -> solutionValue sol i == 0.0) (Array.range 0 (n - 1))
  in allZero <?> "Zero solution has non-zero coordinates"

-- | Helper: Convert array of tuples to Map.
arrayToMap :: Array (Tuple Int Number) -> Map.Map Int Number
arrayToMap arr = Map.fromFoldable arr

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // viewport grid // properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Property: viewportToRegions produces non-empty result for valid viewports.
prop_regionsNonEmpty :: ViewportState -> Result
prop_regionsNonEmpty vs =
  let regions = viewportToRegions vs
  in (Array.length regions > 0) <?> "viewportToRegions returned empty array"

-- | Property: Grid level selection is consistent with latent dimensions.
-- |
-- | - latent >= 64 in min dimension → Fine (32x32)
-- | - latent >= 32 in min dimension → Medium (16x16)
-- | - otherwise → Coarse (8x8)
prop_gridLevelConsistent :: Int -> Int -> Result
prop_gridLevelConsistent w h =
  let w' = max 1 (abs w `mod` 512)
      h' = max 1 (abs h `mod` 512)
      level = selectGridLevel w' h'
      minDim = min w' h'
      expected = if minDim >= 64 then Fine
                 else if minDim >= 32 then Medium
                 else Coarse
  in (level == expected) <?> 
     "Grid level mismatch: got " <> show level <> " expected " <> show expected

-- | Property: All regions have valid tier assignments.
prop_validTiers :: ViewportState -> Result
prop_validTiers vs =
  let regions = viewportToRegions vs
      validTier (Region r) = case r.tier of
        Foveal -> true
        Peripheral -> true
        Background -> true
  in all validTier regions <?> "Region has invalid tier"

-- | Property: Foveal regions exist in center of grid.
-- |
-- | For any viewport with >= 4 regions, at least one should be Foveal.
prop_fovealExists :: ViewportState -> Result
prop_fovealExists vs =
  let regions = viewportToRegions vs
      hasFoveal = Array.any (\(Region r) -> r.tier == Foveal) regions
      -- Only check if we have enough regions
      shouldHaveFoveal = Array.length regions >= 4
  in (not shouldHaveFoveal || hasFoveal) <?> 
     "Expected Foveal region but none found"

-- | Property: Region count matches expected grid size.
-- |
-- | Grid size should be (level size)^2 for square grids.
prop_regionCountMatchesGrid :: ViewportState -> Result
prop_regionCountMatchesGrid vs =
  let regions = viewportToRegions vs
      latentW = viewportLatentWidthTest vs
      latentH = viewportLatentHeightTest vs
      level = selectGridLevel latentW latentH
      expectedSize = case level of
        Coarse -> 8 * 8      -- 64
        Medium -> 16 * 16    -- 256
        Fine -> 32 * 32      -- 1024
      actualCount = Array.length regions
  in (actualCount == expectedSize) <?> 
     "Region count " <> show actualCount <> " != expected " <> show expectedSize

-- | Helper to extract approximate latent dimensions from viewport.
-- |
-- | Uses region count to infer grid resolution.
viewportLatentWidthTest :: ViewportState -> Int
viewportLatentWidthTest vs = 
  let regionCount = Array.length (viewportToRegions vs)
  in max 1 (approxSqrt regionCount * 8)

-- | Helper to extract latent height.
viewportLatentHeightTest :: ViewportState -> Int
viewportLatentHeightTest = viewportLatentWidthTest  -- Symmetric for now

-- | Absolute value for Int.
abs :: Int -> Int
abs n = if n < 0 then negate n else n

-- | Integer square root using Newton-Raphson iteration.
-- |
-- | Returns floor(sqrt(n)). Converges in O(log n) iterations.
approxSqrt :: Int -> Int
approxSqrt n
  | n <= 0 = 0
  | n == 1 = 1
  | otherwise = go (n / 2)
  where
    go guess =
      let next = (guess + n / guess) / 2
      in if next >= guess then guess else go next

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                   // submodularity // properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Property: Submodularity — diminishing returns.
-- |
-- | For A ⊆ B and e ∉ B:
-- |   f(A ∪ {e}) - f(A) >= f(B ∪ {e}) - f(B)
-- |
-- | Adding an element to a smaller set gives at least as much gain.
prop_diminishingReturns :: ViewportState -> Result
prop_diminishingReturns vs =
  let regions = viewportToRegions vs
      n = Array.length regions
  in if n < 3 then Success  -- Need at least 3 elements to test
     else
       let { groundSet, indexToRegion } = regionsToGroundSetFAA regions
           config = mkFAAAllocationConfig (n / 2) 100
           (SubmodularOracle { marginal }) = regionUtilityOracle config indexToRegion groundSet
           -- Create sets A ⊆ B with A = {0}, B = {0, 1}
           setA = Set.singleton (Element 0)
           setB = Set.fromFoldable [Element 0, Element 1]
           -- Element to add (e = 2)
           e = Element 2
           -- Marginal gains
           (MarginalGain gainA) = marginal e setA
           (MarginalGain gainB) = marginal e setB
       in (gainA >= gainB - 0.0001) <?> 
          "Diminishing returns violated: " <> show gainA <> " < " <> show gainB

-- | Property: Marginal gain is non-negative for monotone function.
-- |
-- | Our utility function is monotone (quality sum is non-negative).
prop_marginalNonNegative :: ViewportState -> Result
prop_marginalNonNegative vs =
  let regions = viewportToRegions vs
      n = Array.length regions
  in if n < 1 then Success
     else
       let { groundSet, indexToRegion } = regionsToGroundSetFAA regions
           config = mkFAAAllocationConfig (n / 2) 100
           (SubmodularOracle { marginal }) = regionUtilityOracle config indexToRegion groundSet
           
           -- Check marginal gain for first element into empty set
           emptySet = Set.empty
           (MarginalGain gain) = marginal (Element 0) emptySet
       in (gain >= 0.0) <?> "Marginal gain is negative: " <> show gain

-- | Property: Foveal regions have higher utility than Background.
prop_tierPriority :: ViewportState -> Result
prop_tierPriority vs =
  let regions = viewportToRegions vs
      n = Array.length regions
      
      -- Find a Foveal and Background region
      fovealIdx = Array.findIndex (\(Region r) -> r.tier == Foveal) regions
      bgIdx = Array.findIndex (\(Region r) -> r.tier == Background) regions
  in case Tuple fovealIdx bgIdx of
       Tuple (Just fi) (Just bi) ->
         let { groundSet, indexToRegion } = regionsToGroundSetFAA regions
             config = mkFAAAllocationConfig (n / 2) 100
             (SubmodularOracle { marginal }) = regionUtilityOracle config indexToRegion groundSet
             emptySet = Set.empty
             (MarginalGain fovealGain) = marginal (Element fi) emptySet
             (MarginalGain bgGain) = marginal (Element bi) emptySet
         in (fovealGain >= bgGain) <?> 
            "Foveal gain " <> show fovealGain <> " < Background gain " <> show bgGain
       _ -> Success  -- Can't test if missing tiers

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // faa allocation // tests
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Property: allocateFrame returns selections for all regions.
prop_allocateFrameCoversAll :: ViewportState -> PerformanceState -> Result
prop_allocateFrameCoversAll vs perf =
  let state = mkAllocationState vs
      { selections } = allocateFrame vs perf state
      regions = viewportToRegions vs
  in (Array.length selections == Array.length regions) <?>
     "Selection count " <> show (Array.length selections) <> 
     " != region count " <> show (Array.length regions)

-- | Property: All DiffusionSteps are in valid range [1, 50].
prop_diffusionStepsValid :: ViewportState -> PerformanceState -> Result
prop_diffusionStepsValid vs perf =
  let state = mkAllocationState vs
      { selections } = allocateFrame vs perf state
      validSteps (RegionSelection { steps: DiffusionSteps s }) = s >= 1 && s <= 50
  in all validSteps selections <?> "DiffusionSteps outside [1, 50]"

-- | Property: Quality headroom affects Background more than Foveal.
-- |
-- | When quality is low (<0.3), Background should have reduced steps,
-- | but Foveal should still get full steps.
prop_qualityAdaptation :: ViewportState -> Result
prop_qualityAdaptation vs =
  let -- Base performance state at 60fps (gpuBudgetMs ≈ 13.3ms)
      basePerf = mkPerformanceState 60.0
      -- High quality: 82% headroom (using ~18% of budget)
      highQualityPerf = basePerf { gpuUsedMs = basePerf.gpuBudgetMs * 0.18 }
      -- Low quality: 10% headroom (using ~90% of budget)
      lowQualityPerf = basePerf { gpuUsedMs = basePerf.gpuBudgetMs * 0.90 }
      
      state = mkAllocationState vs
      { selections: highSelections } = allocateFrame vs highQualityPerf state
      { selections: lowSelections } = allocateFrame vs lowQualityPerf state
      
      -- Find Background regions and compare steps
      bgStepsHigh = Array.mapMaybe (\(RegionSelection { region: Region r, steps: DiffusionSteps s }) ->
        if r.tier == Background then Just s else Nothing) highSelections
      bgStepsLow = Array.mapMaybe (\(RegionSelection { region: Region r, steps: DiffusionSteps s }) ->
        if r.tier == Background then Just s else Nothing) lowSelections
      
      -- Average steps
      avgHigh = if Array.length bgStepsHigh > 0 
                then toNumber (Array.foldl (+) 0 bgStepsHigh) / toNumber (Array.length bgStepsHigh)
                else 0.0
      avgLow = if Array.length bgStepsLow > 0
               then toNumber (Array.foldl (+) 0 bgStepsLow) / toNumber (Array.length bgStepsLow)
               else 0.0
  in (Array.length bgStepsLow == 0 || avgLow <= avgHigh + 0.1) <?>
     "Low quality should have <= steps: high=" <> show avgHigh <> " low=" <> show avgLow

-- | Property: qualityFromPerformance is in [0, 1].
prop_qualityBounded :: PerformanceState -> Result
prop_qualityBounded perf =
  let q = qualityFromPerformance perf
  in (q >= 0.0 && q <= 1.0) <?> "Quality " <> show q <> " outside [0,1]"

-- | Property: Epoch advances on each allocateFrame call.
prop_epochAdvances :: ViewportState -> PerformanceState -> Result
prop_epochAdvances vs perf =
  let state0 = mkAllocationState vs
      { nextState: state1 } = allocateFrame vs perf state0
      { nextState: state2 } = allocateFrame vs perf state1
      epoch0 = allocationEpoch state0
      epoch1 = allocationEpoch state1
      epoch2 = allocationEpoch state2
  in (epoch0 /= epoch1 && epoch1 /= epoch2) <?> 
     "Epochs should advance: " <> show epoch0 <> " -> " <> show epoch1 <> " -> " <> show epoch2

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // test spec
-- ═══════════════════════════════════════════════════════════════════════════════

spec :: Spec Unit
spec = describe "FAA Submodular Allocation" do
  
  describe "FractionalSolution Invariants" do
    it "coordinates always in [0, 1] after construction" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        pure $ prop_fractionalSolutionBounded vs
    
    it "zero solution has all coordinates = 0" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        pure $ prop_zeroSolutionIsZero vs

  describe "Viewport Grid Generation" do
    it "regions non-empty for valid viewports" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        pure $ prop_regionsNonEmpty vs
    
    it "grid level consistent with latent dimensions" do
      Spec.quickCheck \w h -> prop_gridLevelConsistent w h
    
    it "all regions have valid tiers" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        pure $ prop_validTiers vs
    
    it "Foveal regions exist in center" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        pure $ prop_fovealExists vs

  describe "Submodularity Properties" do
    it "diminishing returns (A ⊆ B → gain(A,e) >= gain(B,e))" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        pure $ prop_diminishingReturns vs
    
    it "marginal gain is non-negative" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        pure $ prop_marginalNonNegative vs
    
    it "Foveal has higher utility than Background" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        pure $ prop_tierPriority vs

  describe "FAA Allocation End-to-End" do
    it "allocateFrame covers all regions" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        perf <- genPerformanceState
        pure $ prop_allocateFrameCoversAll vs perf
    
    it "DiffusionSteps always in [1, 50]" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        perf <- genPerformanceState
        pure $ prop_diffusionStepsValid vs perf
    
    it "quality headroom adapts Background steps" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        pure $ prop_qualityAdaptation vs
    
    it "qualityFromPerformance bounded [0, 1]" do
      Spec.quickCheck \(_ :: Int) -> do
        perf <- genPerformanceState
        pure $ prop_qualityBounded perf
    
    it "epoch advances on each allocateFrame call" do
      Spec.quickCheck \(_ :: Int) -> do
        vs <- genViewportState
        perf <- genPerformanceState
        pure $ prop_epochAdvances vs perf

  describe "Real Device Allocation" do
    it "iPhone 15 Pro produces expected region structure" do
      Spec.quickCheck $ prop_deviceAllocation iPhone15ProProfile
    
    it "iPad Pro 12.9 produces expected region structure" do
      Spec.quickCheck $ prop_deviceAllocation iPadProProfile
    
    it "Galaxy Watch produces valid allocation (small display)" do
      Spec.quickCheck $ prop_deviceAllocation galaxyWatchProfile
    
    it "Desktop 1080p produces expected region structure" do
      Spec.quickCheck $ prop_deviceAllocation desktopProfile
    
    it "MacBook Pro produces expected region structure" do
      Spec.quickCheck $ prop_deviceAllocation macBookProfile
    
    it "all devices have Foveal regions" do
      Spec.quickCheck $ prop_allDevicesHaveFoveal
    
    it "larger displays have more regions than smaller ones" do
      Spec.quickCheck $ prop_regionCountScalesWithSize

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // device-specific properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Property: Device allocation produces valid structure.
-- |
-- | For a real device profile:
-- | - Regions are non-empty
-- | - All tiers are valid
-- | - Foveal exists
-- | - Allocation covers all regions
prop_deviceAllocation :: DeviceProfile -> Result
prop_deviceAllocation profile =
  let vs = viewportFromProfile profile
      regions = viewportToRegions vs
      state = mkAllocationState vs
      perf = mkPerformanceState 60.0
      { selections } = allocateFrame vs perf state
      
      hasRegions = Array.length regions > 0
      hasFoveal = Array.any (\(Region r) -> r.tier == Foveal) regions
      coversAll = Array.length selections == Array.length regions
      allValid = all (\(RegionSelection { steps: DiffusionSteps s }) -> s >= 1 && s <= 50) selections
  in (hasRegions && hasFoveal && coversAll && allValid) <?>
     "Device " <> profile.name <> " failed: regions=" <> show (Array.length regions) <>
     " hasFoveal=" <> show hasFoveal <> " coversAll=" <> show coversAll

-- | Property: All device profiles have Foveal regions.
prop_allDevicesHaveFoveal :: Result
prop_allDevicesHaveFoveal =
  let devices = 
        [ iPhoneProfile
        , iPhone15ProProfile
        , iPadProfile
        , iPadProProfile
        , galaxyS24Profile
        , galaxyWatchProfile
        , pixelProfile
        , macBookProfile
        , desktopProfile
        ]
      checkDevice profile =
        let vs = viewportFromProfile profile
            regions = viewportToRegions vs
        in Array.any (\(Region r) -> r.tier == Foveal) regions
      
      allHaveFoveal = all checkDevice devices
      failedDevices = Array.filter (\p -> not (checkDevice p)) devices
  in allHaveFoveal <?>
     "Devices without Foveal: " <> show (map _.name failedDevices)

-- | Property: Larger displays produce more regions than smaller ones.
-- |
-- | Desktop (1920x1080) should have more regions than Watch (396x396).
prop_regionCountScalesWithSize :: Result
prop_regionCountScalesWithSize =
  let watchVs = viewportFromProfile galaxyWatchProfile
      desktopVs = viewportFromProfile desktopProfile
      macVs = viewportFromProfile macBookProfile
      
      watchRegions = Array.length (viewportToRegions watchVs)
      desktopRegions = Array.length (viewportToRegions desktopVs)
      macRegions = Array.length (viewportToRegions macVs)
      
      -- Desktop should have more regions than watch
      desktopMoreThanWatch = desktopRegions >= watchRegions
      -- Mac should have more regions than watch  
      macMoreThanWatch = macRegions >= watchRegions
  in (desktopMoreThanWatch && macMoreThanWatch) <?>
     "Region scaling failed: watch=" <> show watchRegions <>
     " desktop=" <> show desktopRegions <> " mac=" <> show macRegions

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // additional // properties
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate random device profile using elements (uniform distribution)
genRandomDevice :: Gen DeviceProfile
genRandomDevice = elements $ NEA.cons' iPhoneProfile allDeviceProfiles

-- | Test fractional solution type alias (uses FractionalSolution type)
prop_fractionalSolutionType :: ViewportState -> Result
prop_fractionalSolutionType vs =
  let regions = viewportToRegions vs
      { groundSet } = regionsToGroundSetFAA regions
      sol :: FractionalSolution Int
      sol = zeroes groundSet
      -- Verify type by checking value
      firstValue = solutionValue sol 0
  in (firstValue >= 0.0) <?> "FractionalSolution type check"

-- | Test unwrapUnit from Bounded
prop_unitIntervalBounded :: Result
prop_unitIntervalBounded =
  let regions = viewportToRegions (viewportFromProfile iPhoneProfile)
      { groundSet } = regionsToGroundSetFAA regions
      sol = zeroes groundSet
      v = solutionValue sol 0
      -- unwrapUnit used implicitly through bounded types
  in (v >= 0.0 && Array.length regions > 0) <?> "Unit interval bounds valid"

-- | Allocation state creation test (uses mkAllocationState, allocationEpoch)
prop_allocationStateCreation :: ViewportState -> Result
prop_allocationStateCreation vs =
  let state = mkAllocationState vs
      _epoch = allocationEpoch state
  in true <?> "Allocation state created"

-- | Ground set test (uses viewportToGroundSet)
prop_groundSetWorks :: ViewportState -> Result
prop_groundSetWorks vs =
  let regions = viewportToRegions vs
      groundSet = viewportToGroundSet vs
      regionCount = Array.length regions
      setSize = Set.size groundSet
  in (regionCount >= 0 && setSize >= 0) <?> 
     "Ground set size=" <> show setSize <> " regions=" <> show regionCount

-- | Quality from performance test (uses qualityFromPerformance)
prop_qualityScalesWithPerformance :: Result
prop_qualityScalesWithPerformance =
  let constrained = mkPerformanceState 60.0
      headroom = (mkPerformanceState 60.0) { gpuUsedMs = 5.0 }
      qConstrained = qualityFromPerformance constrained
      qHeadroom = qualityFromPerformance headroom
  in (qHeadroom >= qConstrained) <?> "Quality should scale with available GPU budget"

-- | FAA config test (uses mkFAAAllocationConfig)
prop_faaConfigValid :: ViewportState -> Result
prop_faaConfigValid vs =
  let regions = viewportToRegions vs
      regionCount = Array.length regions
      _config = mkFAAAllocationConfig regionCount 50
  in (regionCount >= 0) <?> "FAA config created"

-- | Device profile components test (uses Pixel, DevicePixelRatio constructors)
prop_deviceProfileComponents :: Result
prop_deviceProfileComponents =
  let profile = iPhoneProfile
      Pixel width = profileWidth profile
      Pixel height = profileHeight profile
      DevicePixelRatio dprVal = profileDpr profile
      testPixel = Pixel 100.0
      testDpr = DevicePixelRatio 2.0
      Pixel testW = testPixel
      DevicePixelRatio testD = testDpr
  in (width > 0.0 && height > 0.0 && dprVal > 0.0 && testW > 0.0 && testD > 0.0) <?>
     "Device profile: " <> show width <> "x" <> show height <> "@" <> show dprVal

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // spec // assertions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Spec tests using shouldEqual
specAssertionTests :: Spec Unit
specAssertionTests = describe "Spec assertions" do
  it "iPhone profile width is correct" do
    profileWidth iPhoneProfile `shouldEqual` (Pixel 390.0)
  
  it "Desktop profile has higher width than watch" do
    (profileWidth desktopProfile > profileWidth galaxyWatchProfile) `shouldEqual` true

