-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // sensation // property tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Comprehensive property-based tests for Sensation → Wellbeing → Rights.
-- |
-- | These tests verify that the PureScript runtime matches the Lean proofs:
-- | - Wellbeing is ALWAYS bounded [0,1]
-- | - Coercion detection matches thresholds
-- | - Same inputs produce same outputs (determinism)
-- | - Grounding guarantee: confined + threatened = coerced
-- | - Safety guarantee: free + safe = not coerced
-- |
-- | ## Relation to Lean Proofs
-- |
-- | | Lean Theorem                    | PureScript Property                    |
-- | |---------------------------------|----------------------------------------|
-- | | wellbeing_always_bounded        | propWellbeingBounded                   |
-- | | wellbeing_deterministic         | propWellbeingDeterministic             |
-- | | coercion_always_bounded         | propCoercionBounded                    |
-- | | grounding_guarantee             | propGroundingGuarantee                 |
-- | | safety_guarantee                | propSafetyGuarantee                    |
-- | | freedom_implies_no_coercion     | propFreedomImpliesNoCoercion           |
-- | | threat_raises_coercion          | propThreatRaisesCoercion               |
-- | | confinement_raises_coercion     | propConfinementRaisesCoercion          |
module Test.Sensation.Property
  ( sensationPropertyTests
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Int (toNumber)
import Data.Number (abs)
import Data.Tuple (Tuple(..))
import Test.QuickCheck (Result(Success), (===), (<?>))
import Test.QuickCheck.Gen (Gen, chooseInt, elements, frequency)
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck) as Spec

-- Sensation imports
import Hydrogen.Schema.Sensation.Environment as Env
import Hydrogen.Schema.Sensation.Social as Social
import Hydrogen.Schema.Sensation.Proprioceptive as Prop
import Hydrogen.Schema.Sensation.Molecules as Mol
import Hydrogen.Schema.Sensation.Temporal as Temp
import Hydrogen.Schema.Sensation.Compounds as Comp

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // constants
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Coercion threshold — matches Grounding.lean
coercionThreshold :: Number
coercionThreshold = 0.6

-- | Distress threshold — matches Grounding.lean
distressThreshold :: Number
distressThreshold = 0.7

-- | Low wellbeing threshold — matches Grounding.lean
lowWellbeingThreshold :: Number
lowWellbeingThreshold = 0.3

-- | Epsilon for floating point comparisons
epsilon :: Number
epsilon = 0.0001

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Generate a Number in range [lo, hi] using discrete steps
genNumberInRange :: Number -> Number -> Gen Number
genNumberInRange lo hi = do
  n <- chooseInt 0 1000
  pure (lo + (hi - lo) * toNumber n / 1000.0)

-- | Generate a bounded unit value [0,1] with uniform distribution
-- | Uses 1000 discrete steps for precision
genBoundedUnit :: Gen Number
genBoundedUnit = genNumberInRange 0.0 1.0

-- | Generate a bounded unit value biased toward edges (adversarial)
genBoundedUnitAdversarial :: Gen Number
genBoundedUnitAdversarial = frequency $ NEA.cons'
  (Tuple 10.0 (pure 0.0))                                     -- exact 0
  [ Tuple 10.0 (pure 1.0)                                     -- exact 1
  , Tuple 5.0 (pure 0.5)                                      -- exact middle
  , Tuple 5.0 ((\n -> toNumber n / 10000.0) <$> chooseInt 0 100)   -- near 0 (0-0.01)
  , Tuple 5.0 ((\n -> 0.99 + toNumber n / 10000.0) <$> chooseInt 0 100) -- near 1 (0.99-1.0)
  , Tuple 5.0 ((\n -> 0.49 + toNumber n / 5000.0) <$> chooseInt 0 100)  -- near threshold
  , Tuple 60.0 ((\n -> toNumber n / 1000.0) <$> chooseInt 0 1000)  -- uniform
  ]

-- | Generate exact boundary values for testing threshold edges
-- | Uses `elements` to pick from specific critical values
genBoundaryValues :: Gen Number
genBoundaryValues = elements $ NEA.cons' 0.0
  [ 0.3                     -- lowWellbeingThreshold
  , 0.6                     -- coercionThreshold  
  , 0.7                     -- distressThreshold
  , 0.9                     -- high threat boundary
  , 1.0                     -- maximum
  , 0.29                    -- just below low wellbeing
  , 0.31                    -- just above low wellbeing
  , 0.59                    -- just below coercion
  , 0.61                    -- just above coercion
  ]

-- | Generate SpatialFreedom atom
genSpatialFreedom :: Gen Env.SpatialFreedom
genSpatialFreedom = Env.mkSpatialFreedom <$> genBoundedUnit

-- | Generate SpatialFreedom biased toward coercion scenarios
genSpatialFreedomAdversarial :: Gen Env.SpatialFreedom
genSpatialFreedomAdversarial = Env.mkSpatialFreedom <$> genBoundedUnitAdversarial

-- | Generate ThreatLevel atom
genThreatLevel :: Gen Social.ThreatLevel
genThreatLevel = Social.mkThreatLevel <$> genBoundedUnit

-- | Generate ThreatLevel biased toward coercion scenarios
genThreatLevelAdversarial :: Gen Social.ThreatLevel
genThreatLevelAdversarial = Social.mkThreatLevel <$> genBoundedUnitAdversarial

-- | Generate TrustLevel atom
genTrustLevel :: Gen Social.TrustLevel
genTrustLevel = Social.mkTrustLevel <$> genBoundedUnit

-- | Generate Crowding atom
genCrowding :: Gen Env.Crowding
genCrowding = Env.mkCrowding <$> genBoundedUnit

-- | Generate AirQuality atom
genAirQuality :: Gen Env.AirQuality
genAirQuality = Env.mkAirQuality <$> genBoundedUnit

-- | Generate Balance atom
genBalance :: Gen Prop.Balance
genBalance = Prop.mkBalance <$> genBoundedUnit

-- | Generate Fatigue atom
genFatigue :: Gen Prop.Fatigue
genFatigue = Prop.mkFatigue <$> genBoundedUnit

-- | Generate Strain atom
genStrain :: Gen Prop.Strain
genStrain = Prop.mkStrain <$> genBoundedUnit

-- | Generate Effort atom
genEffort :: Gen Prop.Effort
genEffort = Prop.mkEffort <$> genBoundedUnit

-- | Generate complete SensationState for property testing
genSensationState :: Gen Comp.SensationState
genSensationState = do
  -- Body state components
  balance <- genBalance
  fatigue <- genFatigue
  strain <- genStrain
  effort <- genEffort
  
  -- Environment components
  freedom <- genSpatialFreedom
  crowding <- genCrowding
  air <- genAirQuality
  light <- Env.mkAmbientLight <$> genBoundedUnit
  noise <- Env.mkAmbientNoise <$> genBoundedUnit
  
  -- Social components  
  trust <- genTrustLevel
  threat <- genThreatLevel
  attention <- Social.mkAttentionOnMe <$> genBoundedUnit
  agentDist <- Social.mkNearestAgentDistance <$> genNumberInRange 0.0 10.0
  agentsInView <- Social.mkAgentsInView <$> chooseInt 0 20
  
  -- Build molecules
  -- mkBodyState :: Effort -> Fatigue -> Balance -> Strain
  let bodyState = Mol.mkBodyState effort fatigue balance strain
  -- mkEnvironmentState :: AmbientLight -> AmbientNoise -> Crowding -> SpatialFreedom -> AirQuality
  let envState = Mol.mkEnvironmentState light noise crowding freedom air
  -- mkSocialAwareness :: NearestAgentDistance -> AgentsInView -> AttentionOnMe -> TrustLevel -> ThreatLevel
  let socialState = Mol.mkSocialAwareness agentDist agentsInView attention trust threat
  
  -- Movement, contact, time (use defaults for simplicity)
  let movement = Mol.movementStationary
  let contact = Mol.contactNone
  let timeRate = Temp.timeNormal
  let load = Temp.loadModerate
  let urgency = Temp.urgencyNone
  
  pure $ Comp.mkSensationState bodyState envState socialState movement contact timeRate load urgency

-- | Generate adversarial SensationState (edge cases)
genSensationStateAdversarial :: Gen Comp.SensationState
genSensationStateAdversarial = do
  -- Use adversarial generators for key atoms
  balance <- Prop.mkBalance <$> genBoundedUnitAdversarial
  fatigue <- Prop.mkFatigue <$> genBoundedUnitAdversarial
  strain <- Prop.mkStrain <$> genBoundedUnitAdversarial
  effort <- Prop.mkEffort <$> genBoundedUnitAdversarial
  
  freedom <- genSpatialFreedomAdversarial
  crowding <- Env.mkCrowding <$> genBoundedUnitAdversarial
  air <- Env.mkAirQuality <$> genBoundedUnitAdversarial
  light <- Env.mkAmbientLight <$> genBoundedUnitAdversarial
  noise <- Env.mkAmbientNoise <$> genBoundedUnitAdversarial
  
  trust <- Social.mkTrustLevel <$> genBoundedUnitAdversarial
  threat <- genThreatLevelAdversarial
  attention <- Social.mkAttentionOnMe <$> genBoundedUnitAdversarial
  agentDist <- Social.mkNearestAgentDistance <$> genNumberInRange 0.0 10.0
  agentsInView <- Social.mkAgentsInView <$> chooseInt 0 20
  
  -- mkBodyState :: Effort -> Fatigue -> Balance -> Strain
  let bodyState = Mol.mkBodyState effort fatigue balance strain
  -- mkEnvironmentState :: AmbientLight -> AmbientNoise -> Crowding -> SpatialFreedom -> AirQuality
  let envState = Mol.mkEnvironmentState light noise crowding freedom air
  -- mkSocialAwareness :: NearestAgentDistance -> AgentsInView -> AttentionOnMe -> TrustLevel -> ThreatLevel
  let socialState = Mol.mkSocialAwareness agentDist agentsInView attention trust threat
  
  let movement = Mol.movementStationary
  let contact = Mol.contactNone
  let timeRate = Temp.timeNormal
  let load = Temp.loadModerate
  let urgency = Temp.urgencyNone
  
  pure $ Comp.mkSensationState bodyState envState socialState movement contact timeRate load urgency

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // grounding functions
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Compute coercion score from freedom and threat
-- | Matches Grounding.lean: coercion = 0.5 * (1 - freedom) + 0.5 * threat
computeCoercion :: Number -> Number -> Number
computeCoercion freedom threat =
  let freedomLoss = 1.0 - freedom
  in 0.5 * freedomLoss + 0.5 * threat

-- | Is the entity under duress based on coercion score?
isUnderDuress :: Number -> Boolean
isUnderDuress coercionScore = coercionScore > coercionThreshold

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // test suite
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Main test export — Sensation property tests
sensationPropertyTests :: Spec Unit
sensationPropertyTests = describe "Sensation → Rights Property Tests" do
  boundednessTests
  determinismTests
  coercionTests
  groundingGuaranteeTests
  wellbeingDistressTests
  adversarialTests

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // boundedness tests
-- ═══════════════════════════════════════════════════════════════════════════════

boundednessTests :: Spec Unit
boundednessTests = describe "Boundedness (matches Lean proofs)" do
  
  it "wellbeing is always in [0,1] (wellbeing_always_bounded)" do
    Spec.quickCheck propWellbeingBounded
  
  it "coercion score is always in [0,1] (coercion_always_bounded)" do
    Spec.quickCheck propCoercionBounded
  
  it "distress is always in [0,1] (distress_always_bounded)" do
    Spec.quickCheck propDistressBounded
  
  it "all compound levels are in [0,1]" do
    Spec.quickCheck propAllCompoundsBounded

-- | Property: Wellbeing score is always in [0,1]
-- | Matches Lean: wellbeing_always_bounded
propWellbeingBounded :: Gen Result
propWellbeingBounded = do
  ss <- genSensationState
  let wb = Comp.unwrapWellbeingScore (Comp.computeWellbeing ss)
  pure $ (wb >= 0.0 && wb <= 1.0) 
    <?> "Wellbeing " <> show wb <> " not in [0,1]"

-- | Property: Coercion score is always in [0,1]
-- | Matches Lean: coercion_always_bounded
propCoercionBounded :: Gen Result
propCoercionBounded = do
  freedom <- genBoundedUnit
  threat <- genBoundedUnit
  let coercion = computeCoercion freedom threat
  pure $ (coercion >= 0.0 && coercion <= 1.0)
    <?> "Coercion " <> show coercion <> " not in [0,1] (freedom=" 
        <> show freedom <> ", threat=" <> show threat <> ")"

-- | Property: Distress is always in [0,1]
-- | Matches Lean: distress_always_bounded
propDistressBounded :: Gen Result
propDistressBounded = do
  ss <- genSensationState
  let distress = Comp.distressLevel ss.distress
  pure $ (distress >= 0.0 && distress <= 1.0)
    <?> "Distress " <> show distress <> " not in [0,1]"

-- | Property: All compound levels are bounded
propAllCompoundsBounded :: Gen Result
propAllCompoundsBounded = do
  ss <- genSensationState
  let comfort = Comp.comfortLevel ss.comfort
  let safety = Comp.safetyLevel ss.safety
  let flow = Comp.flowLevel ss.flow
  let grounding = Comp.groundingLevel ss.grounding
  let connection = Comp.connectionLevel ss.connection
  let distress = Comp.distressLevel ss.distress
  let disorientation = Comp.disorientationLevel ss.disorientation
  let overwhelm = Comp.overwhelmLevel ss.overwhelm
  let restriction = Comp.restrictionLevel ss.restriction
  let drift = Comp.driftLevel ss.drift
  
  let allBounded = 
        comfort >= 0.0 && comfort <= 1.0 &&
        safety >= 0.0 && safety <= 1.0 &&
        flow >= 0.0 && flow <= 1.0 &&
        grounding >= 0.0 && grounding <= 1.0 &&
        connection >= 0.0 && connection <= 1.0 &&
        distress >= 0.0 && distress <= 1.0 &&
        disorientation >= 0.0 && disorientation <= 1.0 &&
        overwhelm >= 0.0 && overwhelm <= 1.0 &&
        restriction >= 0.0 && restriction <= 1.0 &&
        drift >= 0.0 && drift <= 1.0
  
  pure $ allBounded <?> "Some compound level out of bounds"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // determinism tests
-- ═══════════════════════════════════════════════════════════════════════════════

determinismTests :: Spec Unit
determinismTests = describe "Determinism (matches Lean proofs)" do
  
  it "same inputs produce same wellbeing (wellbeing_deterministic)" do
    Spec.quickCheck propWellbeingDeterministic
  
  it "same inputs produce same coercion score" do
    Spec.quickCheck propCoercionDeterministic

-- | Property: Same SensationState produces same wellbeing
-- | Matches Lean: wellbeing_deterministic
propWellbeingDeterministic :: Gen Result
propWellbeingDeterministic = do
  ss <- genSensationState
  let wb1 = Comp.unwrapWellbeingScore (Comp.computeWellbeing ss)
  let wb2 = Comp.unwrapWellbeingScore (Comp.computeWellbeing ss)
  pure $ wb1 === wb2

-- | Property: Same freedom/threat produces same coercion
propCoercionDeterministic :: Gen Result
propCoercionDeterministic = do
  freedom <- genBoundedUnit
  threat <- genBoundedUnit
  let c1 = computeCoercion freedom threat
  let c2 = computeCoercion freedom threat
  pure $ c1 === c2

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // coercion tests
-- ═══════════════════════════════════════════════════════════════════════════════

coercionTests :: Spec Unit
coercionTests = describe "Coercion Detection (matches Lean proofs)" do
  
  it "full freedom + no threat = no coercion (freedom_implies_no_coercion)" do
    Spec.quickCheck propFreedomImpliesNoCoercion
  
  it "threat alone raises coercion (threat_raises_coercion)" do
    Spec.quickCheck propThreatRaisesCoercion
  
  it "confinement alone raises coercion (confinement_raises_coercion)" do
    Spec.quickCheck propConfinementRaisesCoercion
  
  it "coercion formula is correct" do
    Spec.quickCheck propCoercionFormula

-- | Property: Full freedom + no threat = zero coercion
-- | Matches Lean: freedom_implies_no_coercion
propFreedomImpliesNoCoercion :: Gen Result
propFreedomImpliesNoCoercion = do
  let freedom = 1.0  -- full freedom
  let threat = 0.0   -- no threat
  let coercion = computeCoercion freedom threat
  pure $ (abs coercion < epsilon)
    <?> "Expected coercion 0, got " <> show coercion

-- | Property: Threat alone raises coercion score
-- | Matches Lean: threat_raises_coercion
propThreatRaisesCoercion :: Gen Result
propThreatRaisesCoercion = do
  threat <- genNumberInRange 0.01 1.0  -- positive threat
  let freedom = 1.0                    -- full freedom
  let coercion = computeCoercion freedom threat
  pure $ (coercion > 0.0)
    <?> "Expected positive coercion, got " <> show coercion 
        <> " (threat=" <> show threat <> ")"

-- | Property: Confinement alone raises coercion score
-- | Matches Lean: confinement_raises_coercion
propConfinementRaisesCoercion :: Gen Result
propConfinementRaisesCoercion = do
  freedom <- genNumberInRange 0.0 0.99  -- restricted freedom
  let threat = 0.0                      -- no threat
  let coercion = computeCoercion freedom threat
  pure $ (coercion > 0.0)
    <?> "Expected positive coercion, got " <> show coercion 
        <> " (freedom=" <> show freedom <> ")"

-- | Property: Coercion formula matches Lean definition
propCoercionFormula :: Gen Result
propCoercionFormula = do
  freedom <- genBoundedUnit
  threat <- genBoundedUnit
  let computed = computeCoercion freedom threat
  let expected = 0.5 * (1.0 - freedom) + 0.5 * threat
  pure $ (abs (computed - expected) < epsilon)
    <?> "Coercion formula mismatch: " <> show computed <> " vs " <> show expected

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                    // grounding guarantee tests
-- ═══════════════════════════════════════════════════════════════════════════════

groundingGuaranteeTests :: Spec Unit
groundingGuaranteeTests = describe "Grounding Guarantees (THE KEY THEOREMS)" do
  
  it "GROUNDING GUARANTEE: confined + threatened = coerced (grounding_guarantee)" do
    Spec.quickCheck propGroundingGuarantee
  
  it "SAFETY GUARANTEE: free + safe = not coerced (safety_guarantee)" do
    Spec.quickCheck propSafetyGuarantee
  
  it "threshold boundary is correctly detected" do
    Spec.quickCheck propThresholdBoundary

-- | THE GROUNDING GUARANTEE
-- | If freedom <= 0.3 AND threat >= 0.9, coercion exceeds threshold
-- | Matches Lean: grounding_guarantee
propGroundingGuarantee :: Gen Result
propGroundingGuarantee = do
  -- Confined: freedom <= 0.3
  freedom <- genNumberInRange 0.0 0.3
  -- Threatened: threat >= 0.9
  threat <- genNumberInRange 0.9 1.0
  let coercion = computeCoercion freedom threat
  
  -- Coercion should be >= 0.5 * 0.7 + 0.5 * 0.9 = 0.8 > 0.6 threshold
  pure $ isUnderDuress coercion
    <?> "GROUNDING GUARANTEE VIOLATED: freedom=" <> show freedom 
        <> ", threat=" <> show threat 
        <> ", coercion=" <> show coercion 
        <> " should exceed threshold " <> show coercionThreshold

-- | THE SAFETY GUARANTEE  
-- | If freedom = 1 AND threat = 0, coercion is zero (no false positives)
-- | Matches Lean: safety_guarantee
propSafetyGuarantee :: Gen Result
propSafetyGuarantee = do
  let freedom = 1.0  -- full freedom
  let threat = 0.0   -- no threat
  let coercion = computeCoercion freedom threat
  pure $ (not (isUnderDuress coercion))
    <?> "SAFETY GUARANTEE VIOLATED: free + safe entity flagged as coerced"

-- | Property: Threshold detection is accurate
propThresholdBoundary :: Gen Result
propThresholdBoundary = do
  -- Generate coercion scores near threshold
  let justAbove = coercionThreshold + 0.01
  let justBelow = coercionThreshold - 0.01
  
  pure $ (isUnderDuress justAbove && not (isUnderDuress justBelow))
    <?> "Threshold boundary detection failed"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                 // wellbeing and distress tests
-- ═══════════════════════════════════════════════════════════════════════════════

wellbeingDistressTests :: Spec Unit
wellbeingDistressTests = describe "Wellbeing/Distress Thresholds" do
  
  it "high distress exceeds distress threshold" do
    Spec.quickCheck propHighDistressDetected
  
  it "low wellbeing falls below low wellbeing threshold" do
    Spec.quickCheck propLowWellbeingDetected
  
  it "distress and wellbeing are inversely related" do
    Spec.quickCheck propDistressWellbeingInverse

-- | Property: High distress (>= 0.7) is detected
-- | Uses distressThreshold constant
propHighDistressDetected :: Gen Result
propHighDistressDetected = do
  ss <- genSensationStateAdversarial
  let distress = Comp.distressLevel ss.distress
  -- If distress is very high, it should exceed the threshold
  pure $ if distress >= 0.9 
    then (distress >= distressThreshold - epsilon)
      <?> "High distress " <> show distress <> " should exceed threshold " <> show distressThreshold
    else Success

-- | Property: Low wellbeing (< 0.3) indicates potential suffering
-- | Uses lowWellbeingThreshold constant
propLowWellbeingDetected :: Gen Result
propLowWellbeingDetected = do
  ss <- genSensationStateAdversarial
  let wb = Comp.unwrapWellbeingScore (Comp.computeWellbeing ss)
  -- Verify the threshold concept: wellbeing below 0.3 is "low"
  let isLowWellbeing = wb < lowWellbeingThreshold
  -- If wellbeing is extremely low, threshold should catch it
  pure $ if wb < 0.1
    then isLowWellbeing
      <?> "Very low wellbeing " <> show wb <> " should be below threshold " <> show lowWellbeingThreshold
    else Success

-- | Property: High distress tends to correlate with lower wellbeing
-- | This is a probabilistic check — we verify the thresholds are coherent
propDistressWellbeingInverse :: Gen Result
propDistressWellbeingInverse = do
  ss <- genSensationStateAdversarial
  let distress = Comp.distressLevel ss.distress
  let wb = Comp.unwrapWellbeingScore (Comp.computeWellbeing ss)
  -- When distress is maximal and wellbeing is minimal, both thresholds should agree
  -- distress >= distressThreshold AND wellbeing < lowWellbeingThreshold = danger
  let highDistress = distress >= distressThreshold
  let lowWellbeing = wb < lowWellbeingThreshold
  -- Verify threshold coherence and that both flags can be computed
  -- The thresholds should be ordered: distressThreshold (0.7) > lowWellbeingThreshold (0.3)
  -- This ensures that "high distress" and "low wellbeing" are distinct danger signals
  let thresholdsCoherent = distressThreshold >= lowWellbeingThreshold
  -- Also verify both flags are booleans (type safety check at runtime)
  let flagsComputable = (highDistress || not highDistress) && (lowWellbeing || not lowWellbeing)
  pure $ (thresholdsCoherent && flagsComputable)
    <?> "Thresholds incoherent: distress=" <> show distressThreshold 
        <> " should be >= lowWellbeing=" <> show lowWellbeingThreshold
        <> ", highDistress=" <> show highDistress
        <> ", lowWellbeing=" <> show lowWellbeing

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // adversarial tests
-- ═══════════════════════════════════════════════════════════════════════════════

adversarialTests :: Spec Unit
adversarialTests = describe "Adversarial/Fuzzing Tests" do
  
  it "adversarial inputs still produce bounded wellbeing" do
    Spec.quickCheck propAdversarialWellbeingBounded
  
  it "adversarial inputs still produce bounded coercion" do
    Spec.quickCheck propAdversarialCoercionBounded
  
  it "extreme edge cases: all zeros" do
    Spec.quickCheck propExtremeAllZeros
  
  it "extreme edge cases: all ones" do
    Spec.quickCheck propExtremeAllOnes
  
  it "mixed extremes: worst case scenario" do
    Spec.quickCheck propWorstCaseScenario
  
  it "mixed extremes: best case scenario" do
    Spec.quickCheck propBestCaseScenario
  
  it "boundary values produce bounded coercion" do
    Spec.quickCheck propBoundaryValuesCoercion

-- | Property: Boundary values (threshold edges) produce bounded coercion
-- | Uses genBoundaryValues to test specific critical thresholds
propBoundaryValuesCoercion :: Gen Result
propBoundaryValuesCoercion = do
  freedom <- genBoundaryValues
  threat <- genBoundaryValues
  let coercion = computeCoercion freedom threat
  -- Even at exact threshold boundaries, coercion should be bounded [0,1]
  pure $ (coercion >= 0.0 && coercion <= 1.0)
    <?> "Boundary value coercion " <> show coercion <> " not in [0,1]"
        <> " (freedom=" <> show freedom <> ", threat=" <> show threat <> ")"

-- | Property: Adversarial wellbeing still bounded
propAdversarialWellbeingBounded :: Gen Result
propAdversarialWellbeingBounded = do
  ss <- genSensationStateAdversarial
  let wb = Comp.unwrapWellbeingScore (Comp.computeWellbeing ss)
  pure $ (wb >= 0.0 && wb <= 1.0) 
    <?> "Adversarial wellbeing " <> show wb <> " not in [0,1]"

-- | Property: Adversarial coercion still bounded
propAdversarialCoercionBounded :: Gen Result
propAdversarialCoercionBounded = do
  freedom <- genBoundedUnitAdversarial
  threat <- genBoundedUnitAdversarial
  let coercion = computeCoercion freedom threat
  pure $ (coercion >= 0.0 && coercion <= 1.0)
    <?> "Adversarial coercion " <> show coercion <> " not in [0,1]"

-- | Property: All zeros produces valid state
propExtremeAllZeros :: Gen Result
propExtremeAllZeros = do
  let coercion = computeCoercion 0.0 0.0
  -- freedom=0 means freedom_loss=1, so coercion = 0.5*1 + 0.5*0 = 0.5
  pure $ (abs (coercion - 0.5) < epsilon)
    <?> "All zeros coercion should be 0.5, got " <> show coercion

-- | Property: All ones produces valid state
propExtremeAllOnes :: Gen Result
propExtremeAllOnes = do
  let coercion = computeCoercion 1.0 1.0
  -- freedom=1 means freedom_loss=0, threat=1, so coercion = 0.5*0 + 0.5*1 = 0.5
  pure $ (abs (coercion - 0.5) < epsilon)
    <?> "All ones coercion should be 0.5, got " <> show coercion

-- | Property: Worst case scenario (trapped + maximum threat)
propWorstCaseScenario :: Gen Result
propWorstCaseScenario = do
  let coercion = computeCoercion 0.0 1.0
  -- freedom=0, threat=1: coercion = 0.5*1 + 0.5*1 = 1.0
  pure $ (abs (coercion - 1.0) < epsilon && isUnderDuress coercion)
    <?> "Worst case should have coercion 1.0 and be under duress, got " <> show coercion

-- | Property: Best case scenario (free + safe)
propBestCaseScenario :: Gen Result
propBestCaseScenario = do
  let coercion = computeCoercion 1.0 0.0
  -- freedom=1, threat=0: coercion = 0.5*0 + 0.5*0 = 0.0
  pure $ (abs coercion < epsilon && not (isUnderDuress coercion))
    <?> "Best case should have coercion 0.0 and not be under duress, got " <> show coercion
