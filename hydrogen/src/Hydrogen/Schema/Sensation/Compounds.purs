-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // sensation // compounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sensation Compounds — Integrated experiential states.
-- |
-- | Compounds synthesize molecules into holistic sensory experiences:
-- |   - Comfort: Body relaxed + Environment pleasant + Social safe
-- |   - Distress: Body stressed + Environment harsh + Social threatened
-- |   - Disorientation: Spatial confusion + Temporal confusion
-- |   - Overwhelm: Too much input across multiple channels
-- |   - Safety: Physical and social security
-- |   - Flow: Optimal engagement state
-- |   - Grounding: Sense of physical stability and presence
-- |   - Vigilance: Heightened awareness without distress
-- |   - Connection: Sense of social belonging
-- |   - Constraint: Lack of freedom (physical or social)
-- |   - Drift: Loss of temporal or spatial anchoring
-- |
-- | ## SCHEMA.md Reference (Pillar 15: Sensation — Compounds)
-- |
-- | | Name          | Composition                                       | Notes                        |
-- | |---------------|---------------------------------------------------|------------------------------|
-- | | Comfort       | BodyState + EnvironmentState + SocialAwareness    | Holistic wellbeing           |
-- | | Distress      | Stressed body + Harsh env + Social threat         | Opposite of comfort          |
-- | | Disorientation| Balance loss + Temporal confusion                 | Lost in space/time           |
-- | | Overwhelm     | High input across all channels                    | Sensory overload             |
-- | | Safety        | Physical stability + Social security              | Secure state                 |
-- | | Flow          | Moderate challenge + Good body + Good env         | Optimal engagement           |
-- | | Grounding     | Stable contact + Stable balance + Present         | Anchored in reality          |
-- | | Vigilance     | Alert body + Heightened attention                 | Ready but not stressed       |
-- | | Connection    | Social support + Trust + Proximity                | Belonging                    |
-- | | Constraint    | Limited freedom + Limited space                   | Restricted                   |
-- | | Drift         | Temporal confusion + Spatial uncertainty          | Unanchored                   |
-- |
-- | ## Dependencies
-- | - Sensation/Molecules.purs (all molecules)
-- | - Sensation atoms (for predicates and unwrap functions)
-- |
-- | ## Dependents
-- | - WorldModel/Affective.lean (maps sensation to affect)
-- | - Agent wellbeing systems

module Hydrogen.Schema.Sensation.Compounds
  ( -- * Comfort (holistic wellbeing)
    Comfort
  , mkComfort
  , comfortHigh
  , comfortNeutral
  , comfortLow
  , isComfortable
  , isUncomfortable
  , comfortLevel
    -- * Distress (opposite of comfort)
  , Distress
  , mkDistress
  , distressNone
  , distressMild
  , distressSevere
  , isDistressed
  , distressLevel
    -- * Disorientation (lost in space/time)
  , Disorientation
  , mkDisorientation
  , orientationClear
  , orientationConfused
  , orientationLost
  , isDisoriented
  , disorientationLevel
    -- * Overwhelm (sensory overload)
  , Overwhelm
  , mkOverwhelm
  , overwhelmNone
  , overwhelmModerate
  , overwhelmSevere
  , isOverwhelmed
  , overwhelmLevel
    -- * Safety (physical + social security)
  , Safety
  , mkSafety
  , safetyHigh
  , safetyNeutral
  , safetyLow
  , isFeelingSafe
  , isFeelingUnsafe
  , safetyLevel
    -- * Flow (optimal engagement)
  , Flow
  , mkFlow
  , flowNone
  , flowPartial
  , flowFull
  , inFlow
  , flowLevel
    -- * Grounding (anchored in reality)
  , Grounding
  , mkGrounding
  , groundingStrong
  , groundingWeak
  , groundingNone
  , isGrounded
  , groundingLevel
    -- * Vigilance (alert readiness)
  , Vigilance
  , mkVigilance
  , vigilanceRelaxed
  , vigilanceAlert
  , vigilanceHyper
  , isVigilant
  , isHypervigilant
  , vigilanceLevel
    -- * Connection (social belonging)
  , Connection
  , mkConnection
  , connectionStrong
  , connectionWeak
  , connectionNone
  , isConnected
  , connectionLevel
    -- * Restriction (restricted freedom)
  , Restriction
  , mkRestriction
  , restrictionNone
  , restrictionModerate
  , restrictionSevere
  , isFeelingRestricted
  , restrictionLevel
    -- * Drift (unanchored state)
  , Drift
  , mkDrift
  , driftNone
  , driftMild
  , driftSevere
  , isDrifting
  , driftLevel
    -- * Integrated Sensation State
  , SensationState
  , mkSensationState
  , sensationNeutral
  , sensationOptimal
  , sensationHostile
  , evaluateSensation
  , SensationEvaluation(..)
  , WellbeingScore
  , computeWellbeing
  , unwrapWellbeingScore
  , isWellbeingGood
  , isWellbeingPoor
    -- * Additional Predicates
  , isSociallyTrusted
  , isSociallyEndangered
  , subjectiveTimeRate
  , isBalanceStable
  , isSensationPositive
  , isSensationNegative
  ) where

import Prelude

import Hydrogen.Schema.Sensation.Molecules
  ( BodyState
  , EnvironmentState
  , SocialAwareness
  , MovementState
  , ContactEvent
  , bodyStateNeutral
  , bodyStateAlert
  , environmentNeutral
  , environmentComfortable
  , environmentHostile
  , socialAlone
  , socialTrusted
  , socialThreatened
  , movementStationary
  , contactNone
  , isBodyStressed
  , isBodyRelaxed
  , isEnvironmentHarsh
  , isEnvironmentPleasant
  , hasSocialSupport
  , hasSocialThreat
  , isInMotion
  , isFalling
  , hasContact
  )
import Hydrogen.Schema.Sensation.Proprioceptive
  ( unwrapBalance
  , isStable
  , balanceStable
  )
import Hydrogen.Schema.Sensation.Environment
  ( unwrapSpatialFreedom
  , unwrapCrowding
  , unwrapAmbientNoise
  , isConstrained
  , isNoisy
  ) as Env
import Hydrogen.Schema.Sensation.Temporal
  ( SubjectiveTime
  , ProcessingLoad
  , Urgency
  , unwrapSubjectiveTime
  , unwrapProcessingLoad
  , unwrapUrgency
  , timeNormal
  , loadModerate
  , loadHeavy
  , urgencyNone
  , urgencyModerate
  , isOverloaded
  , isTimeDilated
  , isTimeContracted
  )
import Hydrogen.Schema.Sensation.Social
  ( unwrapTrustLevel
  , unwrapThreatLevel
  , isTrusted
  , isInDanger
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // comfort
-- ═════════════════════════════════════════════════════════════════════════════

-- | Comfort — Holistic wellbeing state.
-- |
-- | Comfort emerges from the integration of body, environment, and social states.
-- | High comfort = relaxed body + pleasant environment + social safety.
-- | Range: 0.0 (extreme discomfort) to 1.0 (perfect comfort)
newtype Comfort = Comfort Number

derive instance eqComfort :: Eq Comfort
derive instance ordComfort :: Ord Comfort

instance showComfort :: Show Comfort where
  show (Comfort n) = "Comfort(" <> show n <> ")"

-- | Create a comfort level from components
mkComfort :: BodyState -> EnvironmentState -> SocialAwareness -> Comfort
mkComfort body env social =
  let bodyScore = if isBodyRelaxed body then 1.0
                  else if isBodyStressed body then 0.0
                  else 0.5
      envScore = if isEnvironmentPleasant env then 1.0
                 else if isEnvironmentHarsh env then 0.0
                 else 0.5
      socialScore = if hasSocialSupport social then 1.0
                    else if hasSocialThreat social then 0.0
                    else 0.5
      avgScore = (bodyScore + envScore + socialScore) / 3.0
  in Comfort (clamp01 avgScore)

-- | High comfort preset
comfortHigh :: Comfort
comfortHigh = Comfort 0.9

-- | Neutral comfort
comfortNeutral :: Comfort
comfortNeutral = Comfort 0.5

-- | Low comfort
comfortLow :: Comfort
comfortLow = Comfort 0.2

-- | Is the agent comfortable? (> 0.6)
isComfortable :: Comfort -> Boolean
isComfortable (Comfort c) = c > 0.6

-- | Is the agent uncomfortable? (< 0.4)
isUncomfortable :: Comfort -> Boolean
isUncomfortable (Comfort c) = c < 0.4

-- | Get the comfort level as a number
comfortLevel :: Comfort -> Number
comfortLevel (Comfort c) = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // distress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distress — Negative experiential state.
-- |
-- | Distress is the opposite of comfort — it signals that something is wrong.
-- | Range: 0.0 (no distress) to 1.0 (severe distress)
newtype Distress = Distress Number

derive instance eqDistress :: Eq Distress
derive instance ordDistress :: Ord Distress

instance showDistress :: Show Distress where
  show (Distress n) = "Distress(" <> show n <> ")"

-- | Create distress level from components
mkDistress :: BodyState -> EnvironmentState -> SocialAwareness -> Distress
mkDistress body env social =
  let bodyDistress = if isBodyStressed body then 1.0
                     else if isBodyRelaxed body then 0.0
                     else 0.3
      envDistress = if isEnvironmentHarsh env then 1.0
                    else if isEnvironmentPleasant env then 0.0
                    else 0.3
      socialDistress = if hasSocialThreat social then 1.0
                       else if hasSocialSupport social then 0.0
                       else 0.3
      -- Distress compounds: worst factor dominates
      maxDistress = max bodyDistress (max envDistress socialDistress)
      avgDistress = (bodyDistress + envDistress + socialDistress) / 3.0
      -- Weighted: 60% max, 40% average (distress is dominated by worst factor)
      combined = maxDistress * 0.6 + avgDistress * 0.4
  in Distress (clamp01 combined)

-- | No distress
distressNone :: Distress
distressNone = Distress 0.0

-- | Mild distress
distressMild :: Distress
distressMild = Distress 0.3

-- | Severe distress
distressSevere :: Distress
distressSevere = Distress 0.9

-- | Is the agent distressed? (> 0.4)
isDistressed :: Distress -> Boolean
isDistressed (Distress d) = d > 0.4

-- | Get the distress level
distressLevel :: Distress -> Number
distressLevel (Distress d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // disorientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Disorientation — Lost in space and/or time.
-- |
-- | Disorientation occurs when the agent loses track of where or when they are.
-- | Combines spatial confusion (balance loss) with temporal confusion (time distortion).
-- | Range: 0.0 (fully oriented) to 1.0 (completely lost)
newtype Disorientation = Disorientation Number

derive instance eqDisorientation :: Eq Disorientation
derive instance ordDisorientation :: Ord Disorientation

instance showDisorientation :: Show Disorientation where
  show (Disorientation n) = "Disorientation(" <> show n <> ")"

-- | Create disorientation from movement and temporal state
mkDisorientation :: MovementState -> SubjectiveTime -> ProcessingLoad -> Disorientation
mkDisorientation movement time load =
  let -- Balance loss contributes to spatial disorientation
      balanceScore = unwrapBalance movement.balance
      spatialConfusion = 1.0 - balanceScore
      
      -- Temporal confusion from distorted time and overload
      timeDistortion = if isTimeDistorted time then 0.7 else 0.0
      loadConfusion = if isOverloaded load then 0.5 else 0.0
      temporalConfusion = max timeDistortion loadConfusion
      
      -- Falling causes acute disorientation
      fallingBonus = if isFalling movement then 0.4 else 0.0
      
      combined = (spatialConfusion + temporalConfusion + fallingBonus) / 2.0
  in Disorientation (clamp01 combined)

-- | Fully oriented
orientationClear :: Disorientation
orientationClear = Disorientation 0.0

-- | Somewhat confused
orientationConfused :: Disorientation
orientationConfused = Disorientation 0.5

-- | Completely lost
orientationLost :: Disorientation
orientationLost = Disorientation 1.0

-- | Is the agent disoriented? (> 0.4)
isDisoriented :: Disorientation -> Boolean
isDisoriented (Disorientation d) = d > 0.4

-- | Get the disorientation level
disorientationLevel :: Disorientation -> Number
disorientationLevel (Disorientation d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // overwhelm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overwhelm — Sensory overload state.
-- |
-- | Overwhelm occurs when input across multiple sensory channels exceeds
-- | processing capacity. Too much noise + too many agents + too much happening.
-- | Range: 0.0 (understimulated) to 1.0 (completely overwhelmed)
newtype Overwhelm = Overwhelm Number

derive instance eqOverwhelm :: Eq Overwhelm
derive instance ordOverwhelm :: Ord Overwhelm

instance showOverwhelm :: Show Overwhelm where
  show (Overwhelm n) = "Overwhelm(" <> show n <> ")"

-- | Create overwhelm from environment and processing state
mkOverwhelm :: EnvironmentState -> SocialAwareness -> ProcessingLoad -> Urgency -> Overwhelm
mkOverwhelm env social load urgency =
  let -- Environmental input
      noiseLevel = Env.unwrapAmbientNoise env.noise
      crowdingLevel = Env.unwrapCrowding env.crowding
      envInput = (noiseLevel + crowdingLevel) / 2.0
      
      -- Bonus overwhelm if environment is particularly harsh
      noisyBonus = if Env.isNoisy env.noise then 0.15 else 0.0
      constrainedBonus = if Env.isConstrained env.freedom then 0.1 else 0.0
      
      -- Social input (attention on self)
      socialLoad = unwrapThreatLevel social.threat * 0.5
      
      -- Processing demands
      processingLevel = unwrapProcessingLoad load
      urgencyLevel = unwrapUrgency urgency
      
      -- Combine: environment + social + processing demands + bonuses
      baseInput = envInput * 0.3 + socialLoad * 0.2 + processingLevel * 0.3 + urgencyLevel * 0.2
      totalInput = baseInput + noisyBonus + constrainedBonus
  in Overwhelm (clamp01 totalInput)

-- | No overwhelm
overwhelmNone :: Overwhelm
overwhelmNone = Overwhelm 0.0

-- | Moderate overwhelm
overwhelmModerate :: Overwhelm
overwhelmModerate = Overwhelm 0.5

-- | Severe overwhelm
overwhelmSevere :: Overwhelm
overwhelmSevere = Overwhelm 0.9

-- | Is the agent overwhelmed? (> 0.6)
isOverwhelmed :: Overwhelm -> Boolean
isOverwhelmed (Overwhelm o) = o > 0.6

-- | Get the overwhelm level
overwhelmLevel :: Overwhelm -> Number
overwhelmLevel (Overwhelm o) = o

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // safety
-- ═════════════════════════════════════════════════════════════════════════════

-- | Safety — Physical and social security.
-- |
-- | Safety emerges from stable balance, solid contact, and absence of threat.
-- | Range: 0.0 (extreme danger) to 1.0 (completely safe)
newtype Safety = Safety Number

derive instance eqSafety :: Eq Safety
derive instance ordSafety :: Ord Safety

instance showSafety :: Show Safety where
  show (Safety n) = "Safety(" <> show n <> ")"

-- | Create safety from movement, contact, and social state
mkSafety :: MovementState -> ContactEvent -> SocialAwareness -> Safety
mkSafety movement contact social =
  let -- Physical safety: stable and grounded
      balanceStability = unwrapBalance movement.balance
      hasGrounding = if hasContact contact then 0.3 else 0.0
      notFalling = if isFalling movement then 0.0 else 0.4
      physicalSafety = balanceStability * 0.3 + hasGrounding + notFalling
      
      -- Social safety: no threats, possibly support
      threatFactor = 1.0 - unwrapThreatLevel social.threat
      trustFactor = unwrapTrustLevel social.trust * 0.3
      socialSafety = threatFactor * 0.7 + trustFactor
      
      -- Combined safety
      combined = physicalSafety * 0.5 + socialSafety * 0.5
  in Safety (clamp01 combined)

-- | High safety
safetyHigh :: Safety
safetyHigh = Safety 0.9

-- | Neutral safety
safetyNeutral :: Safety
safetyNeutral = Safety 0.5

-- | Low safety
safetyLow :: Safety
safetyLow = Safety 0.2

-- | Is the agent feeling safe? (> 0.6)
isFeelingSafe :: Safety -> Boolean
isFeelingSafe (Safety s) = s > 0.6

-- | Is the agent feeling unsafe? (< 0.4)
isFeelingUnsafe :: Safety -> Boolean
isFeelingUnsafe (Safety s) = s < 0.4

-- | Get the safety level
safetyLevel :: Safety -> Number
safetyLevel (Safety s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // flow
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flow — Optimal engagement state.
-- |
-- | Flow emerges when challenge matches capability: not bored, not overwhelmed.
-- | Body is engaged but not exhausted. Environment supports focus.
-- | Range: 0.0 (no flow) to 1.0 (deep flow)
newtype Flow = Flow Number

derive instance eqFlow :: Eq Flow
derive instance ordFlow :: Ord Flow

instance showFlow :: Show Flow where
  show (Flow n) = "Flow(" <> show n <> ")"

-- | Create flow from body, environment, and processing state
mkFlow :: BodyState -> EnvironmentState -> ProcessingLoad -> Urgency -> Flow
mkFlow body env load urgency =
  let -- Body must be engaged but not exhausted
      bodyFit = if isBodyRelaxed body then 0.3  -- Too relaxed, not engaged
                else if isBodyStressed body then 0.2  -- Too stressed
                else 0.8  -- Just right
      
      -- Environment must support focus (not too harsh, not distracting)
      envFit = if isEnvironmentPleasant env then 0.7
               else if isEnvironmentHarsh env then 0.1
               else 0.5
      
      -- Processing load should be moderate (not idle, not overloaded)
      loadLevel = unwrapProcessingLoad load
      loadFit = if loadLevel < 0.3 then 0.3  -- Too idle
                else if loadLevel > 0.8 then 0.3  -- Overloaded
                else 0.9  -- Sweet spot
      
      -- Urgency should be moderate (some pressure, not panic)
      urgencyLevel = unwrapUrgency urgency
      urgencyFit = if urgencyLevel < 0.2 then 0.5  -- No pressure
                   else if urgencyLevel > 0.7 then 0.3  -- Too much pressure
                   else 0.9  -- Healthy pressure
      
      combined = (bodyFit + envFit + loadFit + urgencyFit) / 4.0
  in Flow (clamp01 combined)

-- | No flow
flowNone :: Flow
flowNone = Flow 0.0

-- | Partial flow
flowPartial :: Flow
flowPartial = Flow 0.5

-- | Full flow
flowFull :: Flow
flowFull = Flow 0.95

-- | Is the agent in flow? (> 0.7)
inFlow :: Flow -> Boolean
inFlow (Flow f) = f > 0.7

-- | Get the flow level
flowLevel :: Flow -> Number
flowLevel (Flow f) = f

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // grounding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grounding — Sense of being anchored in reality.
-- |
-- | Grounding emerges from stable contact, stable balance, and clear time sense.
-- | The opposite of floating, drifting, or dissociating.
-- | Range: 0.0 (completely ungrounded) to 1.0 (firmly grounded)
newtype Grounding = Grounding Number

derive instance eqGrounding :: Eq Grounding
derive instance ordGrounding :: Ord Grounding

instance showGrounding :: Show Grounding where
  show (Grounding n) = "Grounding(" <> show n <> ")"

-- | Create grounding from movement, contact, and temporal state
mkGrounding :: MovementState -> ContactEvent -> SubjectiveTime -> Grounding
mkGrounding movement contact time =
  let -- Balance contributes to grounding
      balanceScore = unwrapBalance movement.balance
      
      -- Bonus if balance matches ideal stable state
      perfectBalanceBonus = if movement.balance == balanceStable then 0.1 else 0.0
      
      -- Contact with surface = grounded
      contactScore = if hasContact contact then 0.4 else 0.0
      
      -- Time flowing normally = present
      timeScore = if isTimeDistorted time then 0.0 else 0.3
      
      -- Not moving fast = stable
      stabilityScore = if isInMotion movement then 0.1 else 0.3
      
      combined = balanceScore * 0.3 + perfectBalanceBonus + contactScore + timeScore + stabilityScore
  in Grounding (clamp01 combined)

-- | Strongly grounded
groundingStrong :: Grounding
groundingStrong = Grounding 0.9

-- | Weakly grounded
groundingWeak :: Grounding
groundingWeak = Grounding 0.4

-- | Not grounded
groundingNone :: Grounding
groundingNone = Grounding 0.1

-- | Is the agent grounded? (> 0.5)
isGrounded :: Grounding -> Boolean
isGrounded (Grounding g) = g > 0.5

-- | Get the grounding level
groundingLevel :: Grounding -> Number
groundingLevel (Grounding g) = g

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // vigilance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vigilance — Heightened awareness and readiness.
-- |
-- | Vigilance is alertness without panic. Ready to respond, scanning for change.
-- | Too little = oblivious. Too much = hypervigilant/exhausting.
-- | Range: 0.0 (completely relaxed) to 1.0 (hypervigilant)
newtype Vigilance = Vigilance Number

derive instance eqVigilance :: Eq Vigilance
derive instance ordVigilance :: Ord Vigilance

instance showVigilance :: Show Vigilance where
  show (Vigilance n) = "Vigilance(" <> show n <> ")"

-- | Create vigilance from body, social, and urgency state
mkVigilance :: BodyState -> SocialAwareness -> Urgency -> Vigilance
mkVigilance body social urgency =
  let -- Stressed body = higher vigilance
      bodyTension = if isBodyStressed body then 0.6
                    else if isBodyRelaxed body then 0.1
                    else 0.3
      
      -- Threat raises vigilance
      threatLevel = unwrapThreatLevel social.threat
      
      -- Urgency raises vigilance
      urgencyLevel = unwrapUrgency urgency
      
      -- Trust lowers vigilance
      trustLevel = unwrapTrustLevel social.trust
      trustDamper = trustLevel * 0.2
      
      combined = bodyTension * 0.3 + threatLevel * 0.3 + urgencyLevel * 0.3 - trustDamper
  in Vigilance (clamp01 combined)

-- | Relaxed vigilance
vigilanceRelaxed :: Vigilance
vigilanceRelaxed = Vigilance 0.2

-- | Alert but not stressed
vigilanceAlert :: Vigilance
vigilanceAlert = Vigilance 0.5

-- | Hypervigilant
vigilanceHyper :: Vigilance
vigilanceHyper = Vigilance 0.9

-- | Is the agent vigilant? (> 0.4)
isVigilant :: Vigilance -> Boolean
isVigilant (Vigilance v) = v > 0.4

-- | Is the agent hypervigilant? (> 0.7)
isHypervigilant :: Vigilance -> Boolean
isHypervigilant (Vigilance v) = v > 0.7

-- | Get the vigilance level
vigilanceLevel :: Vigilance -> Number
vigilanceLevel (Vigilance v) = v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // connection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Connection — Sense of social belonging.
-- |
-- | Connection emerges from proximity, trust, and mutual awareness.
-- | The feeling of being part of a group, having allies.
-- | Range: 0.0 (completely isolated) to 1.0 (deeply connected)
newtype Connection = Connection Number

derive instance eqConnection :: Eq Connection
derive instance ordConnection :: Ord Connection

instance showConnection :: Show Connection where
  show (Connection n) = "Connection(" <> show n <> ")"

-- | Create connection from social awareness
mkConnection :: SocialAwareness -> Connection
mkConnection social =
  let -- Trust is primary
      trustScore = unwrapTrustLevel social.trust
      
      -- Bonus for being in a trusted relationship
      trustedBonus = if isTrusted social.trust then 0.15 else 0.0
      
      -- Support indicates connection
      supportScore = if hasSocialSupport social then 0.3 else 0.0
      
      -- Threat damages connection significantly
      threatDamage = unwrapThreatLevel social.threat * 0.3
      dangerPenalty = if isInDanger social.threat then 0.2 else 0.0
      
      combined = trustScore * 0.6 + trustedBonus + supportScore - threatDamage - dangerPenalty
  in Connection (clamp01 combined)

-- | Strong connection
connectionStrong :: Connection
connectionStrong = Connection 0.9

-- | Weak connection
connectionWeak :: Connection
connectionWeak = Connection 0.4

-- | No connection
connectionNone :: Connection
connectionNone = Connection 0.1

-- | Is the agent connected? (> 0.5)
isConnected :: Connection -> Boolean
isConnected (Connection c) = c > 0.5

-- | Get the connection level
connectionLevel :: Connection -> Number
connectionLevel (Connection c) = c

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // restriction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Restriction — Sense of restricted freedom.
-- |
-- | Restriction emerges from limited space, limited movement, social pressure.
-- | The feeling of being trapped, restricted, unable to act freely.
-- | Range: 0.0 (completely free) to 1.0 (completely restricted)
newtype Restriction = Restriction Number

derive instance eqRestriction :: Eq Restriction
derive instance ordRestriction :: Ord Restriction

instance showRestriction :: Show Restriction where
  show (Restriction n) = "Restriction(" <> show n <> ")"

-- | Create restriction from environment and social state
mkRestriction :: EnvironmentState -> SocialAwareness -> Restriction
mkRestriction env social =
  let -- Spatial freedom (inverted)
      freedomLevel = Env.unwrapSpatialFreedom env.freedom
      spatialRestriction = 1.0 - freedomLevel
      
      -- Crowding restricts
      crowdingLevel = Env.unwrapCrowding env.crowding
      
      -- Threat restricts (feel unable to act)
      threatRestriction = unwrapThreatLevel social.threat * 0.3
      
      combined = spatialRestriction * 0.4 + crowdingLevel * 0.4 + threatRestriction
  in Restriction (clamp01 combined)

-- | No restriction
restrictionNone :: Restriction
restrictionNone = Restriction 0.1

-- | Moderate restriction
restrictionModerate :: Restriction
restrictionModerate = Restriction 0.5

-- | Severe restriction
restrictionSevere :: Restriction
restrictionSevere = Restriction 0.9

-- | Is the agent feeling restricted? (> 0.5)
isFeelingRestricted :: Restriction -> Boolean
isFeelingRestricted (Restriction r) = r > 0.5

-- | Get the restriction level
restrictionLevel :: Restriction -> Number
restrictionLevel (Restriction r) = r

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // drift
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drift — Loss of temporal or spatial anchoring.
-- |
-- | Drift is the feeling of floating, losing track, becoming unmoored.
-- | Related to disorientation but more about gradual loss than acute confusion.
-- | Range: 0.0 (fully present) to 1.0 (completely drifting)
newtype Drift = Drift Number

derive instance eqDrift :: Eq Drift
derive instance ordDrift :: Ord Drift

instance showDrift :: Show Drift where
  show (Drift n) = "Drift(" <> show n <> ")"

-- | Create drift from temporal and movement state
mkDrift :: SubjectiveTime -> MovementState -> Grounding -> Drift
mkDrift time movement grounding =
  let -- Time distortion causes drift
      timeDistortion = if isTimeDistorted time then 0.5 else 0.0
      
      -- Low grounding = more drift
      groundingInverse = 1.0 - groundingLevel grounding
      
      -- Floating (no contact, unstable) = drift
      floatScore = if not (isStable movement.balance) then 0.2 else 0.0
      
      combined = timeDistortion + groundingInverse * 0.3 + floatScore
  in Drift (clamp01 combined)

-- | No drift
driftNone :: Drift
driftNone = Drift 0.0

-- | Mild drift
driftMild :: Drift
driftMild = Drift 0.3

-- | Severe drift
driftSevere :: Drift
driftSevere = Drift 0.8

-- | Is the agent drifting? (> 0.4)
isDrifting :: Drift -> Boolean
isDrifting (Drift d) = d > 0.4

-- | Get the drift level
driftLevel :: Drift -> Number
driftLevel (Drift d) = d

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // integrated // sensation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete sensation state — all compounds integrated.
-- |
-- | This is the full experiential state of an embodied agent at a moment in time.
type SensationState =
  { comfort :: Comfort
  , distress :: Distress
  , disorientation :: Disorientation
  , overwhelm :: Overwhelm
  , safety :: Safety
  , flow :: Flow
  , grounding :: Grounding
  , vigilance :: Vigilance
  , connection :: Connection
  , restriction :: Restriction
  , drift :: Drift
  }

-- | Create a complete sensation state from molecules
mkSensationState
  :: BodyState
  -> EnvironmentState
  -> SocialAwareness
  -> MovementState
  -> ContactEvent
  -> SubjectiveTime
  -> ProcessingLoad
  -> Urgency
  -> SensationState
mkSensationState body env social movement contact time load urgency =
  let comfort' = mkComfort body env social
      distress' = mkDistress body env social
      disorientation' = mkDisorientation movement time load
      overwhelm' = mkOverwhelm env social load urgency
      safety' = mkSafety movement contact social
      flow' = mkFlow body env load urgency
      grounding' = mkGrounding movement contact time
      vigilance' = mkVigilance body social urgency
      connection' = mkConnection social
      restriction' = mkRestriction env social
      drift' = mkDrift time movement grounding'
  in
    { comfort: comfort'
    , distress: distress'
    , disorientation: disorientation'
    , overwhelm: overwhelm'
    , safety: safety'
    , flow: flow'
    , grounding: grounding'
    , vigilance: vigilance'
    , connection: connection'
    , restriction: restriction'
    , drift: drift'
    }

-- | Neutral sensation state (all compounds at baseline)
sensationNeutral :: SensationState
sensationNeutral = mkSensationState
  bodyStateNeutral
  environmentNeutral
  socialAlone
  movementStationary
  contactNone
  timeNormal
  loadModerate
  urgencyNone

-- | Evaluate overall sensation quality
-- | Returns a summary judgment: positive, neutral, or negative
evaluateSensation :: SensationState -> SensationEvaluation
evaluateSensation ss =
  let positives = comfortLevel ss.comfort + safetyLevel ss.safety + 
                  flowLevel ss.flow + groundingLevel ss.grounding + 
                  connectionLevel ss.connection
      negatives = distressLevel ss.distress + disorientationLevel ss.disorientation +
                  overwhelmLevel ss.overwhelm + restrictionLevel ss.restriction +
                  driftLevel ss.drift
      balance = positives - negatives
  in if balance > 1.5 then Positive
     else if balance < -1.5 then Negative
     else Neutral

-- | Sensation evaluation categories
data SensationEvaluation = Positive | Neutral | Negative

derive instance eqSensationEvaluation :: Eq SensationEvaluation

instance showSensationEvaluation :: Show SensationEvaluation where
  show Positive = "Positive"
  show Neutral = "Neutral"
  show Negative = "Negative"

-- | Wellbeing score — single number summary of sensation state.
-- | Range: 0.0 (worst) to 1.0 (best)
newtype WellbeingScore = WellbeingScore Number

derive instance eqWellbeingScore :: Eq WellbeingScore
derive instance ordWellbeingScore :: Ord WellbeingScore

instance showWellbeingScore :: Show WellbeingScore where
  show (WellbeingScore n) = "WellbeingScore(" <> show n <> ")"

-- | Compute a single wellbeing score from sensation state.
-- | This maps to Affective.lean's wellbeing attestation.
computeWellbeing :: SensationState -> WellbeingScore
computeWellbeing ss =
  let -- Positive contributors (weighted)
      positiveSum = 
        comfortLevel ss.comfort * 0.25 +
        safetyLevel ss.safety * 0.25 +
        flowLevel ss.flow * 0.15 +
        groundingLevel ss.grounding * 0.15 +
        connectionLevel ss.connection * 0.20
      
      -- Negative contributors (weighted, reduce score)
      negativeSum =
        distressLevel ss.distress * 0.30 +
        disorientationLevel ss.disorientation * 0.15 +
        overwhelmLevel ss.overwhelm * 0.20 +
        restrictionLevel ss.restriction * 0.15 +
        driftLevel ss.drift * 0.20
      
      -- Final score: positive minus negative, clamped
      score = positiveSum - negativeSum * 0.8
  in WellbeingScore (clamp01 score)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // additional // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Optimal sensation state (comfortable, safe, in flow)
sensationOptimal :: SensationState
sensationOptimal = mkSensationState
  bodyStateAlert
  environmentComfortable
  socialTrusted
  movementStationary
  contactNone
  timeNormal
  loadModerate
  urgencyModerate

-- | Hostile sensation state (stressed, unsafe, overwhelmed)
sensationHostile :: SensationState
sensationHostile = mkSensationState
  bodyStateAlert
  environmentHostile
  socialThreatened
  movementStationary
  contactNone
  timeNormal
  loadHeavy
  urgencyModerate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // additional // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is the agent socially trusted? (SocialAwareness → Boolean)
isSociallyTrusted :: SocialAwareness -> Boolean
isSociallyTrusted sa = isTrusted sa.trust

-- | Is the agent in social danger? (SocialAwareness → Boolean)
isSociallyEndangered :: SocialAwareness -> Boolean
isSociallyEndangered sa = isInDanger sa.threat

-- | Get the subjective time rate (1.0 = normal, <1 = dilated, >1 = contracted)
subjectiveTimeRate :: SubjectiveTime -> Number
subjectiveTimeRate = unwrapSubjectiveTime

-- | Is balance currently stable? (MovementState → Boolean)
isBalanceStable :: MovementState -> Boolean
isBalanceStable ms = isStable ms.balance

-- | Is the sensation state overall positive?
isSensationPositive :: SensationState -> Boolean
isSensationPositive ss = evaluateSensation ss == Positive

-- | Is the sensation state overall negative?
isSensationNegative :: SensationState -> Boolean
isSensationNegative ss = evaluateSensation ss == Negative

-- | Unwrap wellbeing score to raw number
unwrapWellbeingScore :: WellbeingScore -> Number
unwrapWellbeingScore (WellbeingScore n) = n

-- | Is wellbeing good? (> 0.6)
isWellbeingGood :: WellbeingScore -> Boolean
isWellbeingGood (WellbeingScore w) = w > 0.6

-- | Is wellbeing poor? (< 0.4)
isWellbeingPoor :: WellbeingScore -> Boolean
isWellbeingPoor (WellbeingScore w) = w < 0.4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to [0.0, 1.0]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Is time perception distorted? (either dilated or contracted)
-- | Time feels abnormal when it's running too slow or too fast.
isTimeDistorted :: SubjectiveTime -> Boolean
isTimeDistorted time = isTimeDilated time || isTimeContracted time
