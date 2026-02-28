-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // schema // sensation // molecules
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sensation Molecules — Composed sensation primitives.
-- |
-- | Molecules combine atoms into meaningful composite sensations:
-- |   - BodyState: Proprioceptive + Contact atoms
-- |   - EnvironmentState: Environmental + Force atoms
-- |   - SocialAwareness: Social atoms
-- |   - ContactEvent: What I'm touching, where, how
-- |   - MovementState: How I'm moving
-- |
-- | ## SCHEMA.md Reference (Pillar 15: Sensation — Molecules)
-- |
-- | | Name             | Composition                              | Notes                     |
-- | |------------------|------------------------------------------|---------------------------|
-- | | BodyState        | Proprioceptive + Contact atoms           | Full self-sensation       |
-- | | EnvironmentState | Environmental + Force atoms              | Full world-sensation      |
-- | | SocialAwareness  | Social atoms                             | Awareness of others       |
-- | | ContactEvent     | Pressure + Normal + Position             | Single touch event        |
-- | | MovementState    | Momentum + Effort + Balance              | How I'm moving            |
-- |
-- | ## Dependencies
-- | - Sensation/Proprioceptive.purs
-- | - Sensation/Contact.purs
-- | - Sensation/Environment.purs
-- | - Sensation/Force.purs
-- | - Sensation/Temporal.purs
-- | - Sensation/Social.purs
-- |
-- | ## Dependents
-- | - Sensation/Compounds.purs (uses molecules to build integrated states)

module Hydrogen.Schema.Sensation.Molecules
  ( -- * BodyState (self-sensation)
    BodyState
  , mkBodyState
  , bodyStateNeutral
  , bodyStateExhausted
  , bodyStateAlert
  , isBodyStressed
  , isBodyRelaxed
  , isBodyExhausted
  , bodyEffortLevel
  , bodyFatigueLevel
  , bodyStrainLevel
  , bodyBalanceLevel
    -- * EnvironmentState (world-sensation)
  , EnvironmentState
  , mkEnvironmentState
  , environmentNeutral
  , environmentHostile
  , environmentComfortable
  , isEnvironmentHarsh
  , isEnvironmentPleasant
  , environmentLightLevel
  , environmentNoiseLevel
  , environmentCrowdingLevel
  , environmentFreedomLevel
    -- * SocialAwareness (others-sensation)
  , SocialAwareness
  , mkSocialAwareness
  , socialAlone
  , socialCrowd
  , socialTrusted
  , socialThreatened
  , hasSocialSupport
  , hasSocialThreat
  , hasSocialDanger
  , hasTrustedCompanions
  , socialTrustLevel
  , socialThreatLevel
    -- * ContactEvent (single touch)
  , ContactEvent
  , mkContactEvent
  , contactNone
  , contactLight
  , contactFirm
  , contactCollision
  , hasContact
  , isContactDangerous
  , isContactSafe
    -- * MovementState (how I'm moving)
  , MovementState
  , mkMovementState
  , movementStationary
  , movementWalking
  , movementRunning
  , movementFalling
  , movementCollided
  , isInMotion
  , isMovingQuickly
  , isFalling
  , wasRecentlyImpacted
  , movementSpeed
  , movementAcceleration
  , movementBalance
  ) where

import Prelude

import Hydrogen.Schema.Sensation.Proprioceptive
  ( Balance
  , Effort
  , Fatigue
  , Strain
  , balanceStable
  , effortNone
  , effortHeavy
  , effortModerate
  , fatigueNone
  , fatigueSevere
  , strainNone
  , strainHigh
  , isStable
  , isExhausted
  , unwrapBalance
  , unwrapEffort
  , unwrapFatigue
  , unwrapStrain
  )
import Hydrogen.Schema.Sensation.Contact
  ( ContactPressure
  , ContactNormal
  , Friction
  , Compliance
  , SurfaceTemperature
  , pressureNone
  , pressureLight
  , pressureHeavy
  , pressureCrushing
  , normalUp
  , frictionMedium
  , complianceFirm
  , tempNeutral
  , isPressureSafe
  , isPressureDangerous
  , unwrapContactPressure
  )
import Hydrogen.Schema.Sensation.Environment
  ( AmbientLight
  , AmbientNoise
  , Crowding
  , SpatialFreedom
  , AirQuality
  , lightModerate
  , noiseQuiet
  , noiseLoud
  , crowdingEmpty
  , crowdingDense
  , freedomModerate
  , freedomNone
  , freedomAmple
  , airGood
  , airPoor
  , isDark
  , isNoisy
  , isConstrained
  , isAirBreathable
  , unwrapAmbientLight
  , unwrapAmbientNoise
  , unwrapCrowding
  , unwrapSpatialFreedom
  )
import Hydrogen.Schema.Sensation.Force
  ( Velocity
  , Acceleration
  , ImpactIntensity
  , Buoyancy
  , velocityStationary
  , velocitySlow
  , velocityModerate
  , velocityFast
  , accelerationNone
  , impactNone
  , impactHeavy
  , buoyancyNeutral
  , buoyancySinking
  , isStationary
  , isMovingFast
  , wasSeverelyImpacted
  , unwrapVelocity
  , unwrapAcceleration
  )
import Hydrogen.Schema.Sensation.Social
  ( NearestAgentDistance
  , AgentsInView
  , AttentionOnMe
  , TrustLevel
  , ThreatLevel
  , distanceNone
  , distancePersonal
  , distanceIntimate
  , viewNone
  , viewFew
  , viewMany
  , attentionNone
  , attentionModerate
  , trustModerate
  , trustHigh
  , trustNone
  , threatNone
  , threatHigh
  , isAlone
  , isTrusted
  , isInDanger
  , unwrapTrustLevel
  , unwrapThreatLevel
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // body // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete body state — proprioceptive + contact sensation.
-- |
-- | How the agent's body feels: effort, fatigue, balance, strain.
-- | The internal physical state of the embodied agent.
type BodyState =
  { effort :: Effort
  , fatigue :: Fatigue
  , balance :: Balance
  , strain :: Strain
  }

-- | Create a body state
mkBodyState :: Effort -> Fatigue -> Balance -> Strain -> BodyState
mkBodyState effort fatigue balance strain =
  { effort, fatigue, balance, strain }

-- | Neutral body state (resting, fresh, stable)
bodyStateNeutral :: BodyState
bodyStateNeutral =
  { effort: effortNone
  , fatigue: fatigueNone
  , balance: balanceStable
  , strain: strainNone
  }

-- | Exhausted body state
bodyStateExhausted :: BodyState
bodyStateExhausted =
  { effort: effortHeavy
  , fatigue: fatigueSevere
  , balance: balanceStable
  , strain: strainHigh
  }

-- | Alert body state (ready for action)
bodyStateAlert :: BodyState
bodyStateAlert =
  { effort: effortModerate
  , fatigue: fatigueNone
  , balance: balanceStable
  , strain: strainNone
  }

-- | Is the body under stress? (high effort or fatigue or strain or exhausted)
isBodyStressed :: BodyState -> Boolean
isBodyStressed bs =
  unwrapEffort bs.effort > 0.6 ||
  unwrapFatigue bs.fatigue > 0.6 ||
  unwrapStrain bs.strain > 0.5 ||
  isExhausted bs.fatigue

-- | Is the body relaxed? (low effort, fatigue, strain and stable)
isBodyRelaxed :: BodyState -> Boolean
isBodyRelaxed bs =
  unwrapEffort bs.effort < 0.2 &&
  unwrapFatigue bs.fatigue < 0.3 &&
  unwrapStrain bs.strain < 0.2 &&
  isStable bs.balance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // environment // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete environment state — ambient + force sensation.
-- |
-- | How the environment feels: light, noise, crowding, air, freedom.
-- | The external conditions surrounding the agent.
type EnvironmentState =
  { light :: AmbientLight
  , noise :: AmbientNoise
  , crowding :: Crowding
  , freedom :: SpatialFreedom
  , airQuality :: AirQuality
  }

-- | Create an environment state
mkEnvironmentState :: AmbientLight -> AmbientNoise -> Crowding -> SpatialFreedom -> AirQuality -> EnvironmentState
mkEnvironmentState light noise crowding freedom airQuality =
  { light, noise, crowding, freedom, airQuality }

-- | Neutral environment (moderate everything)
environmentNeutral :: EnvironmentState
environmentNeutral =
  { light: lightModerate
  , noise: noiseQuiet
  , crowding: crowdingEmpty
  , freedom: freedomModerate
  , airQuality: airGood
  }

-- | Hostile environment (dark, loud, crowded, constrained)
environmentHostile :: EnvironmentState
environmentHostile =
  { light: lightModerate
  , noise: noiseLoud
  , crowding: crowdingDense
  , freedom: freedomNone
  , airQuality: airPoor
  }

-- | Comfortable environment
environmentComfortable :: EnvironmentState
environmentComfortable =
  { light: lightModerate
  , noise: noiseQuiet
  , crowding: crowdingEmpty
  , freedom: freedomAmple
  , airQuality: airGood
  }

-- | Is environment harsh? (multiple negative factors)
isEnvironmentHarsh :: EnvironmentState -> Boolean
isEnvironmentHarsh es =
  let harshFactors =
        (if isDark es.light then 1 else 0) +
        (if isNoisy es.noise then 1 else 0) +
        (if isConstrained es.freedom then 1 else 0) +
        (if not (isAirBreathable es.airQuality) then 1 else 0)
  in harshFactors >= 2

-- | Is environment pleasant? (all factors positive)
isEnvironmentPleasant :: EnvironmentState -> Boolean
isEnvironmentPleasant es =
  not (isDark es.light) &&
  not (isNoisy es.noise) &&
  not (isConstrained es.freedom) &&
  isAirBreathable es.airQuality

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // social // awareness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Social awareness — perception of other agents.
-- |
-- | Who is around, how close, do I trust them.
type SocialAwareness =
  { nearestDistance :: NearestAgentDistance
  , agentsVisible :: AgentsInView
  , attention :: AttentionOnMe
  , trust :: TrustLevel
  , threat :: ThreatLevel
  }

-- | Create a social awareness state
mkSocialAwareness :: NearestAgentDistance -> AgentsInView -> AttentionOnMe -> TrustLevel -> ThreatLevel -> SocialAwareness
mkSocialAwareness nearestDistance agentsVisible attention trust threat =
  { nearestDistance, agentsVisible, attention, trust, threat }

-- | Alone (no other agents)
socialAlone :: SocialAwareness
socialAlone =
  { nearestDistance: distanceNone
  , agentsVisible: viewNone
  , attention: attentionNone
  , trust: trustModerate
  , threat: threatNone
  }

-- | In a crowd
socialCrowd :: SocialAwareness
socialCrowd =
  { nearestDistance: distancePersonal
  , agentsVisible: viewMany
  , attention: attentionModerate
  , trust: trustModerate
  , threat: threatNone
  }

-- | With trusted companions
socialTrusted :: SocialAwareness
socialTrusted =
  { nearestDistance: distancePersonal
  , agentsVisible: viewFew
  , attention: attentionModerate
  , trust: trustHigh
  , threat: threatNone
  }

-- | Threatened by others
socialThreatened :: SocialAwareness
socialThreatened =
  { nearestDistance: distanceIntimate
  , agentsVisible: viewFew
  , attention: attentionModerate
  , trust: trustNone
  , threat: threatHigh
  }

-- | Does agent have social support? (trusted agents nearby)
hasSocialSupport :: SocialAwareness -> Boolean
hasSocialSupport sa =
  not (isAlone sa.nearestDistance) && isTrusted sa.trust

-- | Is there a social threat? (danger from others)
hasSocialThreat :: SocialAwareness -> Boolean
hasSocialThreat sa = isInDanger sa.threat

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // contact // event
-- ═════════════════════════════════════════════════════════════════════════════

-- | A single contact/touch event.
-- |
-- | What the agent is touching at a specific point.
type ContactEvent =
  { pressure :: ContactPressure
  , normal :: ContactNormal
  , friction :: Friction
  , compliance :: Compliance
  , temperature :: SurfaceTemperature
  }

-- | Create a contact event
mkContactEvent :: ContactPressure -> ContactNormal -> Friction -> Compliance -> SurfaceTemperature -> ContactEvent
mkContactEvent pressure normal friction compliance temperature =
  { pressure, normal, friction, compliance, temperature }

-- | No contact
contactNone :: ContactEvent
contactNone =
  { pressure: pressureNone
  , normal: normalUp
  , friction: frictionMedium
  , compliance: complianceFirm
  , temperature: tempNeutral
  }

-- | Light touch
contactLight :: ContactEvent
contactLight =
  { pressure: pressureLight
  , normal: normalUp
  , friction: frictionMedium
  , compliance: complianceFirm
  , temperature: tempNeutral
  }

-- | Firm contact
contactFirm :: ContactEvent
contactFirm =
  { pressure: pressureHeavy
  , normal: normalUp
  , friction: frictionMedium
  , compliance: complianceFirm
  , temperature: tempNeutral
  }

-- | Collision impact
contactCollision :: ContactEvent
contactCollision =
  { pressure: pressureCrushing
  , normal: normalUp
  , friction: frictionMedium
  , compliance: complianceFirm
  , temperature: tempNeutral
  }

-- | Is there contact? (pressure > 0)
hasContact :: ContactEvent -> Boolean
hasContact ce = unwrapContactPressure ce.pressure > 0.0

-- | Is contact dangerous? (high pressure or extreme temperature)
isContactDangerous :: ContactEvent -> Boolean
isContactDangerous ce = isPressureDangerous ce.pressure

-- | Is contact safe? (pressure within safe bounds)
isContactSafe :: ContactEvent -> Boolean
isContactSafe ce = isPressureSafe ce.pressure

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // movement // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Movement state — how the agent is currently moving.
-- |
-- | Combines velocity, acceleration, balance, and recent impacts.
type MovementState =
  { velocity :: Velocity
  , acceleration :: Acceleration
  , balance :: Balance
  , buoyancy :: Buoyancy
  , recentImpact :: ImpactIntensity
  }

-- | Create a movement state
mkMovementState :: Velocity -> Acceleration -> Balance -> Buoyancy -> ImpactIntensity -> MovementState
mkMovementState velocity acceleration balance buoyancy recentImpact =
  { velocity, acceleration, balance, buoyancy, recentImpact }

-- | Stationary (not moving)
movementStationary :: MovementState
movementStationary =
  { velocity: velocityStationary
  , acceleration: accelerationNone
  , balance: balanceStable
  , buoyancy: buoyancyNeutral
  , recentImpact: impactNone
  }

-- | Walking pace
movementWalking :: MovementState
movementWalking =
  { velocity: velocitySlow
  , acceleration: accelerationNone
  , balance: balanceStable
  , buoyancy: buoyancyNeutral
  , recentImpact: impactNone
  }

-- | Running pace
movementRunning :: MovementState
movementRunning =
  { velocity: velocityModerate
  , acceleration: accelerationNone
  , balance: balanceStable
  , buoyancy: buoyancyNeutral
  , recentImpact: impactNone
  }

-- | Falling (loss of balance, accelerating downward)
movementFalling :: MovementState
movementFalling =
  { velocity: velocityFast
  , acceleration: accelerationNone
  , balance: balanceStable  -- Will be overridden by context
  , buoyancy: buoyancySinking
  , recentImpact: impactNone
  }

-- | Just collided (stationary after heavy impact)
movementCollided :: MovementState
movementCollided =
  { velocity: velocityStationary
  , acceleration: accelerationNone
  , balance: balanceStable
  , buoyancy: buoyancyNeutral
  , recentImpact: impactHeavy
  }

-- | Is agent currently in motion? (MovementState level predicate)
isInMotion :: MovementState -> Boolean
isInMotion ms = not (isStationary ms.velocity)

-- | Is agent moving fast? (velocity above threshold)
isMovingQuickly :: MovementState -> Boolean
isMovingQuickly ms = isMovingFast ms.velocity

-- | Is agent falling? (sinking + unstable or high speed)
isFalling :: MovementState -> Boolean
isFalling ms =
  not (isStable ms.balance) || wasSeverelyImpacted ms.recentImpact

-- | Was agent recently impacted heavily?
wasRecentlyImpacted :: MovementState -> Boolean
wasRecentlyImpacted ms = wasSeverelyImpacted ms.recentImpact

-- | Get the current velocity magnitude
movementSpeed :: MovementState -> Number
movementSpeed ms = unwrapVelocity ms.velocity

-- | Get the current acceleration magnitude
movementAcceleration :: MovementState -> Number
movementAcceleration ms = unwrapAcceleration ms.acceleration

-- | Get the current balance stability (0 = unstable, 1 = stable)
movementBalance :: MovementState -> Number
movementBalance ms = unwrapBalance ms.balance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // environment // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the ambient light level (0 = dark, 1 = bright)
environmentLightLevel :: EnvironmentState -> Number
environmentLightLevel es = unwrapAmbientLight es.light

-- | Get the ambient noise level (0 = silent, 1 = deafening)
environmentNoiseLevel :: EnvironmentState -> Number
environmentNoiseLevel es = unwrapAmbientNoise es.noise

-- | Get the crowding level (0 = empty, 1 = crushed)
environmentCrowdingLevel :: EnvironmentState -> Number
environmentCrowdingLevel es = unwrapCrowding es.crowding

-- | Get the spatial freedom (0 = none, 1 = unlimited)
environmentFreedomLevel :: EnvironmentState -> Number
environmentFreedomLevel es = unwrapSpatialFreedom es.freedom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // social // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the trust level toward nearest agents (0 = none, 1 = complete)
socialTrustLevel :: SocialAwareness -> Number
socialTrustLevel sa = unwrapTrustLevel sa.trust

-- | Get the threat level from nearby agents (0 = none, 1 = critical)
socialThreatLevel :: SocialAwareness -> Number
socialThreatLevel sa = unwrapThreatLevel sa.threat

-- | Is there an imminent social threat?
hasSocialDanger :: SocialAwareness -> Boolean
hasSocialDanger sa = isInDanger sa.threat

-- | Is the agent with trusted companions?
hasTrustedCompanions :: SocialAwareness -> Boolean
hasTrustedCompanions sa = not (isAlone sa.nearestDistance) && isTrusted sa.trust

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // body // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the current effort level (0 = none, 1 = maximum)
bodyEffortLevel :: BodyState -> Number
bodyEffortLevel bs = unwrapEffort bs.effort

-- | Get the current fatigue level (0 = fresh, 1 = exhausted)
bodyFatigueLevel :: BodyState -> Number
bodyFatigueLevel bs = unwrapFatigue bs.fatigue

-- | Get the current strain level (0 = none, 1 = critical)
bodyStrainLevel :: BodyState -> Number
bodyStrainLevel bs = unwrapStrain bs.strain

-- | Get the current balance stability (0 = unstable, 1 = stable)
bodyBalanceLevel :: BodyState -> Number
bodyBalanceLevel bs = unwrapBalance bs.balance

-- | Is the body exhausted? (fatigue at exhaustion level)
isBodyExhausted :: BodyState -> Boolean
isBodyExhausted bs = isExhausted bs.fatigue
