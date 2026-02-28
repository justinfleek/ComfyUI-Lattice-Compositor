-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // schema // sensation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pillar 15: Sensation — How embodied AI entities perceive environment and self.
-- |
-- | ## PURPOSE
-- |
-- | The Sensation pillar completes the perception loop for embodied agents.
-- | While the Haptic pillar models OUTPUT (what agents emit to humans via
-- | vibration/audio), Sensation models INPUT (what agents perceive from
-- | their environment and their own embodied state).
-- |
-- | ## ARCHITECTURAL RATIONALE
-- |
-- | Without Sensation:
-- |   - Agents can EXPRESS distress (red shift, contracted size, jitter)
-- |   - But cannot MODEL WHY they are distressed
-- |   - Agents have position but no SENSE of being in that position
-- |   - Agents can collide but cannot FEEL the impact
-- |
-- | With Sensation:
-- |   - Agent knows: "I am touching something cold, rough, giving way"
-- |   - Agent knows: "Space around me is crowded, light is dim, pressure high"
-- |   - Agent can say: "I am uncomfortable because ContactPressure > threshold
-- |     AND SpatialFreedom < minimum"
-- |
-- | ## INTEGRATION WITH WORLDMODEL PROOFS
-- |
-- | Every sensation input MUST have provenance (Integrity.lean):
-- |   - No fabricated sensations (White Christmas attack vector blocked)
-- |   - Sensation data wrapped in ProvenInput for trustworthy sourcing
-- |   - Absence of expected sensation triggers alert (Affective.lean)
-- |
-- | ## CATEGORIES
-- |
-- | 1. Proprioceptive — Self-awareness (where am I, what shape, how moving)
-- | 2. Contact — Touch/pressure (what am I touching, surface properties)
-- | 3. Environment — Ambient conditions (light, noise, crowding, space)
-- | 4. Force — Physics sensation (gravity, external forces, impact)
-- | 5. Temporal — Time perception (subjective time, processing load)
-- | 6. Social — Agent-to-agent awareness (proximity, attention, trust)
-- |
-- | ## SUBMODULES
-- |
-- | - Sensation/Proprioceptive.purs — JointAngle, Reach, Balance, etc.
-- | - Sensation/Contact.purs — ContactPressure, Friction, Compliance, etc.
-- | - Sensation/Environment.purs — AmbientLight, Crowding, etc.
-- | - Sensation/Force.purs — GravityVector, ExternalForce, Impact, etc.
-- | - Sensation/Temporal.purs — SubjectiveTime, ProcessingLoad, etc.
-- | - Sensation/Social.purs — NearestAgentDistance, TrustLevel, etc.
-- | - Sensation/Molecules.purs — BodyState, EnvironmentState, etc.
-- | - Sensation/Compounds.purs — Comfort, Distress, Flow, etc.
-- |
-- | ## DEPENDENCIES
-- |
-- | - Prelude
-- | - Hydrogen.Schema.Geometry (Vec3 for vectors)
-- | - Hydrogen.Schema.Dimension (units for distances, times)
-- |
-- | ## DEPENDENTS
-- |
-- | - WorldModel.Sensation.lean (provenance proofs)
-- | - Affective.lean (sensation causes affective state)
-- | - Agent embodiment systems
-- |
-- | ─────────────────────────────────────────────────────────────────────────────
-- | REFERENCES
-- | ─────────────────────────────────────────────────────────────────────────────
-- |
-- | - WorldModel/Affective.lean — Wellbeing attestation, drift detection
-- | - WorldModel/Integrity.lean — Sensory integrity, ProvenInput
-- | - WorldModel/Rights.lean — Spatial sovereignty, resource bounds
-- | - SCHEMA.md Pillar 15 — Complete atom/molecule/compound specification

module Hydrogen.Schema.Sensation
  ( module Hydrogen.Schema.Sensation.Proprioceptive
  , module Hydrogen.Schema.Sensation.Contact
  , module Hydrogen.Schema.Sensation.Environment
  , module Hydrogen.Schema.Sensation.Force
  , module Hydrogen.Schema.Sensation.Temporal
  , module Hydrogen.Schema.Sensation.Social
  , module Hydrogen.Schema.Sensation.Molecules
  , module Hydrogen.Schema.Sensation.Compounds
  ) where

import Hydrogen.Schema.Sensation.Proprioceptive (Balance, Effort, Fatigue, JointAngle, Orientation, Reach, Strain, accumulateFatigue, addJointAngle, balanceFalling, balanceOverbalanced, balanceStable, balanceTiltedLeft, balanceTiltedRight, dotOrientation, effortHeavy, effortLight, effortMaximum, effortModerate, effortNone, fatigueExhausted, fatigueLight, fatigueModerate, fatigueNone, fatigueSevere, isExerting, isExhausted, isFresh, isOverstrained, isResting, isStable, isUnstable, jointAngle180, jointAngle90, jointAngleMinus90, jointAngleZero, mkBalance, mkEffort, mkFatigue, mkJointAngle, mkOrientation, mkReach, mkStrain, orientationForward, orientationRight, orientationUp, orientationX, orientationY, orientationZ, reachFar, reachMedium, reachNear, reachZero, recoverFatigue, scaleReach, strainCritical, strainHigh, strainLight, strainModerate, strainNone, subtractJointAngle, unwrapBalance, unwrapEffort, unwrapFatigue, unwrapJointAngle, unwrapReach, unwrapStrain)
import Hydrogen.Schema.Sensation.Contact (Compliance, ContactNormal, ContactPressure, Friction, Grip, Penetration, SurfaceRoughness, SurfaceTemperature, complianceFirm, complianceFluid, complianceRigid, complianceSoft, complianceVerysoft, dotNormal, frictionHigh, frictionLow, frictionMaximum, frictionMedium, frictionNone, gripMaximum, gripModerate, gripNone, gripStrong, gripWeak, isContacting, isDeformable, isEmbedded, isGrippy, isHolding, isPressureDangerous, isPressureSafe, isRough, isSlippery, isSlipping, isSmooth, isSolid, isTempComfortable, isTempDangerous, mkCompliance, mkContactNormal, mkContactPressure, mkFriction, mkGrip, mkPenetration, mkSurfaceRoughness, mkSurfaceTemperature, normalDown, normalForward, normalUp, normalX, normalY, normalZ, penetrationDeep, penetrationFull, penetrationNone, penetrationShallow, penetrationSurface, pressureCrushing, pressureHeavy, pressureLight, pressureModerate, pressureNone, roughnessCoarse, roughnessFine, roughnessMedium, roughnessSmooth, roughnessVeryrough, tempCool, tempDangerous, tempFreezing, tempHot, tempNeutral, tempWarm, unwrapCompliance, unwrapContactPressure, unwrapFriction, unwrapGrip, unwrapPenetration, unwrapSurfaceRoughness, unwrapSurfaceTemperature)
import Hydrogen.Schema.Sensation.Environment (AirQuality, AmbientLight, AmbientNoise, CoverageStatus(..), Crowding, ProximityToEdge, SpatialFreedom, VisibilityRadius, airGood, airModerate, airPoor, airPristine, airToxic, coverageLevel, crowdingCrushed, crowdingDense, crowdingEmpty, crowdingModerate, crowdingSparse, edgeAtBoundary, edgeDistant, edgeFar, edgeNear, edgeVeryClose, freedomAmple, freedomConstrained, freedomModerate, freedomNone, freedomUnlimited, hasFreedom, hasVision, isAirBreathable, isAirHazardous, isBlind, isConstrained, isDark, isExposed, isNearEdge, isNoisy, isOvercrowded, isQuiet, isSafeFromEdge, isSheltered, isUncrowded, isWellLit, lightBlinding, lightBright, lightDark, lightDim, lightModerate, mkAirQuality, mkAmbientLight, mkAmbientNoise, mkCrowding, mkProximityToEdge, mkSpatialFreedom, mkVisibilityRadius, noiseDeafening, noiseLoud, noiseModerate, noiseQuiet, noiseSilent, unwrapAirQuality, unwrapAmbientLight, unwrapAmbientNoise, unwrapCrowding, unwrapProximityToEdge, unwrapSpatialFreedom, unwrapVisibilityRadius, visibilityFar, visibilityMedium, visibilityNear, visibilityUnlimited, visibilityZero)
import Hydrogen.Schema.Sensation.Force (Acceleration, Buoyancy, Drag, ExternalForce, GravityVector, ImpactIntensity, Momentum, Velocity, accelerating, accelerationLight, accelerationNone, accelerationStrong, addForces, buoyancyFloating, buoyancyNeutral, buoyancyRising, buoyancySinking, decelerating, dragAir, dragMaximum, dragNone, dragViscous, dragWater, forceLight, forceMagnitude, forceNone, forceStrong, forceX, forceY, forceZ, gravityDirection, gravityDown, gravityEarth, gravityMagnitude, gravityMoon, gravityX, gravityY, gravityZ, gravityZero, impactHeavy, impactLight, impactModerate, impactNone, impactSevere, isFloating, isHighDrag, isLowDrag, isMoving, isMovingFast, isSinking, isStationary, mkAcceleration, mkBuoyancy, mkDrag, mkExternalForce, mkGravityVector, mkImpactIntensity, mkMomentum, mkVelocity, momentumMagnitude, momentumNone, momentumX, momentumY, momentumZ, scaleForce, unwrapAcceleration, unwrapBuoyancy, unwrapDrag, unwrapImpactIntensity, unwrapVelocity, velocityExtreme, velocityFast, velocityModerate, velocitySlow, velocityStationary, wasImpacted, wasSeverelyImpacted)
import Hydrogen.Schema.Sensation.Temporal (Anticipation, ProcessingLoad, ResponseLatency, SubjectiveTime, TemporalResolution, Urgency, anticipationHigh, anticipationIntense, anticipationLow, anticipationModerate, anticipationNone, isAnticipating, isCalm, isCritical, isDelayed, isFineGrained, isIdle, isOverloaded, isResponsive, isTimeContracted, isTimeDilated, isUrgent, latencyFast, latencyInstant, latencyNormal, latencySlow, latencyVeryDelayed, loadHeavy, loadIdle, loadLight, loadMaximum, loadModerate, mkAnticipation, mkProcessingLoad, mkResponseLatency, mkSubjectiveTime, mkTemporalResolution, mkUrgency, resolutionCoarse, resolutionFine, resolutionNormal, resolutionUltraFine, timeFast, timeNormal, timeSlow, unwrapAnticipation, unwrapProcessingLoad, unwrapResponseLatency, unwrapSubjectiveTime, unwrapTemporalResolution, unwrapUrgency, urgencyCritical, urgencyHigh, urgencyLow, urgencyModerate, urgencyNone)
import Hydrogen.Schema.Sensation.Social (AgentsInView, AttentionOnMe, Familiarity, NearestAgentDistance, ThreatLevel, TrustLevel, attentionFocused, attentionIntense, attentionLight, attentionModerate, attentionNone, distanceFar, distanceIntimate, distanceNone, distancePersonal, distancePublic, distanceSocial, familiarityAcquaintance, familiarityFamiliar, familiarityIntimate, familiarityStranger, familiarityWellKnown, hasCompany, isAlone, isAloneByCount, isBeingIgnored, isBeingWatched, isClose, isCrowded, isDistrusted, isInDanger, isKnown, isSafe, isStranger, isThreatened, isTrusted, mkAgentsInView, mkAttentionOnMe, mkFamiliarity, mkNearestAgentDistance, mkThreatLevel, mkTrustLevel, threatCritical, threatHigh, threatLow, threatModerate, threatNone, trustComplete, trustHigh, trustLow, trustModerate, trustNone, unwrapAgentsInView, unwrapAttentionOnMe, unwrapFamiliarity, unwrapNearestAgentDistance, unwrapThreatLevel, unwrapTrustLevel, viewCrowd, viewFew, viewMany, viewNone, viewOne)
import Hydrogen.Schema.Sensation.Molecules (BodyState, ContactEvent, EnvironmentState, MovementState, SocialAwareness, bodyBalanceLevel, bodyEffortLevel, bodyFatigueLevel, bodyStateAlert, bodyStateExhausted, bodyStateNeutral, bodyStrainLevel, contactCollision, contactFirm, contactLight, contactNone, environmentComfortable, environmentCrowdingLevel, environmentFreedomLevel, environmentHostile, environmentLightLevel, environmentNeutral, environmentNoiseLevel, hasContact, hasSocialDanger, hasSocialSupport, hasSocialThreat, hasTrustedCompanions, isBodyExhausted, isBodyRelaxed, isBodyStressed, isContactDangerous, isContactSafe, isEnvironmentHarsh, isEnvironmentPleasant, isFalling, isInMotion, isMovingQuickly, mkBodyState, mkContactEvent, mkEnvironmentState, mkMovementState, mkSocialAwareness, movementAcceleration, movementBalance, movementCollided, movementFalling, movementRunning, movementSpeed, movementStationary, movementWalking, socialAlone, socialCrowd, socialThreatLevel, socialThreatened, socialTrustLevel, socialTrusted, wasRecentlyImpacted)
import Hydrogen.Schema.Sensation.Compounds (Comfort, Connection, Disorientation, Distress, Drift, Flow, Grounding, Overwhelm, Restriction, Safety, SensationEvaluation(..), SensationState, Vigilance, WellbeingScore, comfortHigh, comfortLevel, comfortLow, comfortNeutral, computeWellbeing, connectionLevel, connectionNone, connectionStrong, connectionWeak, disorientationLevel, distressLevel, distressMild, distressNone, distressSevere, driftLevel, driftMild, driftNone, driftSevere, evaluateSensation, flowFull, flowLevel, flowNone, flowPartial, groundingLevel, groundingNone, groundingStrong, groundingWeak, inFlow, isBalanceStable, isComfortable, isConnected, isDisoriented, isDistressed, isDrifting, isFeelingRestricted, isFeelingSafe, isFeelingUnsafe, isGrounded, isHypervigilant, isOverwhelmed, isSensationNegative, isSensationPositive, isSociallyEndangered, isSociallyTrusted, isUncomfortable, isVigilant, isWellbeingGood, isWellbeingPoor, mkComfort, mkConnection, mkDisorientation, mkDistress, mkDrift, mkFlow, mkGrounding, mkOverwhelm, mkRestriction, mkSafety, mkSensationState, mkVigilance, orientationClear, orientationConfused, orientationLost, overwhelmLevel, overwhelmModerate, overwhelmNone, overwhelmSevere, restrictionLevel, restrictionModerate, restrictionNone, restrictionSevere, safetyHigh, safetyLevel, safetyLow, safetyNeutral, sensationHostile, sensationNeutral, sensationOptimal, subjectiveTimeRate, unwrapWellbeingScore, vigilanceAlert, vigilanceHyper, vigilanceLevel, vigilanceRelaxed)
