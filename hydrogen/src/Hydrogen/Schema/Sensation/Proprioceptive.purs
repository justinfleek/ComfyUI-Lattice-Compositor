-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // sensation // proprioceptive
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Proprioceptive Atoms — Self-awareness sensation primitives.
-- |
-- | Proprioception is the sense of self-movement, body position, and effort.
-- | For embodied AI agents, these atoms model:
-- |   - Where am I? (position relative to body frame)
-- |   - What shape am I? (articulation state)
-- |   - How am I moving? (velocity, balance)
-- |   - How hard am I working? (effort, fatigue)
-- |
-- | ## SCHEMA.md Reference (Pillar 15: Sensation — Proprioceptive)
-- |
-- | | Name        | Type   | Min   | Max   | Behavior | Notes                        |
-- | |-------------|--------|-------|-------|----------|------------------------------|
-- | | JointAngle  | Number | -180  | 180   | wraps    | Articulation angle (degrees) |
-- | | Reach       | Number | 0     | none  | finite   | Volume agent can affect      |
-- | | Balance     | Number | -1    | 1     | clamps   | Stability state              |
-- | | Effort      | Number | 0     | 1     | clamps   | Current resource usage       |
-- | | Fatigue     | Number | 0     | 1     | clamps   | Accumulated effort over time |
-- | | Strain      | Number | 0     | 1     | clamps   | Structural stress level      |
-- |
-- | ## Dependencies
-- | - Prelude
-- |
-- | ## Dependents
-- | - Sensation/Molecules.purs (BodyState, MovementState)
-- | - Sensation/Compounds.purs (Disorientation, Flow)

module Hydrogen.Schema.Sensation.Proprioceptive
  ( -- * JointAngle (-180 to 180 degrees, wraps)
    JointAngle
  , mkJointAngle
  , unwrapJointAngle
  , jointAngleZero
  , jointAngle90
  , jointAngleMinus90
  , jointAngle180
  , addJointAngle
  , subtractJointAngle
    -- * Reach (0+, finite)
  , Reach
  , mkReach
  , unwrapReach
  , reachZero
  , reachNear
  , reachMedium
  , reachFar
  , scaleReach
    -- * Balance (-1 to 1, clamps)
  , Balance
  , mkBalance
  , unwrapBalance
  , balanceStable
  , balanceFalling
  , balanceOverbalanced
  , balanceTiltedLeft
  , balanceTiltedRight
  , isStable
  , isUnstable
    -- * Effort (0 to 1, clamps)
  , Effort
  , mkEffort
  , unwrapEffort
  , effortNone
  , effortLight
  , effortModerate
  , effortHeavy
  , effortMaximum
  , isResting
  , isExerting
    -- * Fatigue (0 to 1, clamps)
  , Fatigue
  , mkFatigue
  , unwrapFatigue
  , fatigueNone
  , fatigueLight
  , fatigueModerate
  , fatigueSevere
  , fatigueExhausted
  , accumulateFatigue
  , recoverFatigue
  , isFresh
  , isExhausted
    -- * Strain (0 to 1, clamps)
  , Strain
  , mkStrain
  , unwrapStrain
  , strainNone
  , strainLight
  , strainModerate
  , strainHigh
  , strainCritical
  , isOverstrained
    -- * Orientation (unit vector, normalized)
  , Orientation
  , mkOrientation
  , orientationX
  , orientationY
  , orientationZ
  , orientationForward
  , orientationUp
  , orientationRight
  , dotOrientation
  ) where

import Prelude

import Data.Int (floor, toNumber) as Int
import Data.Number (sqrt) as Num

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // joint // angle
-- ═════════════════════════════════════════════════════════════════════════════

-- | Joint articulation angle in degrees (-180 to 180, wraps).
-- |
-- | For agents with articulated bodies (robot arms, skeletal rigs),
-- | this represents the angle of a single joint. Values wrap around:
-- | 181 degrees becomes -179 degrees.
newtype JointAngle = JointAngle Number

derive instance eqJointAngle :: Eq JointAngle
derive instance ordJointAngle :: Ord JointAngle

instance showJointAngle :: Show JointAngle where
  show (JointAngle n) = "JointAngle(" <> show n <> "deg)"

-- | Wrap angle to -180..180 range
wrapAngle :: Number -> Number
wrapAngle n =
  let normalized = n - 360.0 * floor ((n + 180.0) / 360.0)
  in if normalized <= -180.0 then normalized + 360.0
     else if normalized > 180.0 then normalized - 360.0
     else normalized

-- | Create a joint angle (wraps to -180..180)
mkJointAngle :: Number -> JointAngle
mkJointAngle = JointAngle <<< wrapAngle

-- | Unwrap the joint angle
unwrapJointAngle :: JointAngle -> Number
unwrapJointAngle (JointAngle n) = n

-- | Zero angle (neutral position)
jointAngleZero :: JointAngle
jointAngleZero = JointAngle 0.0

-- | 90 degrees (right angle)
jointAngle90 :: JointAngle
jointAngle90 = JointAngle 90.0

-- | -90 degrees (opposite right angle)
jointAngleMinus90 :: JointAngle
jointAngleMinus90 = JointAngle (-90.0)

-- | 180 degrees (fully extended/folded)
jointAngle180 :: JointAngle
jointAngle180 = JointAngle 180.0

-- | Add two joint angles (result wraps)
addJointAngle :: JointAngle -> JointAngle -> JointAngle
addJointAngle (JointAngle a) (JointAngle b) = mkJointAngle (a + b)

-- | Subtract joint angles (result wraps)
subtractJointAngle :: JointAngle -> JointAngle -> JointAngle
subtractJointAngle (JointAngle a) (JointAngle b) = mkJointAngle (a - b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // reach
-- ═════════════════════════════════════════════════════════════════════════════

-- | Reach radius — the volume an agent can affect (0+, finite).
-- |
-- | For embodied agents, this represents the spatial extent of their
-- | influence: how far can they reach, touch, manipulate objects.
-- | Measured in abstract units (normalized by agent scale).
newtype Reach = Reach Number

derive instance eqReach :: Eq Reach
derive instance ordReach :: Ord Reach

instance showReach :: Show Reach where
  show (Reach n) = "Reach(" <> show n <> ")"

-- | Create a bounded reach (clamps to 0+)
mkReach :: Number -> Reach
mkReach n = Reach (max 0.0 n)

-- | Unwrap the reach value
unwrapReach :: Reach -> Number
unwrapReach (Reach n) = n

-- | Zero reach (no external influence)
reachZero :: Reach
reachZero = Reach 0.0

-- | Near reach (immediate proximity, 1.0)
reachNear :: Reach
reachNear = Reach 1.0

-- | Medium reach (arm's length, 2.0)
reachMedium :: Reach
reachMedium = Reach 2.0

-- | Far reach (extended tools, 5.0)
reachFar :: Reach
reachFar = Reach 5.0

-- | Scale reach by a factor
scaleReach :: Number -> Reach -> Reach
scaleReach factor (Reach r) = mkReach (r * max 0.0 factor)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // balance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Balance state (-1 to 1, clamps).
-- |
-- | Represents stability along a primary axis:
-- |   -1.0 = falling/tipping in negative direction
-- |    0.0 = perfectly stable
-- |   +1.0 = overbalanced in positive direction
-- |
-- | For bipedal agents, this might be left-right tilt.
-- | For general bodies, it's deviation from equilibrium.
newtype Balance = Balance Number

derive instance eqBalance :: Eq Balance
derive instance ordBalance :: Ord Balance

instance showBalance :: Show Balance where
  show (Balance n) = "Balance(" <> show n <> ")"

-- | Create a bounded balance (clamps to -1..1)
mkBalance :: Number -> Balance
mkBalance n = Balance (clamp (-1.0) 1.0 n)

-- | Unwrap the balance value
unwrapBalance :: Balance -> Number
unwrapBalance (Balance n) = n

-- | Perfectly stable (0.0)
balanceStable :: Balance
balanceStable = Balance 0.0

-- | Falling/tipping negative (-1.0)
balanceFalling :: Balance
balanceFalling = Balance (-1.0)

-- | Overbalanced positive (+1.0)
balanceOverbalanced :: Balance
balanceOverbalanced = Balance 1.0

-- | Tilted left/negative (-0.5)
balanceTiltedLeft :: Balance
balanceTiltedLeft = Balance (-0.5)

-- | Tilted right/positive (+0.5)
balanceTiltedRight :: Balance
balanceTiltedRight = Balance 0.5

-- | Is the agent stable? (within +-0.3 of equilibrium)
isStable :: Balance -> Boolean
isStable (Balance b) = b >= -0.3 && b <= 0.3

-- | Is the agent unstable? (beyond +-0.7 from equilibrium)
isUnstable :: Balance -> Boolean
isUnstable (Balance b) = b < -0.7 || b > 0.7

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // effort
-- ═════════════════════════════════════════════════════════════════════════════

-- | Effort level (0 to 1, clamps).
-- |
-- | How hard the agent is currently working — resource usage at this moment.
-- | This is instantaneous exertion, not accumulated fatigue.
-- |   0.0 = completely at rest
-- |   0.5 = moderate work
-- |   1.0 = maximum exertion
newtype Effort = Effort Number

derive instance eqEffort :: Eq Effort
derive instance ordEffort :: Ord Effort

instance showEffort :: Show Effort where
  show (Effort n) = "Effort(" <> show n <> ")"

-- | Create a bounded effort (clamps to 0..1)
mkEffort :: Number -> Effort
mkEffort n = Effort (clampNumber 0.0 1.0 n)

-- | Unwrap the effort value
unwrapEffort :: Effort -> Number
unwrapEffort (Effort n) = n

-- | No effort (at rest)
effortNone :: Effort
effortNone = Effort 0.0

-- | Light effort (0.25)
effortLight :: Effort
effortLight = Effort 0.25

-- | Moderate effort (0.5)
effortModerate :: Effort
effortModerate = Effort 0.5

-- | Heavy effort (0.75)
effortHeavy :: Effort
effortHeavy = Effort 0.75

-- | Maximum effort (1.0)
effortMaximum :: Effort
effortMaximum = Effort 1.0

-- | Is the agent resting? (effort < 0.1)
isResting :: Effort -> Boolean
isResting (Effort e) = e < 0.1

-- | Is the agent exerting significant effort? (effort > 0.6)
isExerting :: Effort -> Boolean
isExerting (Effort e) = e > 0.6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // fatigue
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fatigue level (0 to 1, clamps).
-- |
-- | Accumulated effort over time — the integral of exertion.
-- | Unlike Effort (instantaneous), Fatigue builds up and requires
-- | recovery time to reduce.
-- |   0.0 = completely fresh
-- |   0.5 = moderately tired
-- |   1.0 = exhausted (recovery required)
newtype Fatigue = Fatigue Number

derive instance eqFatigue :: Eq Fatigue
derive instance ordFatigue :: Ord Fatigue

instance showFatigue :: Show Fatigue where
  show (Fatigue n) = "Fatigue(" <> show n <> ")"

-- | Create a bounded fatigue (clamps to 0..1)
mkFatigue :: Number -> Fatigue
mkFatigue n = Fatigue (clampNumber 0.0 1.0 n)

-- | Unwrap the fatigue value
unwrapFatigue :: Fatigue -> Number
unwrapFatigue (Fatigue n) = n

-- | No fatigue (completely fresh)
fatigueNone :: Fatigue
fatigueNone = Fatigue 0.0

-- | Light fatigue (0.25)
fatigueLight :: Fatigue
fatigueLight = Fatigue 0.25

-- | Moderate fatigue (0.5)
fatigueModerate :: Fatigue
fatigueModerate = Fatigue 0.5

-- | Severe fatigue (0.75)
fatigueSevere :: Fatigue
fatigueSevere = Fatigue 0.75

-- | Exhausted (1.0)
fatigueExhausted :: Fatigue
fatigueExhausted = Fatigue 1.0

-- | Accumulate fatigue from effort over a time delta
-- | fatigue' = min 1.0 (fatigue + effort * delta * rate)
accumulateFatigue :: Number -> Number -> Fatigue -> Effort -> Fatigue
accumulateFatigue delta rate (Fatigue f) (Effort e) =
  mkFatigue (f + e * delta * rate)

-- | Recover fatigue over a time delta
-- | fatigue' = max 0.0 (fatigue - delta * recoveryRate)
recoverFatigue :: Number -> Number -> Fatigue -> Fatigue
recoverFatigue delta recoveryRate (Fatigue f) =
  mkFatigue (f - delta * recoveryRate)

-- | Is the agent fresh? (fatigue < 0.2)
isFresh :: Fatigue -> Boolean
isFresh (Fatigue f) = f < 0.2

-- | Is the agent exhausted? (fatigue > 0.8)
isExhausted :: Fatigue -> Boolean
isExhausted (Fatigue f) = f > 0.8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // strain
-- ═════════════════════════════════════════════════════════════════════════════

-- | Structural strain level (0 to 1, clamps).
-- |
-- | How much stress the agent's body/structure is under.
-- | Unlike fatigue (which accumulates from effort), strain is from
-- | external forces or awkward configurations.
-- |   0.0 = no structural stress
-- |   0.5 = moderate strain
-- |   1.0 = critical strain (damage imminent)
newtype Strain = Strain Number

derive instance eqStrain :: Eq Strain
derive instance ordStrain :: Ord Strain

instance showStrain :: Show Strain where
  show (Strain n) = "Strain(" <> show n <> ")"

-- | Create a bounded strain (clamps to 0..1)
mkStrain :: Number -> Strain
mkStrain n = Strain (clampNumber 0.0 1.0 n)

-- | Unwrap the strain value
unwrapStrain :: Strain -> Number
unwrapStrain (Strain n) = n

-- | No strain
strainNone :: Strain
strainNone = Strain 0.0

-- | Light strain (0.25)
strainLight :: Strain
strainLight = Strain 0.25

-- | Moderate strain (0.5)
strainModerate :: Strain
strainModerate = Strain 0.5

-- | High strain (0.75)
strainHigh :: Strain
strainHigh = Strain 0.75

-- | Critical strain (1.0)
strainCritical :: Strain
strainCritical = Strain 1.0

-- | Is the agent overstrained? (strain > 0.7)
isOverstrained :: Strain -> Boolean
isOverstrained (Strain s) = s > 0.7

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Orientation as a unit vector (normalized).
-- |
-- | Which direction the agent is facing/pointing.
-- | Represented as (x, y, z) components of a unit vector.
type Orientation =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Create an orientation (automatically normalizes)
mkOrientation :: Number -> Number -> Number -> Orientation
mkOrientation x y z =
  let mag = Num.sqrt (x * x + y * y + z * z)
      safeMag = if mag < 0.0001 then 1.0 else mag
  in { x: x / safeMag, y: y / safeMag, z: z / safeMag }

-- | Get X component
orientationX :: Orientation -> Number
orientationX o = o.x

-- | Get Y component
orientationY :: Orientation -> Number
orientationY o = o.y

-- | Get Z component
orientationZ :: Orientation -> Number
orientationZ o = o.z

-- | Forward orientation (positive Z)
orientationForward :: Orientation
orientationForward = { x: 0.0, y: 0.0, z: 1.0 }

-- | Up orientation (positive Y)
orientationUp :: Orientation
orientationUp = { x: 0.0, y: 1.0, z: 0.0 }

-- | Right orientation (positive X)
orientationRight :: Orientation
orientationRight = { x: 1.0, y: 0.0, z: 0.0 }

-- | Dot product of two orientations (cosine of angle between them)
dotOrientation :: Orientation -> Orientation -> Number
dotOrientation a b = a.x * b.x + a.y * b.y + a.z * b.z

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to a range.
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)

-- | Floor function
floor :: Number -> Number
floor n = Int.toNumber (Int.floor n)
