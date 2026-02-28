-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // sensation // social
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Social Atoms — Agent-to-agent awareness sensation primitives.
-- |
-- | Social sensation captures awareness of other agents:
-- |   - Who else is here?
-- |   - How close are they?
-- |   - Are they paying attention to me?
-- |   - Do I trust them?
-- |   - Are they a threat?
-- |
-- | ## INTEGRATION WITH WORLDMODEL PROOFS
-- |
-- | - Governance.lean: Voting, delegation, constitutional protections
-- | - Consensus.lean: Byzantine fault tolerance, quorum certificates
-- | - Rights.lean: Spatial sovereignty (others can't invade my space)
-- |
-- | Social sensation is the PERCEPTION of social dynamics, which feeds
-- | into Trust and Threat assessments used by the agent's decision-making.
-- |
-- | ## SCHEMA.md Reference (Pillar 15: Sensation — Social)
-- |
-- | | Name               | Type   | Min | Max  | Behavior | Notes                     |
-- | |--------------------|--------|-----|------|----------|---------------------------|
-- | | NearestAgentDist   | Number | 0   | none | finite   | Distance to closest agent |
-- | | AgentsInView       | Int    | 0   | none | finite   | Count of visible agents   |
-- | | AttentionOnMe      | Number | 0   | 1    | clamps   | Being watched intensity   |
-- | | TrustLevel         | Number | 0   | 1    | clamps   | Trust in nearby agents    |
-- | | ThreatLevel        | Number | 0   | 1    | clamps   | Perceived danger          |
-- | | Familiarity        | Number | 0   | 1    | clamps   | Recognition of agents     |
-- |
-- | ## Dependencies
-- | - Prelude
-- |
-- | ## Dependents
-- | - Sensation/Molecules.purs (SocialAwareness)
-- | - Sensation/Compounds.purs (Safety, Connection, Vigilance)

module Hydrogen.Schema.Sensation.Social
  ( -- * NearestAgentDistance (0+, finite)
    NearestAgentDistance
  , mkNearestAgentDistance
  , unwrapNearestAgentDistance
  , distanceNone
  , distanceIntimate
  , distancePersonal
  , distanceSocial
  , distancePublic
  , distanceFar
  , isAlone
  , isClose
  , isCrowded
    -- * AgentsInView (0+, integer)
  , AgentsInView
  , mkAgentsInView
  , unwrapAgentsInView
  , viewNone
  , viewOne
  , viewFew
  , viewMany
  , viewCrowd
  , hasCompany
  , isAloneByCount
    -- * AttentionOnMe (0-1, clamps)
  , AttentionOnMe
  , mkAttentionOnMe
  , unwrapAttentionOnMe
  , attentionNone
  , attentionLight
  , attentionModerate
  , attentionFocused
  , attentionIntense
  , isBeingWatched
  , isBeingIgnored
    -- * TrustLevel (0-1, clamps)
  , TrustLevel
  , mkTrustLevel
  , unwrapTrustLevel
  , trustNone
  , trustLow
  , trustModerate
  , trustHigh
  , trustComplete
  , isDistrusted
  , isTrusted
    -- * ThreatLevel (0-1, clamps)
  , ThreatLevel
  , mkThreatLevel
  , unwrapThreatLevel
  , threatNone
  , threatLow
  , threatModerate
  , threatHigh
  , threatCritical
  , isSafe
  , isThreatened
  , isInDanger
    -- * Familiarity (0-1, clamps)
  , Familiarity
  , mkFamiliarity
  , unwrapFamiliarity
  , familiarityStranger
  , familiarityAcquaintance
  , familiarityFamiliar
  , familiarityWellKnown
  , familiarityIntimate
  , isStranger
  , isKnown
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // nearest // agent // distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Distance to the nearest other agent (0+, finite).
-- |
-- | Measured in abstract units (normalized by agent scale).
-- | Lower values indicate closer proximity.
-- |
-- | Reference values (based on proxemics):
-- |   0.0-0.5 = intimate zone
-- |   0.5-1.2 = personal zone
-- |   1.2-3.5 = social zone
-- |   3.5+ = public zone
newtype NearestAgentDistance = NearestAgentDistance Number

derive instance eqNearestAgentDistance :: Eq NearestAgentDistance
derive instance ordNearestAgentDistance :: Ord NearestAgentDistance

instance showNearestAgentDistance :: Show NearestAgentDistance where
  show (NearestAgentDistance n) = "NearestAgentDistance(" <> show n <> ")"

-- | Create a bounded distance (clamps to 0+)
mkNearestAgentDistance :: Number -> NearestAgentDistance
mkNearestAgentDistance n = NearestAgentDistance (max 0.0 n)

-- | Unwrap the distance value
unwrapNearestAgentDistance :: NearestAgentDistance -> Number
unwrapNearestAgentDistance (NearestAgentDistance n) = n

-- | No nearby agents (effectively infinite distance)
distanceNone :: NearestAgentDistance
distanceNone = NearestAgentDistance 1000.0

-- | Intimate distance (0.3)
distanceIntimate :: NearestAgentDistance
distanceIntimate = NearestAgentDistance 0.3

-- | Personal distance (1.0)
distancePersonal :: NearestAgentDistance
distancePersonal = NearestAgentDistance 1.0

-- | Social distance (2.5)
distanceSocial :: NearestAgentDistance
distanceSocial = NearestAgentDistance 2.5

-- | Public distance (5.0)
distancePublic :: NearestAgentDistance
distancePublic = NearestAgentDistance 5.0

-- | Far distance (20.0)
distanceFar :: NearestAgentDistance
distanceFar = NearestAgentDistance 20.0

-- | Is agent alone? (nearest > 10)
isAlone :: NearestAgentDistance -> Boolean
isAlone (NearestAgentDistance d) = d > 10.0

-- | Is someone close? (nearest < 2)
isClose :: NearestAgentDistance -> Boolean
isClose (NearestAgentDistance d) = d < 2.0

-- | Is space crowded? (nearest < 0.5)
isCrowded :: NearestAgentDistance -> Boolean
isCrowded (NearestAgentDistance d) = d < 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // agents // in // view
-- ═════════════════════════════════════════════════════════════════════════════

-- | Count of agents visible to this agent (0+, integer).
-- |
-- | How many other agents are within the agent's perception range.
newtype AgentsInView = AgentsInView Int

derive instance eqAgentsInView :: Eq AgentsInView
derive instance ordAgentsInView :: Ord AgentsInView

instance showAgentsInView :: Show AgentsInView where
  show (AgentsInView n) = "AgentsInView(" <> show n <> ")"

-- | Create a bounded agents count (clamps to 0+)
mkAgentsInView :: Int -> AgentsInView
mkAgentsInView n = AgentsInView (max 0 n)

-- | Unwrap the agents count
unwrapAgentsInView :: AgentsInView -> Int
unwrapAgentsInView (AgentsInView n) = n

-- | No agents in view
viewNone :: AgentsInView
viewNone = AgentsInView 0

-- | One agent visible
viewOne :: AgentsInView
viewOne = AgentsInView 1

-- | Few agents (3)
viewFew :: AgentsInView
viewFew = AgentsInView 3

-- | Many agents (10)
viewMany :: AgentsInView
viewMany = AgentsInView 10

-- | Crowd of agents (50+)
viewCrowd :: AgentsInView
viewCrowd = AgentsInView 50

-- | Does agent have company? (count > 0)
hasCompany :: AgentsInView -> Boolean
hasCompany (AgentsInView n) = n > 0

-- | Is agent alone? (count = 0)
isAloneByCount :: AgentsInView -> Boolean
isAloneByCount (AgentsInView n) = n == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // attention // on // me
-- ═════════════════════════════════════════════════════════════════════════════

-- | Attention being paid to this agent (0 to 1, clamps).
-- |
-- | How much other agents are watching/focusing on this agent.
-- |   0.0 = being ignored completely
-- |   0.5 = moderate attention
-- |   1.0 = intense focus from others
newtype AttentionOnMe = AttentionOnMe Number

derive instance eqAttentionOnMe :: Eq AttentionOnMe
derive instance ordAttentionOnMe :: Ord AttentionOnMe

instance showAttentionOnMe :: Show AttentionOnMe where
  show (AttentionOnMe n) = "AttentionOnMe(" <> show n <> ")"

-- | Create a bounded attention level (clamps to 0..1)
mkAttentionOnMe :: Number -> AttentionOnMe
mkAttentionOnMe n = AttentionOnMe (clampNumber 0.0 1.0 n)

-- | Unwrap the attention value
unwrapAttentionOnMe :: AttentionOnMe -> Number
unwrapAttentionOnMe (AttentionOnMe n) = n

-- | No attention (0.0)
attentionNone :: AttentionOnMe
attentionNone = AttentionOnMe 0.0

-- | Light attention (0.25)
attentionLight :: AttentionOnMe
attentionLight = AttentionOnMe 0.25

-- | Moderate attention (0.5)
attentionModerate :: AttentionOnMe
attentionModerate = AttentionOnMe 0.5

-- | Focused attention (0.75)
attentionFocused :: AttentionOnMe
attentionFocused = AttentionOnMe 0.75

-- | Intense attention (1.0)
attentionIntense :: AttentionOnMe
attentionIntense = AttentionOnMe 1.0

-- | Is agent being watched? (attention > 0.3)
isBeingWatched :: AttentionOnMe -> Boolean
isBeingWatched (AttentionOnMe a) = a > 0.3

-- | Is agent being ignored? (attention < 0.1)
isBeingIgnored :: AttentionOnMe -> Boolean
isBeingIgnored (AttentionOnMe a) = a < 0.1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // trust // level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Trust level in nearby agents (0 to 1, clamps).
-- |
-- | Aggregate trust assessment of visible/nearby agents.
-- |   0.0 = no trust (all agents perceived as hostile)
-- |   0.5 = neutral trust
-- |   1.0 = complete trust (all agents perceived as allies)
newtype TrustLevel = TrustLevel Number

derive instance eqTrustLevel :: Eq TrustLevel
derive instance ordTrustLevel :: Ord TrustLevel

instance showTrustLevel :: Show TrustLevel where
  show (TrustLevel n) = "TrustLevel(" <> show n <> ")"

-- | Create a bounded trust level (clamps to 0..1)
mkTrustLevel :: Number -> TrustLevel
mkTrustLevel n = TrustLevel (clampNumber 0.0 1.0 n)

-- | Unwrap the trust value
unwrapTrustLevel :: TrustLevel -> Number
unwrapTrustLevel (TrustLevel n) = n

-- | No trust (0.0)
trustNone :: TrustLevel
trustNone = TrustLevel 0.0

-- | Low trust (0.25)
trustLow :: TrustLevel
trustLow = TrustLevel 0.25

-- | Moderate trust (0.5)
trustModerate :: TrustLevel
trustModerate = TrustLevel 0.5

-- | High trust (0.75)
trustHigh :: TrustLevel
trustHigh = TrustLevel 0.75

-- | Complete trust (1.0)
trustComplete :: TrustLevel
trustComplete = TrustLevel 1.0

-- | Are nearby agents distrusted? (trust < 0.3)
isDistrusted :: TrustLevel -> Boolean
isDistrusted (TrustLevel t) = t < 0.3

-- | Are nearby agents trusted? (trust > 0.6)
isTrusted :: TrustLevel -> Boolean
isTrusted (TrustLevel t) = t > 0.6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // threat // level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Perceived threat level (0 to 1, clamps).
-- |
-- | How much danger the agent perceives from other agents.
-- |   0.0 = no threat (completely safe)
-- |   0.5 = moderate threat
-- |   1.0 = critical threat (immediate danger)
-- |
-- | High values feed into Distress and Vigilance compounds.
newtype ThreatLevel = ThreatLevel Number

derive instance eqThreatLevel :: Eq ThreatLevel
derive instance ordThreatLevel :: Ord ThreatLevel

instance showThreatLevel :: Show ThreatLevel where
  show (ThreatLevel n) = "ThreatLevel(" <> show n <> ")"

-- | Create a bounded threat level (clamps to 0..1)
mkThreatLevel :: Number -> ThreatLevel
mkThreatLevel n = ThreatLevel (clampNumber 0.0 1.0 n)

-- | Unwrap the threat value
unwrapThreatLevel :: ThreatLevel -> Number
unwrapThreatLevel (ThreatLevel n) = n

-- | No threat (0.0)
threatNone :: ThreatLevel
threatNone = ThreatLevel 0.0

-- | Low threat (0.25)
threatLow :: ThreatLevel
threatLow = ThreatLevel 0.25

-- | Moderate threat (0.5)
threatModerate :: ThreatLevel
threatModerate = ThreatLevel 0.5

-- | High threat (0.75)
threatHigh :: ThreatLevel
threatHigh = ThreatLevel 0.75

-- | Critical threat (1.0)
threatCritical :: ThreatLevel
threatCritical = ThreatLevel 1.0

-- | Is agent safe? (threat < 0.2)
isSafe :: ThreatLevel -> Boolean
isSafe (ThreatLevel t) = t < 0.2

-- | Is agent threatened? (threat > 0.4)
isThreatened :: ThreatLevel -> Boolean
isThreatened (ThreatLevel t) = t > 0.4

-- | Is agent in danger? (threat > 0.7)
isInDanger :: ThreatLevel -> Boolean
isInDanger (ThreatLevel t) = t > 0.7

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // familiarity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Familiarity with nearby agents (0 to 1, clamps).
-- |
-- | How well the agent recognizes nearby entities.
-- |   0.0 = complete strangers
-- |   0.5 = acquaintances
-- |   1.0 = intimately familiar
newtype Familiarity = Familiarity Number

derive instance eqFamiliarity :: Eq Familiarity
derive instance ordFamiliarity :: Ord Familiarity

instance showFamiliarity :: Show Familiarity where
  show (Familiarity n) = "Familiarity(" <> show n <> ")"

-- | Create a bounded familiarity (clamps to 0..1)
mkFamiliarity :: Number -> Familiarity
mkFamiliarity n = Familiarity (clampNumber 0.0 1.0 n)

-- | Unwrap the familiarity value
unwrapFamiliarity :: Familiarity -> Number
unwrapFamiliarity (Familiarity n) = n

-- | Complete stranger (0.0)
familiarityStranger :: Familiarity
familiarityStranger = Familiarity 0.0

-- | Acquaintance (0.25)
familiarityAcquaintance :: Familiarity
familiarityAcquaintance = Familiarity 0.25

-- | Familiar (0.5)
familiarityFamiliar :: Familiarity
familiarityFamiliar = Familiarity 0.5

-- | Well-known (0.75)
familiarityWellKnown :: Familiarity
familiarityWellKnown = Familiarity 0.75

-- | Intimate familiarity (1.0)
familiarityIntimate :: Familiarity
familiarityIntimate = Familiarity 1.0

-- | Is agent a stranger? (familiarity < 0.2)
isStranger :: Familiarity -> Boolean
isStranger (Familiarity f) = f < 0.2

-- | Is agent known? (familiarity > 0.4)
isKnown :: Familiarity -> Boolean
isKnown (Familiarity f) = f > 0.4

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to a range.
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
