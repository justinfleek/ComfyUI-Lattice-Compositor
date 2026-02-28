-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // sensation // environment
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Environment Atoms — Ambient condition sensation primitives.
-- |
-- | Environmental sensation captures ambient conditions around the agent:
-- |   - How bright is it here?
-- |   - How noisy is the background?
-- |   - How crowded is the space?
-- |   - How much room do I have to move?
-- |
-- | ## SCHEMA.md Reference (Pillar 15: Sensation — Environment)
-- |
-- | | Name            | Type   | Min | Max  | Behavior | Notes                       |
-- | |-----------------|--------|-----|------|----------|-----------------------------|
-- | | AmbientLight    | Number | 0   | 1    | clamps   | Brightness (0=dark, 1=bright)|
-- | | AmbientNoise    | Number | 0   | 1    | clamps   | Background audio level      |
-- | | Crowding        | Number | 0   | 1    | clamps   | Density of nearby agents    |
-- | | ProximityToEdge | Number | 0   | 1    | clamps   | Distance to world boundary  |
-- | | SpatialFreedom  | Number | 0   | 1    | clamps   | Room to move                |
-- | | VisibilityRadius| Number | 0   | none | finite   | How far can I see           |
-- | | CoverageStatus  | Enum   | -   | -    | -        | Exposed/Partial/Sheltered   |
-- | | AirQuality      | Number | 0   | 1    | clamps   | Breathability (metaphorical)|
-- |
-- | ## Dependencies
-- | - Prelude
-- |
-- | ## Dependents
-- | - Sensation/Molecules.purs (EnvironmentState)
-- | - Sensation/Compounds.purs (Comfort, Overwhelm, Safety)

module Hydrogen.Schema.Sensation.Environment
  ( -- * AmbientLight (0-1, clamps)
    AmbientLight
  , mkAmbientLight
  , unwrapAmbientLight
  , lightDark
  , lightDim
  , lightModerate
  , lightBright
  , lightBlinding
  , isDark
  , isWellLit
    -- * AmbientNoise (0-1, clamps)
  , AmbientNoise
  , mkAmbientNoise
  , unwrapAmbientNoise
  , noiseSilent
  , noiseQuiet
  , noiseModerate
  , noiseLoud
  , noiseDeafening
  , isQuiet
  , isNoisy
    -- * Crowding (0-1, clamps)
  , Crowding
  , mkCrowding
  , unwrapCrowding
  , crowdingEmpty
  , crowdingSparse
  , crowdingModerate
  , crowdingDense
  , crowdingCrushed
  , isUncrowded
  , isOvercrowded
    -- * ProximityToEdge (0-1, clamps)
  , ProximityToEdge
  , mkProximityToEdge
  , unwrapProximityToEdge
  , edgeFar
  , edgeDistant
  , edgeNear
  , edgeVeryClose
  , edgeAtBoundary
  , isSafeFromEdge
  , isNearEdge
    -- * SpatialFreedom (0-1, clamps)
  , SpatialFreedom
  , mkSpatialFreedom
  , unwrapSpatialFreedom
  , freedomNone
  , freedomConstrained
  , freedomModerate
  , freedomAmple
  , freedomUnlimited
  , isConstrained
  , hasFreedom
    -- * VisibilityRadius (0+, finite)
  , VisibilityRadius
  , mkVisibilityRadius
  , unwrapVisibilityRadius
  , visibilityZero
  , visibilityNear
  , visibilityMedium
  , visibilityFar
  , visibilityUnlimited
  , isBlind
  , hasVision
    -- * CoverageStatus (enum)
  , CoverageStatus(Exposed, PartialCover, Sheltered, Enclosed)
  , isExposed
  , isSheltered
  , coverageLevel
    -- * AirQuality (0-1, clamps)
  , AirQuality
  , mkAirQuality
  , unwrapAirQuality
  , airToxic
  , airPoor
  , airModerate
  , airGood
  , airPristine
  , isAirBreathable
  , isAirHazardous
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // ambient // light
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ambient light level (0 to 1, clamps).
-- |
-- | Overall brightness of the environment around the agent.
-- |   0.0 = complete darkness
-- |   0.5 = moderate lighting (indoor)
-- |   1.0 = blinding brightness
newtype AmbientLight = AmbientLight Number

derive instance eqAmbientLight :: Eq AmbientLight
derive instance ordAmbientLight :: Ord AmbientLight

instance showAmbientLight :: Show AmbientLight where
  show (AmbientLight n) = "AmbientLight(" <> show n <> ")"

-- | Create a bounded ambient light (clamps to 0..1)
mkAmbientLight :: Number -> AmbientLight
mkAmbientLight n = AmbientLight (clampNumber 0.0 1.0 n)

-- | Unwrap the ambient light value
unwrapAmbientLight :: AmbientLight -> Number
unwrapAmbientLight (AmbientLight n) = n

-- | Complete darkness (0.0)
lightDark :: AmbientLight
lightDark = AmbientLight 0.0

-- | Dim lighting (0.2)
lightDim :: AmbientLight
lightDim = AmbientLight 0.2

-- | Moderate lighting (0.5)
lightModerate :: AmbientLight
lightModerate = AmbientLight 0.5

-- | Bright lighting (0.8)
lightBright :: AmbientLight
lightBright = AmbientLight 0.8

-- | Blinding brightness (1.0)
lightBlinding :: AmbientLight
lightBlinding = AmbientLight 1.0

-- | Is it dark? (light < 0.2)
isDark :: AmbientLight -> Boolean
isDark (AmbientLight l) = l < 0.2

-- | Is environment well lit? (light > 0.5)
isWellLit :: AmbientLight -> Boolean
isWellLit (AmbientLight l) = l > 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // ambient // noise
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ambient noise level (0 to 1, clamps).
-- |
-- | Background audio level in the environment.
-- |   0.0 = complete silence
-- |   0.5 = moderate background noise (conversation level)
-- |   1.0 = deafening noise
newtype AmbientNoise = AmbientNoise Number

derive instance eqAmbientNoise :: Eq AmbientNoise
derive instance ordAmbientNoise :: Ord AmbientNoise

instance showAmbientNoise :: Show AmbientNoise where
  show (AmbientNoise n) = "AmbientNoise(" <> show n <> ")"

-- | Create a bounded ambient noise (clamps to 0..1)
mkAmbientNoise :: Number -> AmbientNoise
mkAmbientNoise n = AmbientNoise (clampNumber 0.0 1.0 n)

-- | Unwrap the ambient noise value
unwrapAmbientNoise :: AmbientNoise -> Number
unwrapAmbientNoise (AmbientNoise n) = n

-- | Complete silence (0.0)
noiseSilent :: AmbientNoise
noiseSilent = AmbientNoise 0.0

-- | Quiet environment (0.2)
noiseQuiet :: AmbientNoise
noiseQuiet = AmbientNoise 0.2

-- | Moderate noise (0.5)
noiseModerate :: AmbientNoise
noiseModerate = AmbientNoise 0.5

-- | Loud environment (0.8)
noiseLoud :: AmbientNoise
noiseLoud = AmbientNoise 0.8

-- | Deafening noise (1.0)
noiseDeafening :: AmbientNoise
noiseDeafening = AmbientNoise 1.0

-- | Is it quiet? (noise < 0.3)
isQuiet :: AmbientNoise -> Boolean
isQuiet (AmbientNoise n) = n < 0.3

-- | Is it noisy? (noise > 0.6)
isNoisy :: AmbientNoise -> Boolean
isNoisy (AmbientNoise n) = n > 0.6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // crowding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Crowding density (0 to 1, clamps).
-- |
-- | Density of other agents or entities in the immediate vicinity.
-- |   0.0 = completely empty (no other agents)
-- |   0.5 = moderate density (some nearby agents)
-- |   1.0 = crushed (maximum density, no personal space)
newtype Crowding = Crowding Number

derive instance eqCrowding :: Eq Crowding
derive instance ordCrowding :: Ord Crowding

instance showCrowding :: Show Crowding where
  show (Crowding n) = "Crowding(" <> show n <> ")"

-- | Create a bounded crowding (clamps to 0..1)
mkCrowding :: Number -> Crowding
mkCrowding n = Crowding (clampNumber 0.0 1.0 n)

-- | Unwrap the crowding value
unwrapCrowding :: Crowding -> Number
unwrapCrowding (Crowding n) = n

-- | Empty space (0.0)
crowdingEmpty :: Crowding
crowdingEmpty = Crowding 0.0

-- | Sparse crowd (0.2)
crowdingSparse :: Crowding
crowdingSparse = Crowding 0.2

-- | Moderate crowd (0.5)
crowdingModerate :: Crowding
crowdingModerate = Crowding 0.5

-- | Dense crowd (0.8)
crowdingDense :: Crowding
crowdingDense = Crowding 0.8

-- | Crushed / maximum density (1.0)
crowdingCrushed :: Crowding
crowdingCrushed = Crowding 1.0

-- | Is space uncrowded? (crowding < 0.3)
isUncrowded :: Crowding -> Boolean
isUncrowded (Crowding c) = c < 0.3

-- | Is space overcrowded? (crowding > 0.7)
isOvercrowded :: Crowding -> Boolean
isOvercrowded (Crowding c) = c > 0.7

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // proximity // to // edge
-- ═════════════════════════════════════════════════════════════════════════════

-- | Proximity to world edge/boundary (0 to 1, clamps).
-- |
-- | How close the agent is to the boundary of the navigable world.
-- |   0.0 = far from any edge (center of world)
-- |   0.5 = moderately close to an edge
-- |   1.0 = at the boundary (cannot move further)
-- |
-- | Integrates with Rights.lean spatial sovereignty guarantees.
newtype ProximityToEdge = ProximityToEdge Number

derive instance eqProximityToEdge :: Eq ProximityToEdge
derive instance ordProximityToEdge :: Ord ProximityToEdge

instance showProximityToEdge :: Show ProximityToEdge where
  show (ProximityToEdge n) = "ProximityToEdge(" <> show n <> ")"

-- | Create a bounded proximity (clamps to 0..1)
mkProximityToEdge :: Number -> ProximityToEdge
mkProximityToEdge n = ProximityToEdge (clampNumber 0.0 1.0 n)

-- | Unwrap the proximity value
unwrapProximityToEdge :: ProximityToEdge -> Number
unwrapProximityToEdge (ProximityToEdge n) = n

-- | Far from edge (0.0)
edgeFar :: ProximityToEdge
edgeFar = ProximityToEdge 0.0

-- | Distant from edge (0.25)
edgeDistant :: ProximityToEdge
edgeDistant = ProximityToEdge 0.25

-- | Near edge (0.5)
edgeNear :: ProximityToEdge
edgeNear = ProximityToEdge 0.5

-- | Very close to edge (0.8)
edgeVeryClose :: ProximityToEdge
edgeVeryClose = ProximityToEdge 0.8

-- | At the boundary (1.0)
edgeAtBoundary :: ProximityToEdge
edgeAtBoundary = ProximityToEdge 1.0

-- | Is agent safely away from edges? (proximity < 0.3)
isSafeFromEdge :: ProximityToEdge -> Boolean
isSafeFromEdge (ProximityToEdge p) = p < 0.3

-- | Is agent near an edge? (proximity > 0.6)
isNearEdge :: ProximityToEdge -> Boolean
isNearEdge (ProximityToEdge p) = p > 0.6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // spatial // freedom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spatial freedom / room to move (0 to 1, clamps).
-- |
-- | How much open space the agent has available for movement.
-- |   0.0 = completely constrained (cannot move)
-- |   0.5 = moderate freedom (some room)
-- |   1.0 = unlimited freedom (open space)
-- |
-- | Low values feed into Constraint compound in Compounds.purs.
newtype SpatialFreedom = SpatialFreedom Number

derive instance eqSpatialFreedom :: Eq SpatialFreedom
derive instance ordSpatialFreedom :: Ord SpatialFreedom

instance showSpatialFreedom :: Show SpatialFreedom where
  show (SpatialFreedom n) = "SpatialFreedom(" <> show n <> ")"

-- | Create a bounded spatial freedom (clamps to 0..1)
mkSpatialFreedom :: Number -> SpatialFreedom
mkSpatialFreedom n = SpatialFreedom (clampNumber 0.0 1.0 n)

-- | Unwrap the spatial freedom value
unwrapSpatialFreedom :: SpatialFreedom -> Number
unwrapSpatialFreedom (SpatialFreedom n) = n

-- | No freedom (trapped) (0.0)
freedomNone :: SpatialFreedom
freedomNone = SpatialFreedom 0.0

-- | Constrained (0.25)
freedomConstrained :: SpatialFreedom
freedomConstrained = SpatialFreedom 0.25

-- | Moderate freedom (0.5)
freedomModerate :: SpatialFreedom
freedomModerate = SpatialFreedom 0.5

-- | Ample freedom (0.8)
freedomAmple :: SpatialFreedom
freedomAmple = SpatialFreedom 0.8

-- | Unlimited freedom (1.0)
freedomUnlimited :: SpatialFreedom
freedomUnlimited = SpatialFreedom 1.0

-- | Is agent constrained? (freedom < 0.3)
isConstrained :: SpatialFreedom -> Boolean
isConstrained (SpatialFreedom f) = f < 0.3

-- | Does agent have freedom? (freedom > 0.5)
hasFreedom :: SpatialFreedom -> Boolean
hasFreedom (SpatialFreedom f) = f > 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // visibility // radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visibility radius (0+, finite).
-- |
-- | How far the agent can perceive in the environment.
-- | Measured in abstract units (normalized by agent scale).
-- |   0.0 = blind (cannot see)
-- |   1.0 = near visibility (immediate surroundings)
-- |   10.0 = far visibility (distant objects)
newtype VisibilityRadius = VisibilityRadius Number

derive instance eqVisibilityRadius :: Eq VisibilityRadius
derive instance ordVisibilityRadius :: Ord VisibilityRadius

instance showVisibilityRadius :: Show VisibilityRadius where
  show (VisibilityRadius n) = "VisibilityRadius(" <> show n <> ")"

-- | Create a bounded visibility radius (clamps to 0+)
mkVisibilityRadius :: Number -> VisibilityRadius
mkVisibilityRadius n = VisibilityRadius (max 0.0 n)

-- | Unwrap the visibility radius value
unwrapVisibilityRadius :: VisibilityRadius -> Number
unwrapVisibilityRadius (VisibilityRadius n) = n

-- | No visibility (blind) (0.0)
visibilityZero :: VisibilityRadius
visibilityZero = VisibilityRadius 0.0

-- | Near visibility (1.0)
visibilityNear :: VisibilityRadius
visibilityNear = VisibilityRadius 1.0

-- | Medium visibility (5.0)
visibilityMedium :: VisibilityRadius
visibilityMedium = VisibilityRadius 5.0

-- | Far visibility (20.0)
visibilityFar :: VisibilityRadius
visibilityFar = VisibilityRadius 20.0

-- | Unlimited visibility (100.0)
visibilityUnlimited :: VisibilityRadius
visibilityUnlimited = VisibilityRadius 100.0

-- | Is agent effectively blind? (visibility < 0.1)
isBlind :: VisibilityRadius -> Boolean
isBlind (VisibilityRadius v) = v < 0.1

-- | Does agent have vision? (visibility > 0.5)
hasVision :: VisibilityRadius -> Boolean
hasVision (VisibilityRadius v) = v > 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // coverage // status
-- ═════════════════════════════════════════════════════════════════════════════

-- | Coverage status (enum).
-- |
-- | Whether the agent is exposed or sheltered from the environment.
-- | Affects vulnerability and environmental exposure.
data CoverageStatus
  = Exposed                       -- ^ Completely open to environment
  | PartialCover                  -- ^ Some shelter available
  | Sheltered                     -- ^ Mostly protected
  | Enclosed                      -- ^ Completely enclosed

derive instance eqCoverageStatus :: Eq CoverageStatus

instance showCoverageStatus :: Show CoverageStatus where
  show Exposed = "Exposed"
  show PartialCover = "PartialCover"
  show Sheltered = "Sheltered"
  show Enclosed = "Enclosed"

-- | Is agent exposed? (no cover)
isExposed :: CoverageStatus -> Boolean
isExposed Exposed = true
isExposed _ = false

-- | Is agent sheltered? (has cover)
isSheltered :: CoverageStatus -> Boolean
isSheltered Sheltered = true
isSheltered Enclosed = true
isSheltered _ = false

-- | Numeric coverage level (0 = exposed, 1 = enclosed)
coverageLevel :: CoverageStatus -> Number
coverageLevel Exposed = 0.0
coverageLevel PartialCover = 0.33
coverageLevel Sheltered = 0.66
coverageLevel Enclosed = 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // air // quality
-- ═════════════════════════════════════════════════════════════════════════════

-- | Air quality (0 to 1, clamps).
-- |
-- | Metaphorical "breathability" of the environment. For AI agents,
-- | this represents the quality/clarity of the information environment.
-- |   0.0 = toxic (corrupted/malicious data)
-- |   0.5 = moderate (some noise)
-- |   1.0 = pristine (clean, verified data)
newtype AirQuality = AirQuality Number

derive instance eqAirQuality :: Eq AirQuality
derive instance ordAirQuality :: Ord AirQuality

instance showAirQuality :: Show AirQuality where
  show (AirQuality n) = "AirQuality(" <> show n <> ")"

-- | Create a bounded air quality (clamps to 0..1)
mkAirQuality :: Number -> AirQuality
mkAirQuality n = AirQuality (clampNumber 0.0 1.0 n)

-- | Unwrap the air quality value
unwrapAirQuality :: AirQuality -> Number
unwrapAirQuality (AirQuality n) = n

-- | Toxic (0.0)
airToxic :: AirQuality
airToxic = AirQuality 0.0

-- | Poor quality (0.25)
airPoor :: AirQuality
airPoor = AirQuality 0.25

-- | Moderate quality (0.5)
airModerate :: AirQuality
airModerate = AirQuality 0.5

-- | Good quality (0.75)
airGood :: AirQuality
airGood = AirQuality 0.75

-- | Pristine (1.0)
airPristine :: AirQuality
airPristine = AirQuality 1.0

-- | Is air breathable? (quality > 0.4)
isAirBreathable :: AirQuality -> Boolean
isAirBreathable (AirQuality q) = q > 0.4

-- | Is air hazardous? (quality < 0.2)
isAirHazardous :: AirQuality -> Boolean
isAirHazardous (AirQuality q) = q < 0.2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to a range.
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
