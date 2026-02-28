-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // sensation // contact
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Contact Atoms — Touch and pressure sensation primitives.
-- |
-- | Contact sensation is the input side of haptics. While the Haptic pillar
-- | models OUTPUT (vibrations sent to humans), Contact models INPUT:
-- |   - What am I touching?
-- |   - What does the surface feel like?
-- |   - How much force is at the contact point?
-- |
-- | ## SCHEMA.md Reference (Pillar 15: Sensation — Contact)
-- |
-- | | Name              | Type   | Min   | Max   | Behavior | Notes                      |
-- | |-------------------|--------|-------|-------|----------|----------------------------|
-- | | ContactPressure   | Number | 0     | none  | finite   | Force per area (Pa)        |
-- | | Friction          | Number | 0     | 1     | clamps   | Resistance to sliding      |
-- | | Compliance        | Number | 0     | 1     | clamps   | Surface give/softness      |
-- | | SurfaceTemperature| Number | 0     | 1000  | clamps   | Temperature in Kelvin      |
-- | | SurfaceRoughness  | Number | 0     | 1     | clamps   | Tactile roughness          |
-- | | Grip              | Number | 0     | 1     | clamps   | Hold security              |
-- | | Penetration       | Number | 0     | 1     | clamps   | How deep into surface      |
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Data.Number (sqrt)
-- |
-- | ## Dependents
-- | - Sensation/Molecules.purs (ContactEvent, BodyState)
-- | - Sensation/Compounds.purs (Comfort, Distress)

module Hydrogen.Schema.Sensation.Contact
  ( -- * ContactPressure (0+, finite, Pascals)
    ContactPressure
  , mkContactPressure
  , unwrapContactPressure
  , pressureNone
  , pressureLight
  , pressureModerate
  , pressureHeavy
  , pressureCrushing
  , isPressureSafe
  , isPressureDangerous
    -- * ContactNormal (unit vector)
  , ContactNormal
  , mkContactNormal
  , normalX
  , normalY
  , normalZ
  , normalUp
  , normalDown
  , normalForward
  , dotNormal
    -- * Friction (0-1, clamps)
  , Friction
  , mkFriction
  , unwrapFriction
  , frictionNone
  , frictionLow
  , frictionMedium
  , frictionHigh
  , frictionMaximum
  , isSlippery
  , isGrippy
    -- * Compliance (0-1, clamps)
  , Compliance
  , mkCompliance
  , unwrapCompliance
  , complianceRigid
  , complianceFirm
  , complianceSoft
  , complianceVerysoft
  , complianceFluid
  , isSolid
  , isDeformable
    -- * SurfaceTemperature (0-1000 K, clamps)
  , SurfaceTemperature
  , mkSurfaceTemperature
  , unwrapSurfaceTemperature
  , tempFreezing
  , tempCool
  , tempNeutral
  , tempWarm
  , tempHot
  , tempDangerous
  , isTempComfortable
  , isTempDangerous
    -- * SurfaceRoughness (0-1, clamps)
  , SurfaceRoughness
  , mkSurfaceRoughness
  , unwrapSurfaceRoughness
  , roughnessSmooth
  , roughnessFine
  , roughnessMedium
  , roughnessCoarse
  , roughnessVeryrough
  , isSmooth
  , isRough
    -- * Grip (0-1, clamps)
  , Grip
  , mkGrip
  , unwrapGrip
  , gripNone
  , gripWeak
  , gripModerate
  , gripStrong
  , gripMaximum
  , isHolding
  , isSlipping
    -- * Penetration (0-1, clamps)
  , Penetration
  , mkPenetration
  , unwrapPenetration
  , penetrationNone
  , penetrationSurface
  , penetrationShallow
  , penetrationDeep
  , penetrationFull
  , isContacting
  , isEmbedded
  ) where

import Prelude

import Data.Number (sqrt) as Num

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // contact // pressure
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contact pressure in Pascals (0+, finite).
-- |
-- | Force per unit area at a contact point. Higher values indicate
-- | stronger contact forces. No upper bound (finite behavior).
-- |
-- | Reference values:
-- |   - Light touch: ~100 Pa
-- |   - Firm press: ~10,000 Pa
-- |   - Pain threshold: ~100,000 Pa
-- |   - Bone fracture: ~1,000,000 Pa
newtype ContactPressure = ContactPressure Number

derive instance eqContactPressure :: Eq ContactPressure
derive instance ordContactPressure :: Ord ContactPressure

instance showContactPressure :: Show ContactPressure where
  show (ContactPressure n) = "ContactPressure(" <> show n <> "Pa)"

-- | Create a bounded pressure (clamps to 0+)
mkContactPressure :: Number -> ContactPressure
mkContactPressure n = ContactPressure (max 0.0 n)

-- | Unwrap the pressure value
unwrapContactPressure :: ContactPressure -> Number
unwrapContactPressure (ContactPressure n) = n

-- | No pressure (not touching)
pressureNone :: ContactPressure
pressureNone = ContactPressure 0.0

-- | Light touch (~100 Pa)
pressureLight :: ContactPressure
pressureLight = ContactPressure 100.0

-- | Moderate pressure (~10,000 Pa)
pressureModerate :: ContactPressure
pressureModerate = ContactPressure 10000.0

-- | Heavy pressure (~100,000 Pa)
pressureHeavy :: ContactPressure
pressureHeavy = ContactPressure 100000.0

-- | Crushing pressure (~1,000,000 Pa)
pressureCrushing :: ContactPressure
pressureCrushing = ContactPressure 1000000.0

-- | Is pressure in safe range? (< 50,000 Pa)
isPressureSafe :: ContactPressure -> Boolean
isPressureSafe (ContactPressure p) = p < 50000.0

-- | Is pressure dangerous? (> 100,000 Pa)
isPressureDangerous :: ContactPressure -> Boolean
isPressureDangerous (ContactPressure p) = p > 100000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // contact // normal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contact normal as a unit vector (normalized).
-- |
-- | The direction perpendicular to the contact surface, pointing
-- | away from the surface. Used to determine contact orientation.
type ContactNormal =
  { x :: Number
  , y :: Number
  , z :: Number
  }

-- | Create a contact normal (automatically normalizes)
mkContactNormal :: Number -> Number -> Number -> ContactNormal
mkContactNormal x y z =
  let mag = Num.sqrt (x * x + y * y + z * z)
      safeMag = if mag < 0.0001 then 1.0 else mag
  in { x: x / safeMag, y: y / safeMag, z: z / safeMag }

-- | Get X component
normalX :: ContactNormal -> Number
normalX n = n.x

-- | Get Y component
normalY :: ContactNormal -> Number
normalY n = n.y

-- | Get Z component
normalZ :: ContactNormal -> Number
normalZ n = n.z

-- | Upward-facing surface
normalUp :: ContactNormal
normalUp = { x: 0.0, y: 1.0, z: 0.0 }

-- | Downward-facing surface
normalDown :: ContactNormal
normalDown = { x: 0.0, y: -1.0, z: 0.0 }

-- | Forward-facing surface
normalForward :: ContactNormal
normalForward = { x: 0.0, y: 0.0, z: 1.0 }

-- | Dot product of two normals
dotNormal :: ContactNormal -> ContactNormal -> Number
dotNormal a b = a.x * b.x + a.y * b.y + a.z * b.z

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // friction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Friction coefficient (0 to 1, clamps).
-- |
-- | Resistance to sliding along the contact surface.
-- |   0.0 = frictionless (ice, oil)
-- |   0.5 = moderate friction (wood, plastic)
-- |   1.0 = maximum friction (rubber, sandpaper)
newtype Friction = Friction Number

derive instance eqFriction :: Eq Friction
derive instance ordFriction :: Ord Friction

instance showFriction :: Show Friction where
  show (Friction n) = "Friction(" <> show n <> ")"

-- | Create a bounded friction (clamps to 0..1)
mkFriction :: Number -> Friction
mkFriction n = Friction (clampNumber 0.0 1.0 n)

-- | Unwrap the friction value
unwrapFriction :: Friction -> Number
unwrapFriction (Friction n) = n

-- | No friction (frictionless)
frictionNone :: Friction
frictionNone = Friction 0.0

-- | Low friction (0.2 - slippery)
frictionLow :: Friction
frictionLow = Friction 0.2

-- | Medium friction (0.5 - normal)
frictionMedium :: Friction
frictionMedium = Friction 0.5

-- | High friction (0.8 - grippy)
frictionHigh :: Friction
frictionHigh = Friction 0.8

-- | Maximum friction (1.0)
frictionMaximum :: Friction
frictionMaximum = Friction 1.0

-- | Is surface slippery? (friction < 0.3)
isSlippery :: Friction -> Boolean
isSlippery (Friction f) = f < 0.3

-- | Is surface grippy? (friction > 0.6)
isGrippy :: Friction -> Boolean
isGrippy (Friction f) = f > 0.6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // compliance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surface compliance / softness (0 to 1, clamps).
-- |
-- | How much the surface gives under pressure.
-- |   0.0 = perfectly rigid (steel, stone)
-- |   0.5 = moderately soft (foam, flesh)
-- |   1.0 = completely fluid (water, air)
newtype Compliance = Compliance Number

derive instance eqCompliance :: Eq Compliance
derive instance ordCompliance :: Ord Compliance

instance showCompliance :: Show Compliance where
  show (Compliance n) = "Compliance(" <> show n <> ")"

-- | Create a bounded compliance (clamps to 0..1)
mkCompliance :: Number -> Compliance
mkCompliance n = Compliance (clampNumber 0.0 1.0 n)

-- | Unwrap the compliance value
unwrapCompliance :: Compliance -> Number
unwrapCompliance (Compliance n) = n

-- | Rigid surface (0.0)
complianceRigid :: Compliance
complianceRigid = Compliance 0.0

-- | Firm surface (0.2)
complianceFirm :: Compliance
complianceFirm = Compliance 0.2

-- | Soft surface (0.5)
complianceSoft :: Compliance
complianceSoft = Compliance 0.5

-- | Very soft surface (0.8)
complianceVerysoft :: Compliance
complianceVerysoft = Compliance 0.8

-- | Fluid surface (1.0)
complianceFluid :: Compliance
complianceFluid = Compliance 1.0

-- | Is surface solid? (compliance < 0.3)
isSolid :: Compliance -> Boolean
isSolid (Compliance c) = c < 0.3

-- | Is surface deformable? (compliance > 0.5)
isDeformable :: Compliance -> Boolean
isDeformable (Compliance c) = c > 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // surface // temperature
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surface temperature in Kelvin (0 to 1000 K, clamps).
-- |
-- | Temperature of the contacted surface. Bounded for safety.
-- |
-- | Reference values:
-- |   - Absolute zero: 0 K (not physically achievable)
-- |   - Freezing water: 273 K
-- |   - Body temperature: 310 K
-- |   - Boiling water: 373 K
-- |   - Pain threshold (hot): ~320 K
-- |   - Pain threshold (cold): ~280 K
newtype SurfaceTemperature = SurfaceTemperature Number

derive instance eqSurfaceTemperature :: Eq SurfaceTemperature
derive instance ordSurfaceTemperature :: Ord SurfaceTemperature

instance showSurfaceTemperature :: Show SurfaceTemperature where
  show (SurfaceTemperature n) = "SurfaceTemperature(" <> show n <> "K)"

-- | Create a bounded temperature (clamps to 0..1000)
mkSurfaceTemperature :: Number -> SurfaceTemperature
mkSurfaceTemperature n = SurfaceTemperature (clamp 0.0 1000.0 n)

-- | Unwrap the temperature value
unwrapSurfaceTemperature :: SurfaceTemperature -> Number
unwrapSurfaceTemperature (SurfaceTemperature n) = n

-- | Freezing (273 K = 0 C)
tempFreezing :: SurfaceTemperature
tempFreezing = SurfaceTemperature 273.0

-- | Cool (288 K = 15 C)
tempCool :: SurfaceTemperature
tempCool = SurfaceTemperature 288.0

-- | Neutral / body temperature (310 K = 37 C)
tempNeutral :: SurfaceTemperature
tempNeutral = SurfaceTemperature 310.0

-- | Warm (320 K = 47 C)
tempWarm :: SurfaceTemperature
tempWarm = SurfaceTemperature 320.0

-- | Hot (350 K = 77 C)
tempHot :: SurfaceTemperature
tempHot = SurfaceTemperature 350.0

-- | Dangerous (400 K = 127 C)
tempDangerous :: SurfaceTemperature
tempDangerous = SurfaceTemperature 400.0

-- | Is temperature comfortable? (285-315 K)
isTempComfortable :: SurfaceTemperature -> Boolean
isTempComfortable (SurfaceTemperature t) = t >= 285.0 && t <= 315.0

-- | Is temperature dangerous? (< 273 K or > 330 K)
isTempDangerous :: SurfaceTemperature -> Boolean
isTempDangerous (SurfaceTemperature t) = t < 273.0 || t > 330.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // surface // roughness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Surface roughness (0 to 1, clamps).
-- |
-- | Tactile texture of the surface.
-- |   0.0 = perfectly smooth (glass, polished metal)
-- |   0.5 = medium texture (wood grain, fabric)
-- |   1.0 = very rough (gravel, bark)
newtype SurfaceRoughness = SurfaceRoughness Number

derive instance eqSurfaceRoughness :: Eq SurfaceRoughness
derive instance ordSurfaceRoughness :: Ord SurfaceRoughness

instance showSurfaceRoughness :: Show SurfaceRoughness where
  show (SurfaceRoughness n) = "SurfaceRoughness(" <> show n <> ")"

-- | Create a bounded roughness (clamps to 0..1)
mkSurfaceRoughness :: Number -> SurfaceRoughness
mkSurfaceRoughness n = SurfaceRoughness (clampNumber 0.0 1.0 n)

-- | Unwrap the roughness value
unwrapSurfaceRoughness :: SurfaceRoughness -> Number
unwrapSurfaceRoughness (SurfaceRoughness n) = n

-- | Perfectly smooth (0.0)
roughnessSmooth :: SurfaceRoughness
roughnessSmooth = SurfaceRoughness 0.0

-- | Fine texture (0.2)
roughnessFine :: SurfaceRoughness
roughnessFine = SurfaceRoughness 0.2

-- | Medium texture (0.5)
roughnessMedium :: SurfaceRoughness
roughnessMedium = SurfaceRoughness 0.5

-- | Coarse texture (0.75)
roughnessCoarse :: SurfaceRoughness
roughnessCoarse = SurfaceRoughness 0.75

-- | Very rough (1.0)
roughnessVeryrough :: SurfaceRoughness
roughnessVeryrough = SurfaceRoughness 1.0

-- | Is surface smooth? (roughness < 0.2)
isSmooth :: SurfaceRoughness -> Boolean
isSmooth (SurfaceRoughness r) = r < 0.2

-- | Is surface rough? (roughness > 0.6)
isRough :: SurfaceRoughness -> Boolean
isRough (SurfaceRoughness r) = r > 0.6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // grip
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grip security (0 to 1, clamps).
-- |
-- | How securely the agent is holding an object or surface.
-- |   0.0 = no grip (not holding)
-- |   0.5 = moderate grip (can hold but might slip)
-- |   1.0 = maximum grip (completely secure)
newtype Grip = Grip Number

derive instance eqGrip :: Eq Grip
derive instance ordGrip :: Ord Grip

instance showGrip :: Show Grip where
  show (Grip n) = "Grip(" <> show n <> ")"

-- | Create a bounded grip (clamps to 0..1)
mkGrip :: Number -> Grip
mkGrip n = Grip (clampNumber 0.0 1.0 n)

-- | Unwrap the grip value
unwrapGrip :: Grip -> Number
unwrapGrip (Grip n) = n

-- | No grip (not holding)
gripNone :: Grip
gripNone = Grip 0.0

-- | Weak grip (0.25)
gripWeak :: Grip
gripWeak = Grip 0.25

-- | Moderate grip (0.5)
gripModerate :: Grip
gripModerate = Grip 0.5

-- | Strong grip (0.75)
gripStrong :: Grip
gripStrong = Grip 0.75

-- | Maximum grip (1.0)
gripMaximum :: Grip
gripMaximum = Grip 1.0

-- | Is agent holding something? (grip > 0.1)
isHolding :: Grip -> Boolean
isHolding (Grip g) = g > 0.1

-- | Is grip slipping? (grip between 0.1 and 0.3)
isSlipping :: Grip -> Boolean
isSlipping (Grip g) = g > 0.1 && g < 0.3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // penetration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contact penetration depth (0 to 1, clamps).
-- |
-- | How deeply into a surface the contact point is.
-- |   0.0 = no contact (above surface)
-- |   0.1 = surface contact (touching)
-- |   0.5 = shallow penetration
-- |   1.0 = fully embedded
newtype Penetration = Penetration Number

derive instance eqPenetration :: Eq Penetration
derive instance ordPenetration :: Ord Penetration

instance showPenetration :: Show Penetration where
  show (Penetration n) = "Penetration(" <> show n <> ")"

-- | Create a bounded penetration (clamps to 0..1)
mkPenetration :: Number -> Penetration
mkPenetration n = Penetration (clampNumber 0.0 1.0 n)

-- | Unwrap the penetration value
unwrapPenetration :: Penetration -> Number
unwrapPenetration (Penetration n) = n

-- | No penetration (above surface)
penetrationNone :: Penetration
penetrationNone = Penetration 0.0

-- | Surface contact (0.1)
penetrationSurface :: Penetration
penetrationSurface = Penetration 0.1

-- | Shallow penetration (0.3)
penetrationShallow :: Penetration
penetrationShallow = Penetration 0.3

-- | Deep penetration (0.7)
penetrationDeep :: Penetration
penetrationDeep = Penetration 0.7

-- | Full embedding (1.0)
penetrationFull :: Penetration
penetrationFull = Penetration 1.0

-- | Is there contact? (penetration > 0.05)
isContacting :: Penetration -> Boolean
isContacting (Penetration p) = p > 0.05

-- | Is agent embedded in surface? (penetration > 0.5)
isEmbedded :: Penetration -> Boolean
isEmbedded (Penetration p) = p > 0.5

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp a number to a range.
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi x = max lo (min hi x)
