-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                // hydrogen // schema // dimension // physical // astronomical
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Astronomical length units.
-- |
-- | For measuring at cosmic scales - planetary, stellar, and galactic.
-- | All units convert through Meter as the canonical representation.
-- |
-- | ## Scale Reference
-- | - AU: Solar system scale (sun-earth distance)
-- | - Light year: Stellar/interstellar distances
-- | - Parsec: Astronomical parallax measurement
-- | - Kiloparsec/Megaparsec: Galactic/intergalactic distances

module Hydrogen.Schema.Dimension.Physical.Astronomical
  ( -- * Types
    LightYear(LightYear)
  , Parsec(Parsec)
  , AstronomicalUnit(AstronomicalUnit)
  , Kiloparsec(Kiloparsec)
  , Megaparsec(Megaparsec)
  , LightSecond(LightSecond)
  , LightMinute(LightMinute)
  , SolarRadius(SolarRadius)
  , EarthRadius(EarthRadius)
  , LunarDistance(LunarDistance)
  
  -- * Constructors
  , lightYear
  , lightYears
  , parsec
  , parsecs
  , au
  , astronomicalUnit
  , kiloparsec
  , kiloparsecs
  , megaparsec
  , megaparsecs
  , lightSecond
  , lightSeconds
  , lightMinute
  , lightMinutes
  , solarRadius
  , solarRadii
  , earthRadius
  , earthRadii
  , lunarDistance
  , lunarDistances
  
  -- * Accessors
  , unwrapLightYear
  , unwrapParsec
  , unwrapAU
  , unwrapKiloparsec
  , unwrapMegaparsec
  , unwrapLightSecond
  , unwrapLightMinute
  , unwrapSolarRadius
  , unwrapEarthRadius
  , unwrapLunarDistance
  
  -- * Conversions to Meter
  , lightYearsToMeters
  , parsecsToMeters
  , auToMeters
  , kiloparsecsToMeters
  , megaparsecsToMeters
  , lightSecondsToMeters
  , lightMinutesToMeters
  , solarRadiusToMeters
  , earthRadiusToMeters
  , lunarDistanceToMeters
  
  -- * Physical Constants
  , speedOfLight
  , metersPerLightYear
  , metersPerParsec
  , metersPerAU
  , metersPerSolarRadius
  , metersPerEarthRadius
  , metersPerLunarDistance
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (*)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Speed of light in m/s (exact by definition)
speedOfLight :: Number
speedOfLight = 299792458.0

-- | Meters per light year
metersPerLightYear :: Number
metersPerLightYear = 9.4607304725808e15

-- | Meters per parsec
metersPerParsec :: Number
metersPerParsec = 3.0856775814913673e16

-- | Meters per AU (exact by definition)
metersPerAU :: Number
metersPerAU = 1.495978707e11

-- | Meters per solar radius (IAU nominal)
metersPerSolarRadius :: Number
metersPerSolarRadius = 6.96e8

-- | Meters per Earth radius (IAU nominal equatorial)
metersPerEarthRadius :: Number
metersPerEarthRadius = 6.3781e6

-- | Meters per lunar distance (mean Earth-Moon distance)
metersPerLunarDistance :: Number
metersPerLunarDistance = 3.844e8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // light year
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light year - distance light travels in one Julian year
newtype LightYear = LightYear Number

derive instance eqLightYear :: Eq LightYear
derive instance ordLightYear :: Ord LightYear

instance showLightYear :: Show LightYear where
  show (LightYear n) = show n <> " ly"

lightYear :: Number -> LightYear
lightYear = LightYear

lightYears :: Number -> LightYear
lightYears = LightYear

unwrapLightYear :: LightYear -> Number
unwrapLightYear (LightYear n) = n

lightYearsToMeters :: LightYear -> Number
lightYearsToMeters (LightYear n) = n * metersPerLightYear

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // parsec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Parsec - parallax of one arcsecond (~3.26 light years)
newtype Parsec = Parsec Number

derive instance eqParsec :: Eq Parsec
derive instance ordParsec :: Ord Parsec

instance showParsec :: Show Parsec where
  show (Parsec n) = show n <> " pc"

parsec :: Number -> Parsec
parsec = Parsec

parsecs :: Number -> Parsec
parsecs = Parsec

unwrapParsec :: Parsec -> Number
unwrapParsec (Parsec n) = n

parsecsToMeters :: Parsec -> Number
parsecsToMeters (Parsec n) = n * metersPerParsec

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // astronomical unit
-- ═════════════════════════════════════════════════════════════════════════════

-- | Astronomical Unit - mean sun-earth distance (exact by definition)
newtype AstronomicalUnit = AstronomicalUnit Number

derive instance eqAstronomicalUnit :: Eq AstronomicalUnit
derive instance ordAstronomicalUnit :: Ord AstronomicalUnit

instance showAstronomicalUnit :: Show AstronomicalUnit where
  show (AstronomicalUnit n) = show n <> " AU"

au :: Number -> AstronomicalUnit
au = AstronomicalUnit

astronomicalUnit :: Number -> AstronomicalUnit
astronomicalUnit = AstronomicalUnit

unwrapAU :: AstronomicalUnit -> Number
unwrapAU (AstronomicalUnit n) = n

auToMeters :: AstronomicalUnit -> Number
auToMeters (AstronomicalUnit n) = n * metersPerAU

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // kiloparsec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Kiloparsec - 1000 parsecs (galactic scale)
newtype Kiloparsec = Kiloparsec Number

derive instance eqKiloparsec :: Eq Kiloparsec
derive instance ordKiloparsec :: Ord Kiloparsec

instance showKiloparsec :: Show Kiloparsec where
  show (Kiloparsec n) = show n <> " kpc"

kiloparsec :: Number -> Kiloparsec
kiloparsec = Kiloparsec

kiloparsecs :: Number -> Kiloparsec
kiloparsecs = Kiloparsec

unwrapKiloparsec :: Kiloparsec -> Number
unwrapKiloparsec (Kiloparsec n) = n

kiloparsecsToMeters :: Kiloparsec -> Number
kiloparsecsToMeters (Kiloparsec n) = n * metersPerParsec * 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // megaparsec
-- ═════════════════════════════════════════════════════════════════════════════

-- | Megaparsec - 1 million parsecs (intergalactic scale)
newtype Megaparsec = Megaparsec Number

derive instance eqMegaparsec :: Eq Megaparsec
derive instance ordMegaparsec :: Ord Megaparsec

instance showMegaparsec :: Show Megaparsec where
  show (Megaparsec n) = show n <> " Mpc"

megaparsec :: Number -> Megaparsec
megaparsec = Megaparsec

megaparsecs :: Number -> Megaparsec
megaparsecs = Megaparsec

unwrapMegaparsec :: Megaparsec -> Number
unwrapMegaparsec (Megaparsec n) = n

megaparsecsToMeters :: Megaparsec -> Number
megaparsecsToMeters (Megaparsec n) = n * metersPerParsec * 1.0e6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // light second
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light second - distance light travels in one second
newtype LightSecond = LightSecond Number

derive instance eqLightSecond :: Eq LightSecond
derive instance ordLightSecond :: Ord LightSecond

instance showLightSecond :: Show LightSecond where
  show (LightSecond n) = show n <> " ls"

lightSecond :: Number -> LightSecond
lightSecond = LightSecond

lightSeconds :: Number -> LightSecond
lightSeconds = LightSecond

unwrapLightSecond :: LightSecond -> Number
unwrapLightSecond (LightSecond n) = n

lightSecondsToMeters :: LightSecond -> Number
lightSecondsToMeters (LightSecond n) = n * speedOfLight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // light minute
-- ═════════════════════════════════════════════════════════════════════════════

-- | Light minute - distance light travels in one minute
newtype LightMinute = LightMinute Number

derive instance eqLightMinute :: Eq LightMinute
derive instance ordLightMinute :: Ord LightMinute

instance showLightMinute :: Show LightMinute where
  show (LightMinute n) = show n <> " lm"

lightMinute :: Number -> LightMinute
lightMinute = LightMinute

lightMinutes :: Number -> LightMinute
lightMinutes = LightMinute

unwrapLightMinute :: LightMinute -> Number
unwrapLightMinute (LightMinute n) = n

lightMinutesToMeters :: LightMinute -> Number
lightMinutesToMeters (LightMinute n) = n * speedOfLight * 60.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // solar radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | Solar radius - radius of the Sun (IAU nominal)
-- |
-- | ~696,000 km. Used for expressing stellar sizes.
-- | The Sun has a radius of 1 R☉ by definition.
newtype SolarRadius = SolarRadius Number

derive instance eqSolarRadius :: Eq SolarRadius
derive instance ordSolarRadius :: Ord SolarRadius

instance showSolarRadius :: Show SolarRadius where
  show (SolarRadius n) = show n <> " R☉"

solarRadius :: Number -> SolarRadius
solarRadius = SolarRadius

solarRadii :: Number -> SolarRadius
solarRadii = SolarRadius

unwrapSolarRadius :: SolarRadius -> Number
unwrapSolarRadius (SolarRadius n) = n

solarRadiusToMeters :: SolarRadius -> Number
solarRadiusToMeters (SolarRadius n) = n * metersPerSolarRadius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // earth radius
-- ═════════════════════════════════════════════════════════════════════════════

-- | Earth radius - equatorial radius of Earth (IAU nominal)
-- |
-- | ~6,378 km. Used for expressing planetary sizes and distances.
-- | Earth's equatorial radius is 1 R⊕ by definition.
newtype EarthRadius = EarthRadius Number

derive instance eqEarthRadius :: Eq EarthRadius
derive instance ordEarthRadius :: Ord EarthRadius

instance showEarthRadius :: Show EarthRadius where
  show (EarthRadius n) = show n <> " R⊕"

earthRadius :: Number -> EarthRadius
earthRadius = EarthRadius

earthRadii :: Number -> EarthRadius
earthRadii = EarthRadius

unwrapEarthRadius :: EarthRadius -> Number
unwrapEarthRadius (EarthRadius n) = n

earthRadiusToMeters :: EarthRadius -> Number
earthRadiusToMeters (EarthRadius n) = n * metersPerEarthRadius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // lunar distance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lunar distance - mean distance from Earth to Moon
-- |
-- | ~384,400 km. Used for expressing distances in the Earth-Moon system.
-- | Also called "Moon distance" (LD).
newtype LunarDistance = LunarDistance Number

derive instance eqLunarDistance :: Eq LunarDistance
derive instance ordLunarDistance :: Ord LunarDistance

instance showLunarDistance :: Show LunarDistance where
  show (LunarDistance n) = show n <> " LD"

lunarDistance :: Number -> LunarDistance
lunarDistance = LunarDistance

lunarDistances :: Number -> LunarDistance
lunarDistances = LunarDistance

unwrapLunarDistance :: LunarDistance -> Number
unwrapLunarDistance (LunarDistance n) = n

lunarDistanceToMeters :: LunarDistance -> Number
lunarDistanceToMeters (LunarDistance n) = n * metersPerLunarDistance
