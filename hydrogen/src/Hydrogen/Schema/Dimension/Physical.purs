-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // schema // dimension // physical
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Physical length units - real-world measurements.
-- |
-- | Leader module that re-exports all physical unit sub-modules.
-- |
-- | ## Scale Coverage
-- | From Planck length (10^-35 m) to Quettameters (10^30 m).
-- | Complete coverage for any display context.
-- |
-- | ## Sub-modules
-- | - SI: Meter and all SI prefixes (yocto to quetta)
-- | - Imperial: Inch, foot, mile, nautical mile, etc.
-- | - Typographic: Point, pica, didot, cicero
-- | - Atomic: Angstrom, Bohr radius, Planck length
-- | - Astronomical: Light year, parsec, AU
-- |
-- | ## Design
-- | All units convert through Meter as canonical representation.
-- | Each unit is a distinct newtype preventing unit confusion bugs.

module Hydrogen.Schema.Dimension.Physical
  ( -- * Re-exports: SI Units
    module SI
    
  -- * Re-exports: Imperial Units
  , module Imperial
  
  -- * Re-exports: Typographic Units
  , module Typographic
  
  -- * Re-exports: Atomic Scale Units
  , module Atomic
  
  -- * Re-exports: Astronomical Scale Units
  , module Astronomical
  
  -- * Type Class
  , class PhysicalLength
  , toMeters
  , fromMeters
  
  -- * Generic Conversion
  , convert
  ) where

import Prelude
  ( identity
  , (*)
  , (/)
  , (<<<)
  )

import Hydrogen.Schema.Dimension.Physical.SI
  ( Meter(Meter)
  , Millimeter(Millimeter)
  , Centimeter(Centimeter)
  , Kilometer(Kilometer)
  , Decimeter(Decimeter)
  , Decameter(Decameter)
  , Hectometer(Hectometer)
  , Megameter(Megameter)
  , Gigameter(Gigameter)
  , Terameter(Terameter)
  , Petameter(Petameter)
  , Exameter(Exameter)
  , Zettameter(Zettameter)
  , Yottameter(Yottameter)
  , Ronnameter(Ronnameter)
  , Quettameter(Quettameter)
  , Micrometer(Micrometer)
  , Nanometer(Nanometer)
  , meter
  , meters
  , millimeter
  , millimeters
  , centimeter
  , centimeters
  , kilometer
  , kilometers
  , decimeter
  , decimeters
  , decameter
  , decameters
  , hectometer
  , hectometers
  , megameter
  , megameters
  , gigameter
  , gigameters
  , terameter
  , terameters
  , petameter
  , petameters
  , exameter
  , exameters
  , zettameter
  , zettameters
  , yottameter
  , yottameters
  , ronnameter
  , ronnameters
  , quettameter
  , quettameters
  , micrometer
  , micrometers
  , nanometer
  , nanometers
  , unwrapMeter
  , unwrapMillimeter
  , unwrapCentimeter
  , unwrapKilometer
  , unwrapDecimeter
  , unwrapDecameter
  , unwrapHectometer
  , unwrapMegameter
  , unwrapGigameter
  , unwrapTerameter
  , unwrapPetameter
  , unwrapExameter
  , unwrapZettameter
  , unwrapYottameter
  , unwrapRonnameter
  , unwrapQuettameter
  , unwrapMicrometer
  , unwrapNanometer
  , addMeters
  , subtractMeters
  , scaleMeters
  , negateMeters
  ) as SI

import Hydrogen.Schema.Dimension.Physical.Imperial
  ( Thou(Thou)
  , Inch(Inch)
  , Foot(Foot)
  , Yard(Yard)
  , Mile(Mile)
  , Fathom(Fathom)
  , Chain(Chain)
  , Furlong(Furlong)
  , League(League)
  , NauticalMile(NauticalMile)
  , thou
  , thou_
  , inch
  , inches
  , foot
  , feet
  , yard
  , yards
  , mile
  , miles
  , fathom
  , fathoms
  , chain
  , chains
  , furlong
  , furlongs
  , league
  , leagues
  , nauticalMile
  , nauticalMiles
  , unwrapThou
  , unwrapInch
  , unwrapFoot
  , unwrapYard
  , unwrapMile
  , unwrapFathom
  , unwrapChain
  , unwrapFurlong
  , unwrapLeague
  , unwrapNauticalMile
  , metersPerInch
  , metersPerFoot
  , metersPerYard
  , metersPerMile
  , metersPerFathom
  , metersPerChain
  , metersPerFurlong
  , metersPerLeague
  , metersPerNauticalMile
  ) as Imperial

import Hydrogen.Schema.Dimension.Physical.Typographic
  ( Point(Point)
  , Pica(Pica)
  , Didot(Didot)
  , Cicero(Cicero)
  , Twip(Twip)
  , Agate(Agate)
  , point
  , points
  , pica
  , picas
  , didot
  , didots
  , cicero
  , ciceros
  , twip
  , twips
  , agate
  , agates
  , unwrapPoint
  , unwrapPica
  , unwrapDidot
  , unwrapCicero
  , unwrapTwip
  , unwrapAgate
  , metersPerPoint
  , metersPerPica
  , metersPerDidot
  , metersPerCicero
  , metersPerTwip
  , metersPerAgate
  ) as Typographic

import Hydrogen.Schema.Dimension.Physical.Atomic
  ( Picometer(Picometer)
  , Femtometer(Femtometer)
  , Angstrom(Angstrom)
  , BohrRadius(BohrRadius)
  , Fermi(Fermi)
  , PlanckLength(PlanckLength)
  , picometer
  , picometers
  , femtometer
  , femtometers
  , angstrom
  , angstroms
  , bohrRadius
  , fermi
  , fermis
  , planckLength
  , unwrapPicometer
  , unwrapFemtometer
  , unwrapAngstrom
  , unwrapBohrRadius
  , unwrapFermi
  , unwrapPlanckLength
  ) as Atomic

import Hydrogen.Schema.Dimension.Physical.Astronomical
  ( LightYear(LightYear)
  , Parsec(Parsec)
  , AstronomicalUnit(AstronomicalUnit)
  , Kiloparsec(Kiloparsec)
  , Megaparsec(Megaparsec)
  , LightSecond(LightSecond)
  , LightMinute(LightMinute)
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
  , unwrapLightYear
  , unwrapParsec
  , unwrapAU
  , unwrapKiloparsec
  , unwrapMegaparsec
  , unwrapLightSecond
  , unwrapLightMinute
  , speedOfLight
  , metersPerLightYear
  , metersPerParsec
  , metersPerAU
  ) as Astronomical

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // type class
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type class for physical length units.
-- | All conversions go through Meter as the canonical representation.
class PhysicalLength a where
  toMeters :: a -> SI.Meter
  fromMeters :: SI.Meter -> a

-- ─────────────────────────────────────────────────────────────────────────────
--                                                              // SI instances
-- ─────────────────────────────────────────────────────────────────────────────

instance physicalLengthMeter :: PhysicalLength SI.Meter where
  toMeters = identity
  fromMeters = identity

instance physicalLengthMillimeter :: PhysicalLength SI.Millimeter where
  toMeters (SI.Millimeter n) = SI.Meter (n / 1000.0)
  fromMeters (SI.Meter n) = SI.Millimeter (n * 1000.0)

instance physicalLengthCentimeter :: PhysicalLength SI.Centimeter where
  toMeters (SI.Centimeter n) = SI.Meter (n / 100.0)
  fromMeters (SI.Meter n) = SI.Centimeter (n * 100.0)

instance physicalLengthDecimeter :: PhysicalLength SI.Decimeter where
  toMeters (SI.Decimeter n) = SI.Meter (n / 10.0)
  fromMeters (SI.Meter n) = SI.Decimeter (n * 10.0)

instance physicalLengthDecameter :: PhysicalLength SI.Decameter where
  toMeters (SI.Decameter n) = SI.Meter (n * 10.0)
  fromMeters (SI.Meter n) = SI.Decameter (n / 10.0)

instance physicalLengthHectometer :: PhysicalLength SI.Hectometer where
  toMeters (SI.Hectometer n) = SI.Meter (n * 100.0)
  fromMeters (SI.Meter n) = SI.Hectometer (n / 100.0)

instance physicalLengthKilometer :: PhysicalLength SI.Kilometer where
  toMeters (SI.Kilometer n) = SI.Meter (n * 1000.0)
  fromMeters (SI.Meter n) = SI.Kilometer (n / 1000.0)

instance physicalLengthMegameter :: PhysicalLength SI.Megameter where
  toMeters (SI.Megameter n) = SI.Meter (n * 1.0e6)
  fromMeters (SI.Meter n) = SI.Megameter (n / 1.0e6)

instance physicalLengthGigameter :: PhysicalLength SI.Gigameter where
  toMeters (SI.Gigameter n) = SI.Meter (n * 1.0e9)
  fromMeters (SI.Meter n) = SI.Gigameter (n / 1.0e9)

instance physicalLengthTerameter :: PhysicalLength SI.Terameter where
  toMeters (SI.Terameter n) = SI.Meter (n * 1.0e12)
  fromMeters (SI.Meter n) = SI.Terameter (n / 1.0e12)

instance physicalLengthPetameter :: PhysicalLength SI.Petameter where
  toMeters (SI.Petameter n) = SI.Meter (n * 1.0e15)
  fromMeters (SI.Meter n) = SI.Petameter (n / 1.0e15)

instance physicalLengthExameter :: PhysicalLength SI.Exameter where
  toMeters (SI.Exameter n) = SI.Meter (n * 1.0e18)
  fromMeters (SI.Meter n) = SI.Exameter (n / 1.0e18)

instance physicalLengthZettameter :: PhysicalLength SI.Zettameter where
  toMeters (SI.Zettameter n) = SI.Meter (n * 1.0e21)
  fromMeters (SI.Meter n) = SI.Zettameter (n / 1.0e21)

instance physicalLengthYottameter :: PhysicalLength SI.Yottameter where
  toMeters (SI.Yottameter n) = SI.Meter (n * 1.0e24)
  fromMeters (SI.Meter n) = SI.Yottameter (n / 1.0e24)

instance physicalLengthRonnameter :: PhysicalLength SI.Ronnameter where
  toMeters (SI.Ronnameter n) = SI.Meter (n * 1.0e27)
  fromMeters (SI.Meter n) = SI.Ronnameter (n / 1.0e27)

instance physicalLengthQuettameter :: PhysicalLength SI.Quettameter where
  toMeters (SI.Quettameter n) = SI.Meter (n * 1.0e30)
  fromMeters (SI.Meter n) = SI.Quettameter (n / 1.0e30)

instance physicalLengthMicrometer :: PhysicalLength SI.Micrometer where
  toMeters (SI.Micrometer n) = SI.Meter (n * 1.0e-6)
  fromMeters (SI.Meter n) = SI.Micrometer (n / 1.0e-6)

instance physicalLengthNanometer :: PhysicalLength SI.Nanometer where
  toMeters (SI.Nanometer n) = SI.Meter (n * 1.0e-9)
  fromMeters (SI.Meter n) = SI.Nanometer (n / 1.0e-9)

-- ─────────────────────────────────────────────────────────────────────────────
--                                                          // Imperial instances
-- ─────────────────────────────────────────────────────────────────────────────

instance physicalLengthThou :: PhysicalLength Imperial.Thou where
  toMeters (Imperial.Thou n) = SI.Meter (n * Imperial.metersPerInch / 1000.0)
  fromMeters (SI.Meter n) = Imperial.Thou (n * 1000.0 / Imperial.metersPerInch)

instance physicalLengthInch :: PhysicalLength Imperial.Inch where
  toMeters (Imperial.Inch n) = SI.Meter (n * Imperial.metersPerInch)
  fromMeters (SI.Meter n) = Imperial.Inch (n / Imperial.metersPerInch)

instance physicalLengthFoot :: PhysicalLength Imperial.Foot where
  toMeters (Imperial.Foot n) = SI.Meter (n * Imperial.metersPerFoot)
  fromMeters (SI.Meter n) = Imperial.Foot (n / Imperial.metersPerFoot)

instance physicalLengthYard :: PhysicalLength Imperial.Yard where
  toMeters (Imperial.Yard n) = SI.Meter (n * Imperial.metersPerYard)
  fromMeters (SI.Meter n) = Imperial.Yard (n / Imperial.metersPerYard)

instance physicalLengthMile :: PhysicalLength Imperial.Mile where
  toMeters (Imperial.Mile n) = SI.Meter (n * Imperial.metersPerMile)
  fromMeters (SI.Meter n) = Imperial.Mile (n / Imperial.metersPerMile)

instance physicalLengthFathom :: PhysicalLength Imperial.Fathom where
  toMeters (Imperial.Fathom n) = SI.Meter (n * Imperial.metersPerFathom)
  fromMeters (SI.Meter n) = Imperial.Fathom (n / Imperial.metersPerFathom)

instance physicalLengthChain :: PhysicalLength Imperial.Chain where
  toMeters (Imperial.Chain n) = SI.Meter (n * Imperial.metersPerChain)
  fromMeters (SI.Meter n) = Imperial.Chain (n / Imperial.metersPerChain)

instance physicalLengthFurlong :: PhysicalLength Imperial.Furlong where
  toMeters (Imperial.Furlong n) = SI.Meter (n * Imperial.metersPerFurlong)
  fromMeters (SI.Meter n) = Imperial.Furlong (n / Imperial.metersPerFurlong)

instance physicalLengthLeague :: PhysicalLength Imperial.League where
  toMeters (Imperial.League n) = SI.Meter (n * Imperial.metersPerLeague)
  fromMeters (SI.Meter n) = Imperial.League (n / Imperial.metersPerLeague)

instance physicalLengthNauticalMile :: PhysicalLength Imperial.NauticalMile where
  toMeters (Imperial.NauticalMile n) = SI.Meter (n * Imperial.metersPerNauticalMile)
  fromMeters (SI.Meter n) = Imperial.NauticalMile (n / Imperial.metersPerNauticalMile)

-- ─────────────────────────────────────────────────────────────────────────────
--                                                      // Typographic instances
-- ─────────────────────────────────────────────────────────────────────────────

instance physicalLengthPoint :: PhysicalLength Typographic.Point where
  toMeters (Typographic.Point n) = SI.Meter (n * Typographic.metersPerPoint)
  fromMeters (SI.Meter n) = Typographic.Point (n / Typographic.metersPerPoint)

instance physicalLengthPica :: PhysicalLength Typographic.Pica where
  toMeters (Typographic.Pica n) = SI.Meter (n * Typographic.metersPerPica)
  fromMeters (SI.Meter n) = Typographic.Pica (n / Typographic.metersPerPica)

instance physicalLengthDidot :: PhysicalLength Typographic.Didot where
  toMeters (Typographic.Didot n) = SI.Meter (n * Typographic.metersPerDidot)
  fromMeters (SI.Meter n) = Typographic.Didot (n / Typographic.metersPerDidot)

instance physicalLengthCicero :: PhysicalLength Typographic.Cicero where
  toMeters (Typographic.Cicero n) = SI.Meter (n * Typographic.metersPerCicero)
  fromMeters (SI.Meter n) = Typographic.Cicero (n / Typographic.metersPerCicero)

instance physicalLengthTwip :: PhysicalLength Typographic.Twip where
  toMeters (Typographic.Twip n) = SI.Meter (n * Typographic.metersPerTwip)
  fromMeters (SI.Meter n) = Typographic.Twip (n / Typographic.metersPerTwip)

instance physicalLengthAgate :: PhysicalLength Typographic.Agate where
  toMeters (Typographic.Agate n) = SI.Meter (n * Typographic.metersPerAgate)
  fromMeters (SI.Meter n) = Typographic.Agate (n / Typographic.metersPerAgate)

-- ─────────────────────────────────────────────────────────────────────────────
--                                                          // Atomic instances
-- ─────────────────────────────────────────────────────────────────────────────

instance physicalLengthPicometer :: PhysicalLength Atomic.Picometer where
  toMeters (Atomic.Picometer n) = SI.Meter (n * 1.0e-12)
  fromMeters (SI.Meter n) = Atomic.Picometer (n / 1.0e-12)

instance physicalLengthFemtometer :: PhysicalLength Atomic.Femtometer where
  toMeters (Atomic.Femtometer n) = SI.Meter (n * 1.0e-15)
  fromMeters (SI.Meter n) = Atomic.Femtometer (n / 1.0e-15)

instance physicalLengthAngstrom :: PhysicalLength Atomic.Angstrom where
  toMeters (Atomic.Angstrom n) = SI.Meter (n * 1.0e-10)
  fromMeters (SI.Meter n) = Atomic.Angstrom (n / 1.0e-10)

instance physicalLengthBohrRadius :: PhysicalLength Atomic.BohrRadius where
  toMeters (Atomic.BohrRadius n) = SI.Meter (n * 5.29177210903e-11)
  fromMeters (SI.Meter n) = Atomic.BohrRadius (n / 5.29177210903e-11)

instance physicalLengthFermi :: PhysicalLength Atomic.Fermi where
  toMeters (Atomic.Fermi n) = SI.Meter (n * 1.0e-15)
  fromMeters (SI.Meter n) = Atomic.Fermi (n / 1.0e-15)

instance physicalLengthPlanckLength :: PhysicalLength Atomic.PlanckLength where
  toMeters (Atomic.PlanckLength n) = SI.Meter (n * 1.616255e-35)
  fromMeters (SI.Meter n) = Atomic.PlanckLength (n / 1.616255e-35)

-- ─────────────────────────────────────────────────────────────────────────────
--                                                    // Astronomical instances
-- ─────────────────────────────────────────────────────────────────────────────

instance physicalLengthLightYear :: PhysicalLength Astronomical.LightYear where
  toMeters (Astronomical.LightYear n) = SI.Meter (n * Astronomical.metersPerLightYear)
  fromMeters (SI.Meter n) = Astronomical.LightYear (n / Astronomical.metersPerLightYear)

instance physicalLengthParsec :: PhysicalLength Astronomical.Parsec where
  toMeters (Astronomical.Parsec n) = SI.Meter (n * Astronomical.metersPerParsec)
  fromMeters (SI.Meter n) = Astronomical.Parsec (n / Astronomical.metersPerParsec)

instance physicalLengthAU :: PhysicalLength Astronomical.AstronomicalUnit where
  toMeters (Astronomical.AstronomicalUnit n) = SI.Meter (n * Astronomical.metersPerAU)
  fromMeters (SI.Meter n) = Astronomical.AstronomicalUnit (n / Astronomical.metersPerAU)

instance physicalLengthKiloparsec :: PhysicalLength Astronomical.Kiloparsec where
  toMeters (Astronomical.Kiloparsec n) = SI.Meter (n * Astronomical.metersPerParsec * 1000.0)
  fromMeters (SI.Meter n) = Astronomical.Kiloparsec (n / Astronomical.metersPerParsec / 1000.0)

instance physicalLengthMegaparsec :: PhysicalLength Astronomical.Megaparsec where
  toMeters (Astronomical.Megaparsec n) = SI.Meter (n * Astronomical.metersPerParsec * 1.0e6)
  fromMeters (SI.Meter n) = Astronomical.Megaparsec (n / Astronomical.metersPerParsec / 1.0e6)

instance physicalLengthLightSecond :: PhysicalLength Astronomical.LightSecond where
  toMeters (Astronomical.LightSecond n) = SI.Meter (n * Astronomical.speedOfLight)
  fromMeters (SI.Meter n) = Astronomical.LightSecond (n / Astronomical.speedOfLight)

instance physicalLengthLightMinute :: PhysicalLength Astronomical.LightMinute where
  toMeters (Astronomical.LightMinute n) = SI.Meter (n * Astronomical.speedOfLight * 60.0)
  fromMeters (SI.Meter n) = Astronomical.LightMinute (n / Astronomical.speedOfLight / 60.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // generic conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert between any two physical length units.
-- | Goes through Meter as canonical representation.
convert :: forall a b. PhysicalLength a => PhysicalLength b => a -> b
convert = fromMeters <<< toMeters
