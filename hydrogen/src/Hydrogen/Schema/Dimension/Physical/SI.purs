-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // dimension // physical // si
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | SI (International System of Units) length units.
-- |
-- | The meter is the SI base unit of length, defined as the distance light
-- | travels in vacuum in 1/299,792,458 of a second.
-- |
-- | ## Authority
-- | BIPM (Bureau International des Poids et Mesures) - bipm.org
-- |
-- | ## Prefixes
-- | Full SI prefix coverage from yocto (10^-24) to quetta (10^30).
-- | Ronna (10^27) and Quetta (10^30) were added in 2022.

module Hydrogen.Schema.Dimension.Physical.SI
  ( -- * Base Unit
    Meter(Meter)
  
  -- * Larger Than Meter
  , Decameter(Decameter)
  , Hectometer(Hectometer)
  , Kilometer(Kilometer)
  , Megameter(Megameter)
  , Gigameter(Gigameter)
  , Terameter(Terameter)
  , Petameter(Petameter)
  , Exameter(Exameter)
  , Zettameter(Zettameter)
  , Yottameter(Yottameter)
  , Ronnameter(Ronnameter)
  , Quettameter(Quettameter)
  
  -- * Smaller Than Meter
  , Decimeter(Decimeter)
  , Centimeter(Centimeter)
  , Millimeter(Millimeter)
  , Micrometer(Micrometer)
  , Nanometer(Nanometer)
  
  -- * Constructors (Base)
  , meter
  , meters
  
  -- * Constructors (Larger)
  , decameter
  , decameters
  , hectometer
  , hectometers
  , kilometer
  , kilometers
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
  
  -- * Constructors (Smaller)
  , decimeter
  , decimeters
  , centimeter
  , centimeters
  , millimeter
  , millimeters
  , micrometer
  , micrometers
  , nanometer
  , nanometers
  
  -- * Accessors
  , unwrapMeter
  , unwrapDecameter
  , unwrapHectometer
  , unwrapKilometer
  , unwrapMegameter
  , unwrapGigameter
  , unwrapTerameter
  , unwrapPetameter
  , unwrapExameter
  , unwrapZettameter
  , unwrapYottameter
  , unwrapRonnameter
  , unwrapQuettameter
  , unwrapDecimeter
  , unwrapCentimeter
  , unwrapMillimeter
  , unwrapMicrometer
  , unwrapNanometer
  
  -- * Conversions to Meter
  , decametersToMeters
  , hectometersToMeters
  , kilometersToMeters
  , megametersToMeters
  , gigametersToMeters
  , terametersToMeters
  , petametersToMeters
  , exametersToMeters
  , zettametersToMeters
  , yottametersToMeters
  , ronnametersToMeters
  , quettametersToMeters
  , decimetersToMeters
  , centimetersToMeters
  , millimetersToMeters
  , micrometersToMeters
  , nanometersToMeters
  
  -- * Operations
  , addMeters
  , subtractMeters
  , scaleMeters
  , negateMeters
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Ring
  , class Semiring
  , class Show
  , negate
  , show
  , (+)
  , (-)
  , (*)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // meter (base)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Meter - SI base unit of length
-- | Defined as the distance light travels in vacuum in 1/299,792,458 seconds
newtype Meter = Meter Number

derive instance eqMeter :: Eq Meter
derive instance ordMeter :: Ord Meter

instance showMeter :: Show Meter where
  show (Meter n) = show n <> " m"

instance semiringMeter :: Semiring Meter where
  add (Meter a) (Meter b) = Meter (a + b)
  zero = Meter 0.0
  mul (Meter a) (Meter b) = Meter (a * b)
  one = Meter 1.0

instance ringMeter :: Ring Meter where
  sub (Meter a) (Meter b) = Meter (a - b)

meter :: Number -> Meter
meter = Meter

meters :: Number -> Meter
meters = Meter

unwrapMeter :: Meter -> Number
unwrapMeter (Meter n) = n

addMeters :: Meter -> Meter -> Meter
addMeters (Meter a) (Meter b) = Meter (a + b)

subtractMeters :: Meter -> Meter -> Meter
subtractMeters (Meter a) (Meter b) = Meter (a - b)

scaleMeters :: Number -> Meter -> Meter
scaleMeters factor (Meter n) = Meter (n * factor)

negateMeters :: Meter -> Meter
negateMeters (Meter n) = Meter (negate n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // decameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Decameter - 10 meters (da, rarely used)
newtype Decameter = Decameter Number

derive instance eqDecameter :: Eq Decameter
derive instance ordDecameter :: Ord Decameter

instance showDecameter :: Show Decameter where
  show (Decameter n) = show n <> " dam"

decameter :: Number -> Decameter
decameter = Decameter

decameters :: Number -> Decameter
decameters = Decameter

unwrapDecameter :: Decameter -> Number
unwrapDecameter (Decameter n) = n

decametersToMeters :: Decameter -> Number
decametersToMeters (Decameter n) = n * 10.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // hectometer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hectometer - 100 meters (h, rarely used)
newtype Hectometer = Hectometer Number

derive instance eqHectometer :: Eq Hectometer
derive instance ordHectometer :: Ord Hectometer

instance showHectometer :: Show Hectometer where
  show (Hectometer n) = show n <> " hm"

hectometer :: Number -> Hectometer
hectometer = Hectometer

hectometers :: Number -> Hectometer
hectometers = Hectometer

unwrapHectometer :: Hectometer -> Number
unwrapHectometer (Hectometer n) = n

hectometersToMeters :: Hectometer -> Number
hectometersToMeters (Hectometer n) = n * 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // kilometer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Kilometer - 1000 meters
newtype Kilometer = Kilometer Number

derive instance eqKilometer :: Eq Kilometer
derive instance ordKilometer :: Ord Kilometer

instance showKilometer :: Show Kilometer where
  show (Kilometer n) = show n <> " km"

kilometer :: Number -> Kilometer
kilometer = Kilometer

kilometers :: Number -> Kilometer
kilometers = Kilometer

unwrapKilometer :: Kilometer -> Number
unwrapKilometer (Kilometer n) = n

kilometersToMeters :: Kilometer -> Number
kilometersToMeters (Kilometer n) = n * 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // megameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Megameter - 10^6 meters (1000 km)
newtype Megameter = Megameter Number

derive instance eqMegameter :: Eq Megameter
derive instance ordMegameter :: Ord Megameter

instance showMegameter :: Show Megameter where
  show (Megameter n) = show n <> " Mm"

megameter :: Number -> Megameter
megameter = Megameter

megameters :: Number -> Megameter
megameters = Megameter

unwrapMegameter :: Megameter -> Number
unwrapMegameter (Megameter n) = n

megametersToMeters :: Megameter -> Number
megametersToMeters (Megameter n) = n * 1.0e6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // gigameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gigameter - 10^9 meters
newtype Gigameter = Gigameter Number

derive instance eqGigameter :: Eq Gigameter
derive instance ordGigameter :: Ord Gigameter

instance showGigameter :: Show Gigameter where
  show (Gigameter n) = show n <> " Gm"

gigameter :: Number -> Gigameter
gigameter = Gigameter

gigameters :: Number -> Gigameter
gigameters = Gigameter

unwrapGigameter :: Gigameter -> Number
unwrapGigameter (Gigameter n) = n

gigametersToMeters :: Gigameter -> Number
gigametersToMeters (Gigameter n) = n * 1.0e9

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // terameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Terameter - 10^12 meters
newtype Terameter = Terameter Number

derive instance eqTerameter :: Eq Terameter
derive instance ordTerameter :: Ord Terameter

instance showTerameter :: Show Terameter where
  show (Terameter n) = show n <> " Tm"

terameter :: Number -> Terameter
terameter = Terameter

terameters :: Number -> Terameter
terameters = Terameter

unwrapTerameter :: Terameter -> Number
unwrapTerameter (Terameter n) = n

terametersToMeters :: Terameter -> Number
terametersToMeters (Terameter n) = n * 1.0e12

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // petameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Petameter - 10^15 meters
newtype Petameter = Petameter Number

derive instance eqPetameter :: Eq Petameter
derive instance ordPetameter :: Ord Petameter

instance showPetameter :: Show Petameter where
  show (Petameter n) = show n <> " Pm"

petameter :: Number -> Petameter
petameter = Petameter

petameters :: Number -> Petameter
petameters = Petameter

unwrapPetameter :: Petameter -> Number
unwrapPetameter (Petameter n) = n

petametersToMeters :: Petameter -> Number
petametersToMeters (Petameter n) = n * 1.0e15

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // exameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Exameter - 10^18 meters
newtype Exameter = Exameter Number

derive instance eqExameter :: Eq Exameter
derive instance ordExameter :: Ord Exameter

instance showExameter :: Show Exameter where
  show (Exameter n) = show n <> " Em"

exameter :: Number -> Exameter
exameter = Exameter

exameters :: Number -> Exameter
exameters = Exameter

unwrapExameter :: Exameter -> Number
unwrapExameter (Exameter n) = n

exametersToMeters :: Exameter -> Number
exametersToMeters (Exameter n) = n * 1.0e18

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // zettameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zettameter - 10^21 meters
newtype Zettameter = Zettameter Number

derive instance eqZettameter :: Eq Zettameter
derive instance ordZettameter :: Ord Zettameter

instance showZettameter :: Show Zettameter where
  show (Zettameter n) = show n <> " Zm"

zettameter :: Number -> Zettameter
zettameter = Zettameter

zettameters :: Number -> Zettameter
zettameters = Zettameter

unwrapZettameter :: Zettameter -> Number
unwrapZettameter (Zettameter n) = n

zettametersToMeters :: Zettameter -> Number
zettametersToMeters (Zettameter n) = n * 1.0e21

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // yottameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Yottameter - 10^24 meters
newtype Yottameter = Yottameter Number

derive instance eqYottameter :: Eq Yottameter
derive instance ordYottameter :: Ord Yottameter

instance showYottameter :: Show Yottameter where
  show (Yottameter n) = show n <> " Ym"

yottameter :: Number -> Yottameter
yottameter = Yottameter

yottameters :: Number -> Yottameter
yottameters = Yottameter

unwrapYottameter :: Yottameter -> Number
unwrapYottameter (Yottameter n) = n

yottametersToMeters :: Yottameter -> Number
yottametersToMeters (Yottameter n) = n * 1.0e24

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // ronnameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ronnameter - 10^27 meters (added 2022)
newtype Ronnameter = Ronnameter Number

derive instance eqRonnameter :: Eq Ronnameter
derive instance ordRonnameter :: Ord Ronnameter

instance showRonnameter :: Show Ronnameter where
  show (Ronnameter n) = show n <> " Rm"

ronnameter :: Number -> Ronnameter
ronnameter = Ronnameter

ronnameters :: Number -> Ronnameter
ronnameters = Ronnameter

unwrapRonnameter :: Ronnameter -> Number
unwrapRonnameter (Ronnameter n) = n

ronnametersToMeters :: Ronnameter -> Number
ronnametersToMeters (Ronnameter n) = n * 1.0e27

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // quettameter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Quettameter - 10^30 meters (added 2022, largest SI prefix)
newtype Quettameter = Quettameter Number

derive instance eqQuettameter :: Eq Quettameter
derive instance ordQuettameter :: Ord Quettameter

instance showQuettameter :: Show Quettameter where
  show (Quettameter n) = show n <> " Qm"

quettameter :: Number -> Quettameter
quettameter = Quettameter

quettameters :: Number -> Quettameter
quettameters = Quettameter

unwrapQuettameter :: Quettameter -> Number
unwrapQuettameter (Quettameter n) = n

quettametersToMeters :: Quettameter -> Number
quettametersToMeters (Quettameter n) = n * 1.0e30

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // decimeter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Decimeter - 0.1 meters
newtype Decimeter = Decimeter Number

derive instance eqDecimeter :: Eq Decimeter
derive instance ordDecimeter :: Ord Decimeter

instance showDecimeter :: Show Decimeter where
  show (Decimeter n) = show n <> " dm"

decimeter :: Number -> Decimeter
decimeter = Decimeter

decimeters :: Number -> Decimeter
decimeters = Decimeter

unwrapDecimeter :: Decimeter -> Number
unwrapDecimeter (Decimeter n) = n

decimetersToMeters :: Decimeter -> Number
decimetersToMeters (Decimeter n) = n * 0.1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // centimeter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Centimeter - 0.01 meters
newtype Centimeter = Centimeter Number

derive instance eqCentimeter :: Eq Centimeter
derive instance ordCentimeter :: Ord Centimeter

instance showCentimeter :: Show Centimeter where
  show (Centimeter n) = show n <> " cm"

centimeter :: Number -> Centimeter
centimeter = Centimeter

centimeters :: Number -> Centimeter
centimeters = Centimeter

unwrapCentimeter :: Centimeter -> Number
unwrapCentimeter (Centimeter n) = n

centimetersToMeters :: Centimeter -> Number
centimetersToMeters (Centimeter n) = n * 0.01

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // millimeter
-- ═════════════════════════════════════════════════════════════════════════════

-- | Millimeter - 0.001 meters
newtype Millimeter = Millimeter Number

derive instance eqMillimeter :: Eq Millimeter
derive instance ordMillimeter :: Ord Millimeter

instance showMillimeter :: Show Millimeter where
  show (Millimeter n) = show n <> " mm"

millimeter :: Number -> Millimeter
millimeter = Millimeter

millimeters :: Number -> Millimeter
millimeters = Millimeter

unwrapMillimeter :: Millimeter -> Number
unwrapMillimeter (Millimeter n) = n

millimetersToMeters :: Millimeter -> Number
millimetersToMeters (Millimeter n) = n * 0.001

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // micrometer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Micrometer (micron) - 10^-6 meters
newtype Micrometer = Micrometer Number

derive instance eqMicrometer :: Eq Micrometer
derive instance ordMicrometer :: Ord Micrometer

instance showMicrometer :: Show Micrometer where
  show (Micrometer n) = show n <> " µm"

micrometer :: Number -> Micrometer
micrometer = Micrometer

micrometers :: Number -> Micrometer
micrometers = Micrometer

unwrapMicrometer :: Micrometer -> Number
unwrapMicrometer (Micrometer n) = n

micrometersToMeters :: Micrometer -> Number
micrometersToMeters (Micrometer n) = n * 1.0e-6

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // nanometer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Nanometer - 10^-9 meters
newtype Nanometer = Nanometer Number

derive instance eqNanometer :: Eq Nanometer
derive instance ordNanometer :: Ord Nanometer

instance showNanometer :: Show Nanometer where
  show (Nanometer n) = show n <> " nm"

nanometer :: Number -> Nanometer
nanometer = Nanometer

nanometers :: Number -> Nanometer
nanometers = Nanometer

unwrapNanometer :: Nanometer -> Number
unwrapNanometer (Nanometer n) = n

nanometersToMeters :: Nanometer -> Number
nanometersToMeters (Nanometer n) = n * 1.0e-9
