-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                    // hydrogen // schema // dimension // physical // imperial
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Imperial length units.
-- |
-- | Traditional units from the British Imperial and US customary systems.
-- | All conversions go through Meter as the canonical SI representation.
-- |
-- | ## Conversion Authority
-- | The International Yard and Pound Agreement (1959) defines:
-- | - 1 inch = 25.4 mm exactly
-- | - 1 yard = 0.9144 m exactly
-- |
-- | All other imperial units derive from these definitions.

module Hydrogen.Schema.Dimension.Physical.Imperial
  ( -- * Types
    Thou(Thou)
  , Inch(Inch)
  , Foot(Foot)
  , Yard(Yard)
  , Mile(Mile)
  , Fathom(Fathom)
  , Chain(Chain)
  , Furlong(Furlong)
  , League(League)
  , NauticalMile(NauticalMile)
  
  -- * Constructors
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
  
  -- * Accessors
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
  
  -- * Conversions to Meter
  , thouToMeters
  , inchesToMeters
  , feetToMeters
  , yardsToMeters
  , milesToMeters
  , fathomsToMeters
  , chainsToMeters
  , furlongsToMeters
  , leaguesToMeters
  , nauticalMilesToMeters
  
  -- * Conversion Constants
  , metersPerInch
  , metersPerFoot
  , metersPerYard
  , metersPerMile
  , metersPerFathom
  , metersPerChain
  , metersPerFurlong
  , metersPerLeague
  , metersPerNauticalMile
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (*)
  , (/)
  , (<>)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Meters per inch (exact by definition, 1959)
metersPerInch :: Number
metersPerInch = 0.0254

-- | Meters per foot (12 inches)
metersPerFoot :: Number
metersPerFoot = 0.3048

-- | Meters per yard (3 feet, exact by definition)
metersPerYard :: Number
metersPerYard = 0.9144

-- | Meters per mile (5280 feet)
metersPerMile :: Number
metersPerMile = 1609.344

-- | Meters per fathom (6 feet)
metersPerFathom :: Number
metersPerFathom = 1.8288

-- | Meters per chain (66 feet, surveying)
metersPerChain :: Number
metersPerChain = 20.1168

-- | Meters per furlong (660 feet, 10 chains)
metersPerFurlong :: Number
metersPerFurlong = 201.168

-- | Meters per league (3 miles)
metersPerLeague :: Number
metersPerLeague = 4828.032

-- | Meters per nautical mile (1852 m exactly, by definition)
metersPerNauticalMile :: Number
metersPerNauticalMile = 1852.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // thou (mil)
-- ═════════════════════════════════════════════════════════════════════════════

-- | Thou (mil) - 1/1000 inch
-- | Used in engineering for thin materials, tolerances
newtype Thou = Thou Number

derive instance eqThou :: Eq Thou
derive instance ordThou :: Ord Thou

instance showThou :: Show Thou where
  show (Thou n) = show n <> " mil"

thou :: Number -> Thou
thou = Thou

thou_ :: Number -> Thou
thou_ = Thou

unwrapThou :: Thou -> Number
unwrapThou (Thou n) = n

thouToMeters :: Thou -> Number
thouToMeters (Thou n) = n * metersPerInch / 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // inch
-- ═════════════════════════════════════════════════════════════════════════════

-- | Inch - exactly 25.4 mm (by international agreement, 1959)
newtype Inch = Inch Number

derive instance eqInch :: Eq Inch
derive instance ordInch :: Ord Inch

instance showInch :: Show Inch where
  show (Inch n) = show n <> " in"

inch :: Number -> Inch
inch = Inch

inches :: Number -> Inch
inches = Inch

unwrapInch :: Inch -> Number
unwrapInch (Inch n) = n

inchesToMeters :: Inch -> Number
inchesToMeters (Inch n) = n * metersPerInch

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // foot
-- ═════════════════════════════════════════════════════════════════════════════

-- | Foot - 12 inches
newtype Foot = Foot Number

derive instance eqFoot :: Eq Foot
derive instance ordFoot :: Ord Foot

instance showFoot :: Show Foot where
  show (Foot n) = show n <> " ft"

foot :: Number -> Foot
foot = Foot

feet :: Number -> Foot
feet = Foot

unwrapFoot :: Foot -> Number
unwrapFoot (Foot n) = n

feetToMeters :: Foot -> Number
feetToMeters (Foot n) = n * metersPerFoot

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // yard
-- ═════════════════════════════════════════════════════════════════════════════

-- | Yard - 3 feet (exact by international definition)
newtype Yard = Yard Number

derive instance eqYard :: Eq Yard
derive instance ordYard :: Ord Yard

instance showYard :: Show Yard where
  show (Yard n) = show n <> " yd"

yard :: Number -> Yard
yard = Yard

yards :: Number -> Yard
yards = Yard

unwrapYard :: Yard -> Number
unwrapYard (Yard n) = n

yardsToMeters :: Yard -> Number
yardsToMeters (Yard n) = n * metersPerYard

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // mile
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mile - 5280 feet
newtype Mile = Mile Number

derive instance eqMile :: Eq Mile
derive instance ordMile :: Ord Mile

instance showMile :: Show Mile where
  show (Mile n) = show n <> " mi"

mile :: Number -> Mile
mile = Mile

miles :: Number -> Mile
miles = Mile

unwrapMile :: Mile -> Number
unwrapMile (Mile n) = n

milesToMeters :: Mile -> Number
milesToMeters (Mile n) = n * metersPerMile

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // fathom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fathom - 6 feet (nautical depth measurement)
newtype Fathom = Fathom Number

derive instance eqFathom :: Eq Fathom
derive instance ordFathom :: Ord Fathom

instance showFathom :: Show Fathom where
  show (Fathom n) = show n <> " ftm"

fathom :: Number -> Fathom
fathom = Fathom

fathoms :: Number -> Fathom
fathoms = Fathom

unwrapFathom :: Fathom -> Number
unwrapFathom (Fathom n) = n

fathomsToMeters :: Fathom -> Number
fathomsToMeters (Fathom n) = n * metersPerFathom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // chain
-- ═════════════════════════════════════════════════════════════════════════════

-- | Chain - 66 feet (surveying, Gunter's chain)
-- | 80 chains = 1 mile, 10 chains = 1 furlong
newtype Chain = Chain Number

derive instance eqChain :: Eq Chain
derive instance ordChain :: Ord Chain

instance showChain :: Show Chain where
  show (Chain n) = show n <> " ch"

chain :: Number -> Chain
chain = Chain

chains :: Number -> Chain
chains = Chain

unwrapChain :: Chain -> Number
unwrapChain (Chain n) = n

chainsToMeters :: Chain -> Number
chainsToMeters (Chain n) = n * metersPerChain

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // furlong
-- ═════════════════════════════════════════════════════════════════════════════

-- | Furlong - 660 feet (10 chains, 1/8 mile)
-- | Originally the length of a furrow in a plowed field
newtype Furlong = Furlong Number

derive instance eqFurlong :: Eq Furlong
derive instance ordFurlong :: Ord Furlong

instance showFurlong :: Show Furlong where
  show (Furlong n) = show n <> " fur"

furlong :: Number -> Furlong
furlong = Furlong

furlongs :: Number -> Furlong
furlongs = Furlong

unwrapFurlong :: Furlong -> Number
unwrapFurlong (Furlong n) = n

furlongsToMeters :: Furlong -> Number
furlongsToMeters (Furlong n) = n * metersPerFurlong

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // league
-- ═════════════════════════════════════════════════════════════════════════════

-- | League - 3 miles
-- | Historically variable, standardized here as statute league
newtype League = League Number

derive instance eqLeague :: Eq League
derive instance ordLeague :: Ord League

instance showLeague :: Show League where
  show (League n) = show n <> " lea"

league :: Number -> League
league = League

leagues :: Number -> League
leagues = League

unwrapLeague :: League -> Number
unwrapLeague (League n) = n

leaguesToMeters :: League -> Number
leaguesToMeters (League n) = n * metersPerLeague

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // nautical mile
-- ═════════════════════════════════════════════════════════════════════════════

-- | Nautical mile - 1852 meters exactly (by international definition)
-- | Approximately 1 minute of arc of latitude
newtype NauticalMile = NauticalMile Number

derive instance eqNauticalMile :: Eq NauticalMile
derive instance ordNauticalMile :: Ord NauticalMile

instance showNauticalMile :: Show NauticalMile where
  show (NauticalMile n) = show n <> " nmi"

nauticalMile :: Number -> NauticalMile
nauticalMile = NauticalMile

nauticalMiles :: Number -> NauticalMile
nauticalMiles = NauticalMile

unwrapNauticalMile :: NauticalMile -> Number
unwrapNauticalMile (NauticalMile n) = n

nauticalMilesToMeters :: NauticalMile -> Number
nauticalMilesToMeters (NauticalMile n) = n * metersPerNauticalMile
