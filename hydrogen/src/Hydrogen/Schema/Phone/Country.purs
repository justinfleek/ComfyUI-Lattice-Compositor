-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // phone // country
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Country — Molecule combining country identification with phone metadata.
-- |
-- | A Country molecule composes:
-- | - CountryCode (ISO 3166-1 alpha-2)
-- | - DialCode (E.164 calling code)
-- | - Name (display name)
-- | - Flag (emoji or renderer key)
-- | - FormatPattern (how to display national numbers)
-- | - ExampleNumber (for placeholder/validation hints)
-- |
-- | ## Schema Composition
-- |
-- | ```
-- | Country = CountryCode × DialCode × Name × Flag × FormatPattern × Example
-- | ```
-- |
-- | This is a molecule because it combines multiple atoms into a cohesive
-- | unit with specific semantics (phone-related country data).

module Hydrogen.Schema.Phone.Country
  ( -- * Type
    Country(Country)
  
  -- * Construction
  , country
  , mkCountry
  
  -- * Accessors
  , code
  , dialCode
  , name
  , flag
  , formatPattern
  , exampleNumber
  
  -- * Predicates
  , hasDialCode
  , matchesSearch
  , isInRegion
  
  -- * Format Pattern
  , FormatPattern
  , formatPattern_
  , patternToString
  , countFormatSlots
  
  -- * Region
  , Region
      ( NorthAmerica
      , Europe
      , Asia
      , SouthAmerica
      , Africa
      , Oceania
      , Caribbean
      , MiddleEast
      , CentralAmerica
      )
  , regionName
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , map
  , (<>)
  , (==)
  , (||)
  , ($)
  )

import Data.Array (filter, length) as Array
import Data.String (toLower, contains) as String
import Data.String.Pattern (Pattern(Pattern))
import Data.String.CodeUnits (toCharArray) as String

import Hydrogen.Schema.Phone.CountryCode (CountryCode)
import Hydrogen.Schema.Phone.CountryCode (toString) as CC
import Hydrogen.Schema.Phone.DialCode (DialCode)
import Hydrogen.Schema.Phone.DialCode (toInt, toDisplayString) as DC

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // format pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Phone number format pattern.
-- |
-- | Uses '#' as digit placeholder, other characters are literals.
-- | Examples:
-- | - "(###) ###-####" for US/Canada
-- | - "#### ### ###" for Australia
-- | - "##-####-####" for Japan
newtype FormatPattern = FormatPattern String

derive instance eqFormatPattern :: Eq FormatPattern

instance showFormatPattern :: Show FormatPattern where
  show (FormatPattern p) = "FormatPattern \"" <> p <> "\""

-- | Create a format pattern.
formatPattern_ :: String -> FormatPattern
formatPattern_ = FormatPattern

-- | Get pattern as string.
patternToString :: FormatPattern -> String
patternToString (FormatPattern p) = p

-- | Count the number of digit slots in a pattern.
countFormatSlots :: FormatPattern -> Int
countFormatSlots (FormatPattern p) = 
  Array.length $ Array.filter (\c -> c == '#') $ String.toCharArray p

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // region
-- ═════════════════════════════════════════════════════════════════════════════

-- | Geographic region for country grouping.
data Region
  = NorthAmerica
  | Europe
  | Asia
  | SouthAmerica
  | Africa
  | Oceania
  | Caribbean
  | MiddleEast
  | CentralAmerica

derive instance eqRegion :: Eq Region

instance ordRegion :: Ord Region where
  compare a b = compare (regionToInt a) (regionToInt b)

instance showRegion :: Show Region where
  show r = regionName r

-- | Get display name for region.
regionName :: Region -> String
regionName r = case r of
  NorthAmerica -> "North America"
  Europe -> "Europe"
  Asia -> "Asia"
  SouthAmerica -> "South America"
  Africa -> "Africa"
  Oceania -> "Oceania"
  Caribbean -> "Caribbean"
  MiddleEast -> "Middle East"
  CentralAmerica -> "Central America"

-- | Internal ordering for Ord instance.
regionToInt :: Region -> Int
regionToInt r = case r of
  NorthAmerica -> 0
  Europe -> 1
  Asia -> 2
  SouthAmerica -> 3
  Africa -> 4
  Oceania -> 5
  Caribbean -> 6
  MiddleEast -> 7
  CentralAmerica -> 8

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // country
-- ═════════════════════════════════════════════════════════════════════════════

-- | Country with phone-related metadata.
-- |
-- | A molecule combining country identification with phone number formatting
-- | and validation information.
newtype Country = Country
  { code :: CountryCode
  , dialCode :: DialCode
  , name :: String
  , flag :: String
  , format :: FormatPattern
  , example :: String
  , region :: Region
  }

derive instance eqCountry :: Eq Country

instance ordCountry :: Ord Country where
  compare (Country a) (Country b) = compare a.name b.name

instance showCountry :: Show Country where
  show (Country c) = "Country { " 
    <> "code: " <> show c.code
    <> ", name: " <> show c.name
    <> ", dial: " <> DC.toDisplayString c.dialCode
    <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a country with all fields.
country 
  :: CountryCode 
  -> DialCode 
  -> String 
  -> String 
  -> FormatPattern 
  -> String 
  -> Region
  -> Country
country code' dialCode' name' flag' format' example' region' = Country
  { code: code'
  , dialCode: dialCode'
  , name: name'
  , flag: flag'
  , format: format'
  , example: example'
  , region: region'
  }

-- | Alias for country constructor.
mkCountry 
  :: CountryCode 
  -> DialCode 
  -> String 
  -> String 
  -> FormatPattern 
  -> String 
  -> Region
  -> Country
mkCountry = country

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get country code.
code :: Country -> CountryCode
code (Country c) = c.code

-- | Get dial code.
dialCode :: Country -> DialCode
dialCode (Country c) = c.dialCode

-- | Get country name.
name :: Country -> String
name (Country c) = c.name

-- | Get flag (emoji or key).
flag :: Country -> String
flag (Country c) = c.flag

-- | Get format pattern.
formatPattern :: Country -> FormatPattern
formatPattern (Country c) = c.format

-- | Get example number.
exampleNumber :: Country -> String
exampleNumber (Country c) = c.example

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if country has a specific dial code.
hasDialCode :: Int -> Country -> Boolean
hasDialCode n (Country c) = DC.toInt c.dialCode == n

-- | Check if country matches a search query.
-- |
-- | Searches in: name (case-insensitive), country code, dial code.
matchesSearch :: String -> Country -> Boolean
matchesSearch query (Country c) =
  let q = String.toLower query
      nameLower = String.toLower c.name
      codeLower = String.toLower (CC.toString c.code)
      dialStr = DC.toDisplayString c.dialCode
  in String.contains (Pattern q) nameLower
     || String.contains (Pattern q) codeLower
     || String.contains (Pattern q) dialStr

-- | Check if country is in a specific region.
isInRegion :: Region -> Country -> Boolean
isInRegion r (Country c) = c.region == r
