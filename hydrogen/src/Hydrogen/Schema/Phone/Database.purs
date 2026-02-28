-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // phone // database
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Country database — Complete international phone metadata.
-- |
-- | This module provides the master list of all countries with their
-- | phone number metadata: dial codes, format patterns, and examples.
-- |
-- | ## Organization
-- |
-- | Countries are organized by region for easier maintenance and
-- | to support region-based filtering in the UI.
-- |
-- | ## Data Sources
-- |
-- | - ITU-T E.164 for dial codes
-- | - ISO 3166-1 alpha-2 for country codes
-- | - National numbering plans for format patterns

module Hydrogen.Schema.Phone.Database
  ( -- * All Countries
    allCountries
  , countryCount
  
  -- * Lookup
  , findByCode
  , findByDialCode
  , findByName
  
  -- * Filtering
  , countriesInRegion
  , countriesWithDialCode
  , searchCountries
  
  -- * Regions (re-exported from regional modules)
  , module Hydrogen.Schema.Phone.Database.NorthAmerica
  , module Hydrogen.Schema.Phone.Database.Europe
  , module Hydrogen.Schema.Phone.Database.Asia
  , module Hydrogen.Schema.Phone.Database.SouthAmerica
  , module Hydrogen.Schema.Phone.Database.Africa
  , module Hydrogen.Schema.Phone.Database.Oceania
  , module Hydrogen.Schema.Phone.Database.Caribbean
  , module Hydrogen.Schema.Phone.Database.MiddleEast
  , module Hydrogen.Schema.Phone.Database.CentralAmerica
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (<>)
  , ($)
  , (==)
  )

import Data.Array (filter, find, length) as Array
import Data.Maybe (Maybe)

import Hydrogen.Schema.Phone.Country 
  ( Country
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
  , matchesSearch
  , isInRegion
  , hasDialCode
  , code
  )
import Hydrogen.Schema.Phone.CountryCode (CountryCode)
import Hydrogen.Schema.Phone.CountryCode (toString) as CC

-- Re-export from regional modules
import Hydrogen.Schema.Phone.Database.NorthAmerica (northAmericanCountries)
import Hydrogen.Schema.Phone.Database.Europe (europeanCountries)
import Hydrogen.Schema.Phone.Database.Asia (asianCountries)
import Hydrogen.Schema.Phone.Database.SouthAmerica (southAmericanCountries)
import Hydrogen.Schema.Phone.Database.Africa (africanCountries)
import Hydrogen.Schema.Phone.Database.Oceania (oceanianCountries)
import Hydrogen.Schema.Phone.Database.Caribbean (caribbeanCountries)
import Hydrogen.Schema.Phone.Database.MiddleEast (middleEasternCountries)
import Hydrogen.Schema.Phone.Database.CentralAmerica (centralAmericanCountries)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // all countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete list of all countries with phone metadata.
allCountries :: Array Country
allCountries = 
  northAmericanCountries
  <> europeanCountries
  <> asianCountries
  <> southAmericanCountries
  <> africanCountries
  <> oceanianCountries
  <> caribbeanCountries
  <> middleEasternCountries
  <> centralAmericanCountries

-- | Total count of countries in database.
countryCount :: Int
countryCount = Array.length allCountries

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // lookup
-- ═════════════════════════════════════════════════════════════════════════════

-- | Find country by ISO 3166-1 alpha-2 code.
findByCode :: CountryCode -> Maybe Country
findByCode cc = Array.find (\c -> CC.toString (code c) == CC.toString cc) allCountries

-- | Find first country with matching dial code.
-- |
-- | Note: Multiple countries can share a dial code (e.g., +1 for US/Canada).
-- | This returns the first match.
findByDialCode :: Int -> Maybe Country
findByDialCode dc = Array.find (hasDialCode dc) allCountries

-- | Find country by name (case-insensitive partial match).
findByName :: String -> Maybe Country
findByName name = Array.find (matchesSearch name) allCountries

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // filtering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all countries in a specific region.
countriesInRegion :: Region -> Array Country
countriesInRegion r = Array.filter (isInRegion r) allCountries

-- | Get all countries with a specific dial code.
countriesWithDialCode :: Int -> Array Country
countriesWithDialCode dc = Array.filter (hasDialCode dc) allCountries

-- | Search countries by query (matches name, code, or dial code).
searchCountries :: String -> Array Country
searchCountries query = Array.filter (matchesSearch query) allCountries
