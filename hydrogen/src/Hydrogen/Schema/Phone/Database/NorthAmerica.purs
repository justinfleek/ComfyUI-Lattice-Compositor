-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // phone // database // north-america
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | North American countries phone database.
-- |
-- | Includes US, Canada, and other NANP (North American Numbering Plan) members.

module Hydrogen.Schema.Phone.Database.NorthAmerica
  ( northAmericanCountries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Phone.Country 
  ( Country
  , country
  , formatPattern_
  , Region(NorthAmerica)
  )
import Hydrogen.Schema.Phone.CountryCode (unsafeCountryCode)
import Hydrogen.Schema.Phone.DialCode (unsafeDialCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // north american countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | North American countries (NANP zone primarily).
northAmericanCountries :: Array Country
northAmericanCountries =
  [ unitedStates
  , canada
  ]

-- | United States of America
unitedStates :: Country
unitedStates = country
  (unsafeCountryCode "US")
  (unsafeDialCode 1)
  "United States"
  "🇺🇸"
  (formatPattern_ "(###) ###-####")
  "(555) 123-4567"
  NorthAmerica

-- | Canada
canada :: Country
canada = country
  (unsafeCountryCode "CA")
  (unsafeDialCode 1)
  "Canada"
  "🇨🇦"
  (formatPattern_ "(###) ###-####")
  "(555) 123-4567"
  NorthAmerica
