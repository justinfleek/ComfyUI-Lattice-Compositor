-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                 // hydrogen // schema // phone // database // central-america
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Central American countries phone database.
-- |
-- | Includes all countries in the Central American isthmus,
-- | plus Mexico (which bridges North and Central America).

module Hydrogen.Schema.Phone.Database.CentralAmerica
  ( centralAmericanCountries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Phone.Country 
  ( Country
  , country
  , formatPattern_
  , Region(CentralAmerica)
  )
import Hydrogen.Schema.Phone.CountryCode (unsafeCountryCode)
import Hydrogen.Schema.Phone.DialCode (unsafeDialCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // central american countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | All Central American countries.
centralAmericanCountries :: Array Country
centralAmericanCountries =
  [ mexico
  , guatemala
  , honduras
  , elSalvador
  , nicaragua
  , costaRica
  , panama
  , belize
  ]

-- | Mexico
mexico :: Country
mexico = country
  (unsafeCountryCode "MX")
  (unsafeDialCode 52)
  "Mexico"
  "🇲🇽"
  (formatPattern_ "## #### ####")
  "55 1234 5678"
  CentralAmerica

-- | Guatemala
guatemala :: Country
guatemala = country
  (unsafeCountryCode "GT")
  (unsafeDialCode 502)
  "Guatemala"
  "🇬🇹"
  (formatPattern_ "#### ####")
  "5123 4567"
  CentralAmerica

-- | Honduras
honduras :: Country
honduras = country
  (unsafeCountryCode "HN")
  (unsafeDialCode 504)
  "Honduras"
  "🇭🇳"
  (formatPattern_ "####-####")
  "9123-4567"
  CentralAmerica

-- | El Salvador
elSalvador :: Country
elSalvador = country
  (unsafeCountryCode "SV")
  (unsafeDialCode 503)
  "El Salvador"
  "🇸🇻"
  (formatPattern_ "#### ####")
  "7012 3456"
  CentralAmerica

-- | Nicaragua
nicaragua :: Country
nicaragua = country
  (unsafeCountryCode "NI")
  (unsafeDialCode 505)
  "Nicaragua"
  "🇳🇮"
  (formatPattern_ "#### ####")
  "8123 4567"
  CentralAmerica

-- | Costa Rica
costaRica :: Country
costaRica = country
  (unsafeCountryCode "CR")
  (unsafeDialCode 506)
  "Costa Rica"
  "🇨🇷"
  (formatPattern_ "#### ####")
  "8312 3456"
  CentralAmerica

-- | Panama
panama :: Country
panama = country
  (unsafeCountryCode "PA")
  (unsafeDialCode 507)
  "Panama"
  "🇵🇦"
  (formatPattern_ "####-####")
  "6123-4567"
  CentralAmerica

-- | Belize
belize :: Country
belize = country
  (unsafeCountryCode "BZ")
  (unsafeDialCode 501)
  "Belize"
  "🇧🇿"
  (formatPattern_ "###-####")
  "622-1234"
  CentralAmerica
