-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // phone // database // europe // western
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Western European countries phone database.

module Hydrogen.Schema.Phone.Database.Europe.Western
  ( westernEuropeanCountries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Phone.Country 
  ( Country
  , country
  , formatPattern_
  , Region(Europe)
  )
import Hydrogen.Schema.Phone.CountryCode (unsafeCountryCode)
import Hydrogen.Schema.Phone.DialCode (unsafeDialCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // western european countries
-- ═════════════════════════════════════════════════════════════════════════════

westernEuropeanCountries :: Array Country
westernEuropeanCountries =
  [ unitedKingdom
  , germany
  , france
  , italy
  , spain
  , netherlands
  , belgium
  , switzerland
  , austria
  , sweden
  , norway
  , denmark
  , finland
  , ireland
  , portugal
  , luxembourg
  , iceland
  , andorra
  , monaco
  , sanMarino
  , liechtenstein
  , malta
  ]

unitedKingdom :: Country
unitedKingdom = country
  (unsafeCountryCode "GB")
  (unsafeDialCode 44)
  "United Kingdom"
  "🇬🇧"
  (formatPattern_ "#### ### ####")
  "7911 123456"
  Europe

germany :: Country
germany = country
  (unsafeCountryCode "DE")
  (unsafeDialCode 49)
  "Germany"
  "🇩🇪"
  (formatPattern_ "### #######")
  "151 12345678"
  Europe

france :: Country
france = country
  (unsafeCountryCode "FR")
  (unsafeDialCode 33)
  "France"
  "🇫🇷"
  (formatPattern_ "## ## ## ## ##")
  "06 12 34 56 78"
  Europe

italy :: Country
italy = country
  (unsafeCountryCode "IT")
  (unsafeDialCode 39)
  "Italy"
  "🇮🇹"
  (formatPattern_ "### ### ####")
  "312 345 6789"
  Europe

spain :: Country
spain = country
  (unsafeCountryCode "ES")
  (unsafeDialCode 34)
  "Spain"
  "🇪🇸"
  (formatPattern_ "### ### ###")
  "612 345 678"
  Europe

netherlands :: Country
netherlands = country
  (unsafeCountryCode "NL")
  (unsafeDialCode 31)
  "Netherlands"
  "🇳🇱"
  (formatPattern_ "## ########")
  "06 12345678"
  Europe

belgium :: Country
belgium = country
  (unsafeCountryCode "BE")
  (unsafeDialCode 32)
  "Belgium"
  "🇧🇪"
  (formatPattern_ "### ## ## ##")
  "470 12 34 56"
  Europe

switzerland :: Country
switzerland = country
  (unsafeCountryCode "CH")
  (unsafeDialCode 41)
  "Switzerland"
  "🇨🇭"
  (formatPattern_ "## ### ## ##")
  "78 123 45 67"
  Europe

austria :: Country
austria = country
  (unsafeCountryCode "AT")
  (unsafeDialCode 43)
  "Austria"
  "🇦🇹"
  (formatPattern_ "### #######")
  "664 1234567"
  Europe

sweden :: Country
sweden = country
  (unsafeCountryCode "SE")
  (unsafeDialCode 46)
  "Sweden"
  "🇸🇪"
  (formatPattern_ "##-### ## ##")
  "70-123 45 67"
  Europe

norway :: Country
norway = country
  (unsafeCountryCode "NO")
  (unsafeDialCode 47)
  "Norway"
  "🇳🇴"
  (formatPattern_ "### ## ###")
  "406 12 345"
  Europe

denmark :: Country
denmark = country
  (unsafeCountryCode "DK")
  (unsafeDialCode 45)
  "Denmark"
  "🇩🇰"
  (formatPattern_ "## ## ## ##")
  "32 12 34 56"
  Europe

finland :: Country
finland = country
  (unsafeCountryCode "FI")
  (unsafeDialCode 358)
  "Finland"
  "🇫🇮"
  (formatPattern_ "## ### ####")
  "41 234 5678"
  Europe

ireland :: Country
ireland = country
  (unsafeCountryCode "IE")
  (unsafeDialCode 353)
  "Ireland"
  "🇮🇪"
  (formatPattern_ "## ### ####")
  "85 123 4567"
  Europe

portugal :: Country
portugal = country
  (unsafeCountryCode "PT")
  (unsafeDialCode 351)
  "Portugal"
  "🇵🇹"
  (formatPattern_ "### ### ###")
  "912 345 678"
  Europe

luxembourg :: Country
luxembourg = country
  (unsafeCountryCode "LU")
  (unsafeDialCode 352)
  "Luxembourg"
  "🇱🇺"
  (formatPattern_ "### ### ###")
  "621 234 567"
  Europe

iceland :: Country
iceland = country
  (unsafeCountryCode "IS")
  (unsafeDialCode 354)
  "Iceland"
  "🇮🇸"
  (formatPattern_ "### ####")
  "611 1234"
  Europe

andorra :: Country
andorra = country
  (unsafeCountryCode "AD")
  (unsafeDialCode 376)
  "Andorra"
  "🇦🇩"
  (formatPattern_ "### ###")
  "312 345"
  Europe

monaco :: Country
monaco = country
  (unsafeCountryCode "MC")
  (unsafeDialCode 377)
  "Monaco"
  "🇲🇨"
  (formatPattern_ "## ## ## ##")
  "61 23 45 67"
  Europe

sanMarino :: Country
sanMarino = country
  (unsafeCountryCode "SM")
  (unsafeDialCode 378)
  "San Marino"
  "🇸🇲"
  (formatPattern_ "## ## ## ##")
  "66 12 34 56"
  Europe

liechtenstein :: Country
liechtenstein = country
  (unsafeCountryCode "LI")
  (unsafeDialCode 423)
  "Liechtenstein"
  "🇱🇮"
  (formatPattern_ "### ####")
  "660 1234"
  Europe

malta :: Country
malta = country
  (unsafeCountryCode "MT")
  (unsafeDialCode 356)
  "Malta"
  "🇲🇹"
  (formatPattern_ "#### ####")
  "7912 3456"
  Europe
