-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--               // hydrogen // schema // phone // database // europe // eastern
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Eastern European countries phone database.

module Hydrogen.Schema.Phone.Database.Europe.Eastern
  ( easternEuropeanCountries
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
--                                                 // eastern european countries
-- ═════════════════════════════════════════════════════════════════════════════

easternEuropeanCountries :: Array Country
easternEuropeanCountries =
  [ poland
  , czechRepublic
  , hungary
  , romania
  , greece
  , ukraine
  , slovakia
  , bulgaria
  , croatia
  , slovenia
  , serbia
  , lithuania
  , latvia
  , estonia
  , albania
  , northMacedonia
  , montenegro
  , bosniaHerzegovina
  , moldova
  , cyprus
  , belarus
  , russia
  ]

poland :: Country
poland = country
  (unsafeCountryCode "PL")
  (unsafeDialCode 48)
  "Poland"
  "🇵🇱"
  (formatPattern_ "### ### ###")
  "512 345 678"
  Europe

czechRepublic :: Country
czechRepublic = country
  (unsafeCountryCode "CZ")
  (unsafeDialCode 420)
  "Czech Republic"
  "🇨🇿"
  (formatPattern_ "### ### ###")
  "601 123 456"
  Europe

hungary :: Country
hungary = country
  (unsafeCountryCode "HU")
  (unsafeDialCode 36)
  "Hungary"
  "🇭🇺"
  (formatPattern_ "## ### ####")
  "20 123 4567"
  Europe

romania :: Country
romania = country
  (unsafeCountryCode "RO")
  (unsafeDialCode 40)
  "Romania"
  "🇷🇴"
  (formatPattern_ "### ### ###")
  "721 234 567"
  Europe

greece :: Country
greece = country
  (unsafeCountryCode "GR")
  (unsafeDialCode 30)
  "Greece"
  "🇬🇷"
  (formatPattern_ "### ### ####")
  "691 234 5678"
  Europe

ukraine :: Country
ukraine = country
  (unsafeCountryCode "UA")
  (unsafeDialCode 380)
  "Ukraine"
  "🇺🇦"
  (formatPattern_ "## ### ## ##")
  "50 123 45 67"
  Europe

slovakia :: Country
slovakia = country
  (unsafeCountryCode "SK")
  (unsafeDialCode 421)
  "Slovakia"
  "🇸🇰"
  (formatPattern_ "### ### ###")
  "912 345 678"
  Europe

bulgaria :: Country
bulgaria = country
  (unsafeCountryCode "BG")
  (unsafeDialCode 359)
  "Bulgaria"
  "🇧🇬"
  (formatPattern_ "### ### ###")
  "878 123 456"
  Europe

croatia :: Country
croatia = country
  (unsafeCountryCode "HR")
  (unsafeDialCode 385)
  "Croatia"
  "🇭🇷"
  (formatPattern_ "## ### ####")
  "91 234 5678"
  Europe

slovenia :: Country
slovenia = country
  (unsafeCountryCode "SI")
  (unsafeDialCode 386)
  "Slovenia"
  "🇸🇮"
  (formatPattern_ "## ### ###")
  "31 234 567"
  Europe

serbia :: Country
serbia = country
  (unsafeCountryCode "RS")
  (unsafeDialCode 381)
  "Serbia"
  "🇷🇸"
  (formatPattern_ "## ### ####")
  "60 123 4567"
  Europe

lithuania :: Country
lithuania = country
  (unsafeCountryCode "LT")
  (unsafeDialCode 370)
  "Lithuania"
  "🇱🇹"
  (formatPattern_ "### #####")
  "612 34567"
  Europe

latvia :: Country
latvia = country
  (unsafeCountryCode "LV")
  (unsafeDialCode 371)
  "Latvia"
  "🇱🇻"
  (formatPattern_ "## ### ###")
  "21 234 567"
  Europe

estonia :: Country
estonia = country
  (unsafeCountryCode "EE")
  (unsafeDialCode 372)
  "Estonia"
  "🇪🇪"
  (formatPattern_ "#### ####")
  "5123 4567"
  Europe

albania :: Country
albania = country
  (unsafeCountryCode "AL")
  (unsafeDialCode 355)
  "Albania"
  "🇦🇱"
  (formatPattern_ "## ### ####")
  "66 123 4567"
  Europe

northMacedonia :: Country
northMacedonia = country
  (unsafeCountryCode "MK")
  (unsafeDialCode 389)
  "North Macedonia"
  "🇲🇰"
  (formatPattern_ "## ### ###")
  "70 234 567"
  Europe

montenegro :: Country
montenegro = country
  (unsafeCountryCode "ME")
  (unsafeDialCode 382)
  "Montenegro"
  "🇲🇪"
  (formatPattern_ "## ### ###")
  "67 234 567"
  Europe

bosniaHerzegovina :: Country
bosniaHerzegovina = country
  (unsafeCountryCode "BA")
  (unsafeDialCode 387)
  "Bosnia and Herzegovina"
  "🇧🇦"
  (formatPattern_ "## ### ###")
  "61 234 567"
  Europe

moldova :: Country
moldova = country
  (unsafeCountryCode "MD")
  (unsafeDialCode 373)
  "Moldova"
  "🇲🇩"
  (formatPattern_ "### ## ###")
  "621 23 456"
  Europe

cyprus :: Country
cyprus = country
  (unsafeCountryCode "CY")
  (unsafeDialCode 357)
  "Cyprus"
  "🇨🇾"
  (formatPattern_ "## ######")
  "96 123456"
  Europe

belarus :: Country
belarus = country
  (unsafeCountryCode "BY")
  (unsafeDialCode 375)
  "Belarus"
  "🇧🇾"
  (formatPattern_ "## ### ## ##")
  "29 123 45 67"
  Europe

russia :: Country
russia = country
  (unsafeCountryCode "RU")
  (unsafeDialCode 7)
  "Russia"
  "🇷🇺"
  (formatPattern_ "### ###-##-##")
  "912 345-67-89"
  Europe
