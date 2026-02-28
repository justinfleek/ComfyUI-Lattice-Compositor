-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // phone // database // middle-east
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Middle Eastern countries phone database.
-- |
-- | Includes countries in the Middle East / Western Asia region.
-- | Some overlap with Africa (Egypt) - Egypt is in Africa module.

module Hydrogen.Schema.Phone.Database.MiddleEast
  ( middleEasternCountries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Phone.Country 
  ( Country
  , country
  , formatPattern_
  , Region(MiddleEast)
  )
import Hydrogen.Schema.Phone.CountryCode (unsafeCountryCode)
import Hydrogen.Schema.Phone.DialCode (unsafeDialCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // middle eastern countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | All Middle Eastern countries.
middleEasternCountries :: Array Country
middleEasternCountries =
  [ saudiArabia
  , unitedArabEmirates
  , israel
  , turkey
  , iran
  , iraq
  , jordan
  , lebanon
  , syria
  , yemen
  , oman
  , qatar
  , kuwait
  , bahrain
  , palestine
  , cyprus
  , armenia
  , georgia
  , azerbaijan
  ]

-- | Saudi Arabia
saudiArabia :: Country
saudiArabia = country
  (unsafeCountryCode "SA")
  (unsafeDialCode 966)
  "Saudi Arabia"
  "🇸🇦"
  (formatPattern_ "## ### ####")
  "50 123 4567"
  MiddleEast

-- | United Arab Emirates
unitedArabEmirates :: Country
unitedArabEmirates = country
  (unsafeCountryCode "AE")
  (unsafeDialCode 971)
  "United Arab Emirates"
  "🇦🇪"
  (formatPattern_ "## ### ####")
  "50 123 4567"
  MiddleEast

-- | Israel
israel :: Country
israel = country
  (unsafeCountryCode "IL")
  (unsafeDialCode 972)
  "Israel"
  "🇮🇱"
  (formatPattern_ "##-###-####")
  "50-123-4567"
  MiddleEast

-- | Turkey
turkey :: Country
turkey = country
  (unsafeCountryCode "TR")
  (unsafeDialCode 90)
  "Turkey"
  "🇹🇷"
  (formatPattern_ "### ### ## ##")
  "532 123 45 67"
  MiddleEast

-- | Iran
iran :: Country
iran = country
  (unsafeCountryCode "IR")
  (unsafeDialCode 98)
  "Iran"
  "🇮🇷"
  (formatPattern_ "### ### ####")
  "912 345 6789"
  MiddleEast

-- | Iraq
iraq :: Country
iraq = country
  (unsafeCountryCode "IQ")
  (unsafeDialCode 964)
  "Iraq"
  "🇮🇶"
  (formatPattern_ "### ### ####")
  "790 123 4567"
  MiddleEast

-- | Jordan
jordan :: Country
jordan = country
  (unsafeCountryCode "JO")
  (unsafeDialCode 962)
  "Jordan"
  "🇯🇴"
  (formatPattern_ "# #### ####")
  "7 9012 3456"
  MiddleEast

-- | Lebanon
lebanon :: Country
lebanon = country
  (unsafeCountryCode "LB")
  (unsafeDialCode 961)
  "Lebanon"
  "🇱🇧"
  (formatPattern_ "## ### ###")
  "71 123 456"
  MiddleEast

-- | Syria
syria :: Country
syria = country
  (unsafeCountryCode "SY")
  (unsafeDialCode 963)
  "Syria"
  "🇸🇾"
  (formatPattern_ "### ### ###")
  "944 123 456"
  MiddleEast

-- | Yemen
yemen :: Country
yemen = country
  (unsafeCountryCode "YE")
  (unsafeDialCode 967)
  "Yemen"
  "🇾🇪"
  (formatPattern_ "### ### ###")
  "711 234 567"
  MiddleEast

-- | Oman
oman :: Country
oman = country
  (unsafeCountryCode "OM")
  (unsafeDialCode 968)
  "Oman"
  "🇴🇲"
  (formatPattern_ "#### ####")
  "9212 3456"
  MiddleEast

-- | Qatar
qatar :: Country
qatar = country
  (unsafeCountryCode "QA")
  (unsafeDialCode 974)
  "Qatar"
  "🇶🇦"
  (formatPattern_ "#### ####")
  "3312 3456"
  MiddleEast

-- | Kuwait
kuwait :: Country
kuwait = country
  (unsafeCountryCode "KW")
  (unsafeDialCode 965)
  "Kuwait"
  "🇰🇼"
  (formatPattern_ "#### ####")
  "5012 3456"
  MiddleEast

-- | Bahrain
bahrain :: Country
bahrain = country
  (unsafeCountryCode "BH")
  (unsafeDialCode 973)
  "Bahrain"
  "🇧🇭"
  (formatPattern_ "#### ####")
  "3612 3456"
  MiddleEast

-- | Palestine
palestine :: Country
palestine = country
  (unsafeCountryCode "PS")
  (unsafeDialCode 970)
  "Palestine"
  "🇵🇸"
  (formatPattern_ "### ### ###")
  "599 123 456"
  MiddleEast

-- | Cyprus
cyprus :: Country
cyprus = country
  (unsafeCountryCode "CY")
  (unsafeDialCode 357)
  "Cyprus"
  "🇨🇾"
  (formatPattern_ "## ######")
  "96 123456"
  MiddleEast

-- | Armenia
armenia :: Country
armenia = country
  (unsafeCountryCode "AM")
  (unsafeDialCode 374)
  "Armenia"
  "🇦🇲"
  (formatPattern_ "## ######")
  "91 123456"
  MiddleEast

-- | Georgia
georgia :: Country
georgia = country
  (unsafeCountryCode "GE")
  (unsafeDialCode 995)
  "Georgia"
  "🇬🇪"
  (formatPattern_ "### ## ## ##")
  "555 12 34 56"
  MiddleEast

-- | Azerbaijan
azerbaijan :: Country
azerbaijan = country
  (unsafeCountryCode "AZ")
  (unsafeDialCode 994)
  "Azerbaijan"
  "🇦🇿"
  (formatPattern_ "## ### ## ##")
  "50 123 45 67"
  MiddleEast
