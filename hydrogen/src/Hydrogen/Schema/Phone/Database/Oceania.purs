-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // phone // database // oceania
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Oceanian countries phone database.
-- |
-- | Includes Australia, New Zealand, and Pacific Island nations.

module Hydrogen.Schema.Phone.Database.Oceania
  ( oceanianCountries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude ((<>))

import Hydrogen.Schema.Phone.Country 
  ( Country
  , country
  , formatPattern_
  , Region(Oceania)
  )
import Hydrogen.Schema.Phone.CountryCode (unsafeCountryCode)
import Hydrogen.Schema.Phone.DialCode (unsafeDialCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // oceanian countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | All Oceanian countries.
oceanianCountries :: Array Country
oceanianCountries =
  australasianCountries
  <> melanesianCountries
  <> micronesianCountries
  <> polynesianCountries

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // australasia
-- ═════════════════════════════════════════════════════════════════════════════

australasianCountries :: Array Country
australasianCountries =
  [ australia
  , newZealand
  ]

-- | Australia
australia :: Country
australia = country
  (unsafeCountryCode "AU")
  (unsafeDialCode 61)
  "Australia"
  "🇦🇺"
  (formatPattern_ "### ### ###")
  "412 345 678"
  Oceania

-- | New Zealand
newZealand :: Country
newZealand = country
  (unsafeCountryCode "NZ")
  (unsafeDialCode 64)
  "New Zealand"
  "🇳🇿"
  (formatPattern_ "## ### ####")
  "21 123 4567"
  Oceania

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // melanesia
-- ═════════════════════════════════════════════════════════════════════════════

melanesianCountries :: Array Country
melanesianCountries =
  [ papuaNewGuinea
  , fiji
  , solomonIslands
  , vanuatu
  , newCaledonia
  ]

-- | Papua New Guinea
papuaNewGuinea :: Country
papuaNewGuinea = country
  (unsafeCountryCode "PG")
  (unsafeDialCode 675)
  "Papua New Guinea"
  "🇵🇬"
  (formatPattern_ "### ####")
  "712 3456"
  Oceania

-- | Fiji
fiji :: Country
fiji = country
  (unsafeCountryCode "FJ")
  (unsafeDialCode 679)
  "Fiji"
  "🇫🇯"
  (formatPattern_ "### ####")
  "912 3456"
  Oceania

-- | Solomon Islands
solomonIslands :: Country
solomonIslands = country
  (unsafeCountryCode "SB")
  (unsafeDialCode 677)
  "Solomon Islands"
  "🇸🇧"
  (formatPattern_ "### ####")
  "741 2345"
  Oceania

-- | Vanuatu
vanuatu :: Country
vanuatu = country
  (unsafeCountryCode "VU")
  (unsafeDialCode 678)
  "Vanuatu"
  "🇻🇺"
  (formatPattern_ "### ####")
  "591 2345"
  Oceania

-- | New Caledonia (French territory)
newCaledonia :: Country
newCaledonia = country
  (unsafeCountryCode "NC")
  (unsafeDialCode 687)
  "New Caledonia"
  "🇳🇨"
  (formatPattern_ "## ## ##")
  "75 12 34"
  Oceania

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // micronesia
-- ═════════════════════════════════════════════════════════════════════════════

micronesianCountries :: Array Country
micronesianCountries =
  [ guam
  , palau
  , micronesia
  , marshallIslands
  , kiribati
  , nauru
  ]

-- | Guam (US territory)
guam :: Country
guam = country
  (unsafeCountryCode "GU")
  (unsafeDialCode 1)
  "Guam"
  "🇬🇺"
  (formatPattern_ "(###) ###-####")
  "(671) 123-4567"
  Oceania

-- | Palau
palau :: Country
palau = country
  (unsafeCountryCode "PW")
  (unsafeDialCode 680)
  "Palau"
  "🇵🇼"
  (formatPattern_ "### ####")
  "775 1234"
  Oceania

-- | Federated States of Micronesia
micronesia :: Country
micronesia = country
  (unsafeCountryCode "FM")
  (unsafeDialCode 691)
  "Micronesia"
  "🇫🇲"
  (formatPattern_ "### ####")
  "350 1234"
  Oceania

-- | Marshall Islands
marshallIslands :: Country
marshallIslands = country
  (unsafeCountryCode "MH")
  (unsafeDialCode 692)
  "Marshall Islands"
  "🇲🇭"
  (formatPattern_ "###-####")
  "235-1234"
  Oceania

-- | Kiribati
kiribati :: Country
kiribati = country
  (unsafeCountryCode "KI")
  (unsafeDialCode 686)
  "Kiribati"
  "🇰🇮"
  (formatPattern_ "########")
  "72012345"
  Oceania

-- | Nauru
nauru :: Country
nauru = country
  (unsafeCountryCode "NR")
  (unsafeDialCode 674)
  "Nauru"
  "🇳🇷"
  (formatPattern_ "### ####")
  "555 1234"
  Oceania

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // polynesia
-- ═════════════════════════════════════════════════════════════════════════════

polynesianCountries :: Array Country
polynesianCountries =
  [ samoa
  , tonga
  , frenchPolynesia
  , cookIslands
  , tuvalu
  , americanSamoa
  ]

-- | Samoa
samoa :: Country
samoa = country
  (unsafeCountryCode "WS")
  (unsafeDialCode 685)
  "Samoa"
  "🇼🇸"
  (formatPattern_ "## #####")
  "72 12345"
  Oceania

-- | Tonga
tonga :: Country
tonga = country
  (unsafeCountryCode "TO")
  (unsafeDialCode 676)
  "Tonga"
  "🇹🇴"
  (formatPattern_ "### ####")
  "771 2345"
  Oceania

-- | French Polynesia
frenchPolynesia :: Country
frenchPolynesia = country
  (unsafeCountryCode "PF")
  (unsafeDialCode 689)
  "French Polynesia"
  "🇵🇫"
  (formatPattern_ "## ## ## ##")
  "87 12 34 56"
  Oceania

-- | Cook Islands
cookIslands :: Country
cookIslands = country
  (unsafeCountryCode "CK")
  (unsafeDialCode 682)
  "Cook Islands"
  "🇨🇰"
  (formatPattern_ "## ###")
  "71 234"
  Oceania

-- | Tuvalu
tuvalu :: Country
tuvalu = country
  (unsafeCountryCode "TV")
  (unsafeDialCode 688)
  "Tuvalu"
  "🇹🇻"
  (formatPattern_ "######")
  "901234"
  Oceania

-- | American Samoa (US territory)
americanSamoa :: Country
americanSamoa = country
  (unsafeCountryCode "AS")
  (unsafeDialCode 1)
  "American Samoa"
  "🇦🇸"
  (formatPattern_ "(###) ###-####")
  "(684) 123-4567"
  Oceania
