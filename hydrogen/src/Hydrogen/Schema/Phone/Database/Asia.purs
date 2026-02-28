-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // phone // database // asia
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Asian countries phone database.
-- |
-- | Includes East Asia, Southeast Asia, South Asia, and Central Asia.
-- | Middle Eastern countries are in a separate module.

module Hydrogen.Schema.Phone.Database.Asia
  ( asianCountries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude ((<>))

import Hydrogen.Schema.Phone.Country 
  ( Country
  , country
  , formatPattern_
  , Region(Asia)
  )
import Hydrogen.Schema.Phone.CountryCode (unsafeCountryCode)
import Hydrogen.Schema.Phone.DialCode (unsafeDialCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // asian countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | All Asian countries.
asianCountries :: Array Country
asianCountries =
  eastAsianCountries
  <> southeastAsianCountries
  <> southAsianCountries
  <> centralAsianCountries

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // east asia
-- ═════════════════════════════════════════════════════════════════════════════

eastAsianCountries :: Array Country
eastAsianCountries =
  [ china
  , japan
  , southKorea
  , northKorea
  , taiwan
  , hongKong
  , macau
  , mongolia
  ]

-- | China
china :: Country
china = country
  (unsafeCountryCode "CN")
  (unsafeDialCode 86)
  "China"
  "🇨🇳"
  (formatPattern_ "### #### ####")
  "131 2345 6789"
  Asia

-- | Japan
japan :: Country
japan = country
  (unsafeCountryCode "JP")
  (unsafeDialCode 81)
  "Japan"
  "🇯🇵"
  (formatPattern_ "##-####-####")
  "90-1234-5678"
  Asia

-- | South Korea
southKorea :: Country
southKorea = country
  (unsafeCountryCode "KR")
  (unsafeDialCode 82)
  "South Korea"
  "🇰🇷"
  (formatPattern_ "##-####-####")
  "10-1234-5678"
  Asia

-- | North Korea
northKorea :: Country
northKorea = country
  (unsafeCountryCode "KP")
  (unsafeDialCode 850)
  "North Korea"
  "🇰🇵"
  (formatPattern_ "### ### ####")
  "191 234 5678"
  Asia

-- | Taiwan
taiwan :: Country
taiwan = country
  (unsafeCountryCode "TW")
  (unsafeDialCode 886)
  "Taiwan"
  "🇹🇼"
  (formatPattern_ "### ### ###")
  "912 345 678"
  Asia

-- | Hong Kong
hongKong :: Country
hongKong = country
  (unsafeCountryCode "HK")
  (unsafeDialCode 852)
  "Hong Kong"
  "🇭🇰"
  (formatPattern_ "#### ####")
  "5123 4567"
  Asia

-- | Macau
macau :: Country
macau = country
  (unsafeCountryCode "MO")
  (unsafeDialCode 853)
  "Macau"
  "🇲🇴"
  (formatPattern_ "#### ####")
  "6612 3456"
  Asia

-- | Mongolia
mongolia :: Country
mongolia = country
  (unsafeCountryCode "MN")
  (unsafeDialCode 976)
  "Mongolia"
  "🇲🇳"
  (formatPattern_ "## ## ####")
  "88 12 3456"
  Asia

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // southeast asia
-- ═════════════════════════════════════════════════════════════════════════════

southeastAsianCountries :: Array Country
southeastAsianCountries =
  [ vietnam
  , thailand
  , malaysia
  , singapore
  , indonesia
  , philippines
  , myanmar
  , cambodia
  , laos
  , brunei
  , timorLeste
  ]

-- | Vietnam
vietnam :: Country
vietnam = country
  (unsafeCountryCode "VN")
  (unsafeDialCode 84)
  "Vietnam"
  "🇻🇳"
  (formatPattern_ "## ### ## ##")
  "91 234 56 78"
  Asia

-- | Thailand
thailand :: Country
thailand = country
  (unsafeCountryCode "TH")
  (unsafeDialCode 66)
  "Thailand"
  "🇹🇭"
  (formatPattern_ "## ### ####")
  "81 234 5678"
  Asia

-- | Malaysia
malaysia :: Country
malaysia = country
  (unsafeCountryCode "MY")
  (unsafeDialCode 60)
  "Malaysia"
  "🇲🇾"
  (formatPattern_ "##-### ####")
  "12-345 6789"
  Asia

-- | Singapore
singapore :: Country
singapore = country
  (unsafeCountryCode "SG")
  (unsafeDialCode 65)
  "Singapore"
  "🇸🇬"
  (formatPattern_ "#### ####")
  "8123 4567"
  Asia

-- | Indonesia
indonesia :: Country
indonesia = country
  (unsafeCountryCode "ID")
  (unsafeDialCode 62)
  "Indonesia"
  "🇮🇩"
  (formatPattern_ "###-####-####")
  "812-3456-7890"
  Asia

-- | Philippines
philippines :: Country
philippines = country
  (unsafeCountryCode "PH")
  (unsafeDialCode 63)
  "Philippines"
  "🇵🇭"
  (formatPattern_ "### ### ####")
  "917 123 4567"
  Asia

-- | Myanmar
myanmar :: Country
myanmar = country
  (unsafeCountryCode "MM")
  (unsafeDialCode 95)
  "Myanmar"
  "🇲🇲"
  (formatPattern_ "# ### ####")
  "9 123 4567"
  Asia

-- | Cambodia
cambodia :: Country
cambodia = country
  (unsafeCountryCode "KH")
  (unsafeDialCode 855)
  "Cambodia"
  "🇰🇭"
  (formatPattern_ "## ### ###")
  "12 345 678"
  Asia

-- | Laos
laos :: Country
laos = country
  (unsafeCountryCode "LA")
  (unsafeDialCode 856)
  "Laos"
  "🇱🇦"
  (formatPattern_ "## ## ### ###")
  "20 12 345 678"
  Asia

-- | Brunei
brunei :: Country
brunei = country
  (unsafeCountryCode "BN")
  (unsafeDialCode 673)
  "Brunei"
  "🇧🇳"
  (formatPattern_ "### ####")
  "712 3456"
  Asia

-- | Timor-Leste (East Timor)
timorLeste :: Country
timorLeste = country
  (unsafeCountryCode "TL")
  (unsafeDialCode 670)
  "Timor-Leste"
  "🇹🇱"
  (formatPattern_ "### ####")
  "771 2345"
  Asia

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // south asia
-- ═════════════════════════════════════════════════════════════════════════════

southAsianCountries :: Array Country
southAsianCountries =
  [ india
  , pakistan
  , bangladesh
  , sriLanka
  , nepal
  , bhutan
  , maldives
  ]

-- | India
india :: Country
india = country
  (unsafeCountryCode "IN")
  (unsafeDialCode 91)
  "India"
  "🇮🇳"
  (formatPattern_ "##### #####")
  "98765 43210"
  Asia

-- | Pakistan
pakistan :: Country
pakistan = country
  (unsafeCountryCode "PK")
  (unsafeDialCode 92)
  "Pakistan"
  "🇵🇰"
  (formatPattern_ "### #######")
  "300 1234567"
  Asia

-- | Bangladesh
bangladesh :: Country
bangladesh = country
  (unsafeCountryCode "BD")
  (unsafeDialCode 880)
  "Bangladesh"
  "🇧🇩"
  (formatPattern_ "#### ######")
  "1712 345678"
  Asia

-- | Sri Lanka
sriLanka :: Country
sriLanka = country
  (unsafeCountryCode "LK")
  (unsafeDialCode 94)
  "Sri Lanka"
  "🇱🇰"
  (formatPattern_ "## ### ####")
  "71 234 5678"
  Asia

-- | Nepal
nepal :: Country
nepal = country
  (unsafeCountryCode "NP")
  (unsafeDialCode 977)
  "Nepal"
  "🇳🇵"
  (formatPattern_ "###-#######")
  "984-1234567"
  Asia

-- | Bhutan
bhutan :: Country
bhutan = country
  (unsafeCountryCode "BT")
  (unsafeDialCode 975)
  "Bhutan"
  "🇧🇹"
  (formatPattern_ "## ## ## ##")
  "17 12 34 56"
  Asia

-- | Maldives
maldives :: Country
maldives = country
  (unsafeCountryCode "MV")
  (unsafeDialCode 960)
  "Maldives"
  "🇲🇻"
  (formatPattern_ "###-####")
  "791-2345"
  Asia

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // central asia
-- ═════════════════════════════════════════════════════════════════════════════

centralAsianCountries :: Array Country
centralAsianCountries =
  [ kazakhstan
  , uzbekistan
  , turkmenistan
  , kyrgyzstan
  , tajikistan
  , afghanistan
  ]

-- | Kazakhstan
kazakhstan :: Country
kazakhstan = country
  (unsafeCountryCode "KZ")
  (unsafeDialCode 7)
  "Kazakhstan"
  "🇰🇿"
  (formatPattern_ "(###) ###-##-##")
  "(701) 234-56-78"
  Asia

-- | Uzbekistan
uzbekistan :: Country
uzbekistan = country
  (unsafeCountryCode "UZ")
  (unsafeDialCode 998)
  "Uzbekistan"
  "🇺🇿"
  (formatPattern_ "## ### ## ##")
  "90 123 45 67"
  Asia

-- | Turkmenistan
turkmenistan :: Country
turkmenistan = country
  (unsafeCountryCode "TM")
  (unsafeDialCode 993)
  "Turkmenistan"
  "🇹🇲"
  (formatPattern_ "## ######")
  "65 123456"
  Asia

-- | Kyrgyzstan
kyrgyzstan :: Country
kyrgyzstan = country
  (unsafeCountryCode "KG")
  (unsafeDialCode 996)
  "Kyrgyzstan"
  "🇰🇬"
  (formatPattern_ "### ### ###")
  "700 123 456"
  Asia

-- | Tajikistan
tajikistan :: Country
tajikistan = country
  (unsafeCountryCode "TJ")
  (unsafeDialCode 992)
  "Tajikistan"
  "🇹🇯"
  (formatPattern_ "## ### ####")
  "91 123 4567"
  Asia

-- | Afghanistan
afghanistan :: Country
afghanistan = country
  (unsafeCountryCode "AF")
  (unsafeDialCode 93)
  "Afghanistan"
  "🇦🇫"
  (formatPattern_ "## ### ####")
  "70 123 4567"
  Asia
