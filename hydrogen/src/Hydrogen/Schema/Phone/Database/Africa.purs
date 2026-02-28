-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // phone // database // africa
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | African countries phone database.
-- |
-- | Includes all sovereign nations in Africa, organized by sub-region.
-- | North African countries with Middle Eastern ties are included here.

module Hydrogen.Schema.Phone.Database.Africa
  ( africanCountries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude ((<>))

import Hydrogen.Schema.Phone.Country 
  ( Country
  , country
  , formatPattern_
  , Region(Africa)
  )
import Hydrogen.Schema.Phone.CountryCode (unsafeCountryCode)
import Hydrogen.Schema.Phone.DialCode (unsafeDialCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // african countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | All African countries.
africanCountries :: Array Country
africanCountries =
  northAfricanCountries
  <> westAfricanCountries
  <> eastAfricanCountries
  <> centralAfricanCountries
  <> southernAfricanCountries

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // north africa
-- ═════════════════════════════════════════════════════════════════════════════

northAfricanCountries :: Array Country
northAfricanCountries =
  [ egypt
  , morocco
  , algeria
  , tunisia
  , libya
  , sudan
  ]

-- | Egypt
egypt :: Country
egypt = country
  (unsafeCountryCode "EG")
  (unsafeDialCode 20)
  "Egypt"
  "🇪🇬"
  (formatPattern_ "### ### ####")
  "100 123 4567"
  Africa

-- | Morocco
morocco :: Country
morocco = country
  (unsafeCountryCode "MA")
  (unsafeDialCode 212)
  "Morocco"
  "🇲🇦"
  (formatPattern_ "##-### ####")
  "61-234 5678"
  Africa

-- | Algeria
algeria :: Country
algeria = country
  (unsafeCountryCode "DZ")
  (unsafeDialCode 213)
  "Algeria"
  "🇩🇿"
  (formatPattern_ "### ## ## ##")
  "551 23 45 67"
  Africa

-- | Tunisia
tunisia :: Country
tunisia = country
  (unsafeCountryCode "TN")
  (unsafeDialCode 216)
  "Tunisia"
  "🇹🇳"
  (formatPattern_ "## ### ###")
  "20 123 456"
  Africa

-- | Libya
libya :: Country
libya = country
  (unsafeCountryCode "LY")
  (unsafeDialCode 218)
  "Libya"
  "🇱🇾"
  (formatPattern_ "##-#######")
  "91-1234567"
  Africa

-- | Sudan
sudan :: Country
sudan = country
  (unsafeCountryCode "SD")
  (unsafeDialCode 249)
  "Sudan"
  "🇸🇩"
  (formatPattern_ "## ### ####")
  "91 123 4567"
  Africa

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // west africa
-- ═════════════════════════════════════════════════════════════════════════════

westAfricanCountries :: Array Country
westAfricanCountries =
  [ nigeria
  , ghana
  , senegal
  , ivoryCoast
  , mali
  , burkinaFaso
  , niger
  , guinea
  , benin
  , togo
  , sierraLeone
  , liberia
  , mauritania
  , gambia
  , guineaBissau
  , capeVerde
  ]

-- | Nigeria
nigeria :: Country
nigeria = country
  (unsafeCountryCode "NG")
  (unsafeDialCode 234)
  "Nigeria"
  "🇳🇬"
  (formatPattern_ "### ### ####")
  "801 234 5678"
  Africa

-- | Ghana
ghana :: Country
ghana = country
  (unsafeCountryCode "GH")
  (unsafeDialCode 233)
  "Ghana"
  "🇬🇭"
  (formatPattern_ "## ### ####")
  "24 123 4567"
  Africa

-- | Senegal
senegal :: Country
senegal = country
  (unsafeCountryCode "SN")
  (unsafeDialCode 221)
  "Senegal"
  "🇸🇳"
  (formatPattern_ "## ### ## ##")
  "70 123 45 67"
  Africa

-- | Ivory Coast (Côte d'Ivoire)
ivoryCoast :: Country
ivoryCoast = country
  (unsafeCountryCode "CI")
  (unsafeDialCode 225)
  "Ivory Coast"
  "🇨🇮"
  (formatPattern_ "## ## ## ## ##")
  "07 12 34 56 78"
  Africa

-- | Mali
mali :: Country
mali = country
  (unsafeCountryCode "ML")
  (unsafeDialCode 223)
  "Mali"
  "🇲🇱"
  (formatPattern_ "## ## ## ##")
  "70 12 34 56"
  Africa

-- | Burkina Faso
burkinaFaso :: Country
burkinaFaso = country
  (unsafeCountryCode "BF")
  (unsafeDialCode 226)
  "Burkina Faso"
  "🇧🇫"
  (formatPattern_ "## ## ## ##")
  "70 12 34 56"
  Africa

-- | Niger
niger :: Country
niger = country
  (unsafeCountryCode "NE")
  (unsafeDialCode 227)
  "Niger"
  "🇳🇪"
  (formatPattern_ "## ## ## ##")
  "90 12 34 56"
  Africa

-- | Guinea
guinea :: Country
guinea = country
  (unsafeCountryCode "GN")
  (unsafeDialCode 224)
  "Guinea"
  "🇬🇳"
  (formatPattern_ "### ## ## ##")
  "620 12 34 56"
  Africa

-- | Benin
benin :: Country
benin = country
  (unsafeCountryCode "BJ")
  (unsafeDialCode 229)
  "Benin"
  "🇧🇯"
  (formatPattern_ "## ## ## ##")
  "90 12 34 56"
  Africa

-- | Togo
togo :: Country
togo = country
  (unsafeCountryCode "TG")
  (unsafeDialCode 228)
  "Togo"
  "🇹🇬"
  (formatPattern_ "## ## ## ##")
  "90 12 34 56"
  Africa

-- | Sierra Leone
sierraLeone :: Country
sierraLeone = country
  (unsafeCountryCode "SL")
  (unsafeDialCode 232)
  "Sierra Leone"
  "🇸🇱"
  (formatPattern_ "## ######")
  "76 123456"
  Africa

-- | Liberia
liberia :: Country
liberia = country
  (unsafeCountryCode "LR")
  (unsafeDialCode 231)
  "Liberia"
  "🇱🇷"
  (formatPattern_ "### ### ###")
  "770 123 456"
  Africa

-- | Mauritania
mauritania :: Country
mauritania = country
  (unsafeCountryCode "MR")
  (unsafeDialCode 222)
  "Mauritania"
  "🇲🇷"
  (formatPattern_ "## ## ## ##")
  "22 12 34 56"
  Africa

-- | Gambia
gambia :: Country
gambia = country
  (unsafeCountryCode "GM")
  (unsafeDialCode 220)
  "Gambia"
  "🇬🇲"
  (formatPattern_ "### ####")
  "301 2345"
  Africa

-- | Guinea-Bissau
guineaBissau :: Country
guineaBissau = country
  (unsafeCountryCode "GW")
  (unsafeDialCode 245)
  "Guinea-Bissau"
  "🇬🇼"
  (formatPattern_ "### ####")
  "955 1234"
  Africa

-- | Cape Verde
capeVerde :: Country
capeVerde = country
  (unsafeCountryCode "CV")
  (unsafeDialCode 238)
  "Cape Verde"
  "🇨🇻"
  (formatPattern_ "### ## ##")
  "991 12 34"
  Africa

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // east africa
-- ═════════════════════════════════════════════════════════════════════════════

eastAfricanCountries :: Array Country
eastAfricanCountries =
  [ kenya
  , ethiopia
  , tanzania
  , uganda
  , rwanda
  , burundi
  , southSudan
  , somalia
  , eritrea
  , djibouti
  ]

-- | Kenya
kenya :: Country
kenya = country
  (unsafeCountryCode "KE")
  (unsafeDialCode 254)
  "Kenya"
  "🇰🇪"
  (formatPattern_ "### ### ###")
  "712 345 678"
  Africa

-- | Ethiopia
ethiopia :: Country
ethiopia = country
  (unsafeCountryCode "ET")
  (unsafeDialCode 251)
  "Ethiopia"
  "🇪🇹"
  (formatPattern_ "## ### ####")
  "91 123 4567"
  Africa

-- | Tanzania
tanzania :: Country
tanzania = country
  (unsafeCountryCode "TZ")
  (unsafeDialCode 255)
  "Tanzania"
  "🇹🇿"
  (formatPattern_ "### ### ###")
  "712 345 678"
  Africa

-- | Uganda
uganda :: Country
uganda = country
  (unsafeCountryCode "UG")
  (unsafeDialCode 256)
  "Uganda"
  "🇺🇬"
  (formatPattern_ "### ### ###")
  "712 345 678"
  Africa

-- | Rwanda
rwanda :: Country
rwanda = country
  (unsafeCountryCode "RW")
  (unsafeDialCode 250)
  "Rwanda"
  "🇷🇼"
  (formatPattern_ "### ### ###")
  "781 234 567"
  Africa

-- | Burundi
burundi :: Country
burundi = country
  (unsafeCountryCode "BI")
  (unsafeDialCode 257)
  "Burundi"
  "🇧🇮"
  (formatPattern_ "## ## ## ##")
  "79 12 34 56"
  Africa

-- | South Sudan
southSudan :: Country
southSudan = country
  (unsafeCountryCode "SS")
  (unsafeDialCode 211)
  "South Sudan"
  "🇸🇸"
  (formatPattern_ "## ### ####")
  "91 234 5678"
  Africa

-- | Somalia
somalia :: Country
somalia = country
  (unsafeCountryCode "SO")
  (unsafeDialCode 252)
  "Somalia"
  "🇸🇴"
  (formatPattern_ "# ### ###")
  "6 123 456"
  Africa

-- | Eritrea
eritrea :: Country
eritrea = country
  (unsafeCountryCode "ER")
  (unsafeDialCode 291)
  "Eritrea"
  "🇪🇷"
  (formatPattern_ "# ### ###")
  "7 123 456"
  Africa

-- | Djibouti
djibouti :: Country
djibouti = country
  (unsafeCountryCode "DJ")
  (unsafeDialCode 253)
  "Djibouti"
  "🇩🇯"
  (formatPattern_ "## ## ## ##")
  "77 12 34 56"
  Africa

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // central africa
-- ═════════════════════════════════════════════════════════════════════════════

centralAfricanCountries :: Array Country
centralAfricanCountries =
  [ democraticRepublicCongo
  , republicCongo
  , cameroon
  , chad
  , centralAfricanRepublic
  , gabon
  , equatorialGuinea
  , saoTome
  ]

-- | Democratic Republic of the Congo
democraticRepublicCongo :: Country
democraticRepublicCongo = country
  (unsafeCountryCode "CD")
  (unsafeDialCode 243)
  "DR Congo"
  "🇨🇩"
  (formatPattern_ "### ### ###")
  "812 345 678"
  Africa

-- | Republic of the Congo
republicCongo :: Country
republicCongo = country
  (unsafeCountryCode "CG")
  (unsafeDialCode 242)
  "Congo"
  "🇨🇬"
  (formatPattern_ "## ### ####")
  "06 123 4567"
  Africa

-- | Cameroon
cameroon :: Country
cameroon = country
  (unsafeCountryCode "CM")
  (unsafeDialCode 237)
  "Cameroon"
  "🇨🇲"
  (formatPattern_ "### ## ## ##")
  "670 12 34 56"
  Africa

-- | Chad
chad :: Country
chad = country
  (unsafeCountryCode "TD")
  (unsafeDialCode 235)
  "Chad"
  "🇹🇩"
  (formatPattern_ "## ## ## ##")
  "66 12 34 56"
  Africa

-- | Central African Republic
centralAfricanRepublic :: Country
centralAfricanRepublic = country
  (unsafeCountryCode "CF")
  (unsafeDialCode 236)
  "Central African Republic"
  "🇨🇫"
  (formatPattern_ "## ## ## ##")
  "70 12 34 56"
  Africa

-- | Gabon
gabon :: Country
gabon = country
  (unsafeCountryCode "GA")
  (unsafeDialCode 241)
  "Gabon"
  "🇬🇦"
  (formatPattern_ "# ## ## ##")
  "6 12 34 56"
  Africa

-- | Equatorial Guinea
equatorialGuinea :: Country
equatorialGuinea = country
  (unsafeCountryCode "GQ")
  (unsafeDialCode 240)
  "Equatorial Guinea"
  "🇬🇶"
  (formatPattern_ "### ### ###")
  "222 123 456"
  Africa

-- | São Tomé and Príncipe
saoTome :: Country
saoTome = country
  (unsafeCountryCode "ST")
  (unsafeDialCode 239)
  "São Tomé and Príncipe"
  "🇸🇹"
  (formatPattern_ "### ####")
  "981 2345"
  Africa

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // southern africa
-- ═════════════════════════════════════════════════════════════════════════════

southernAfricanCountries :: Array Country
southernAfricanCountries =
  [ southAfrica
  , namibia
  , botswana
  , zimbabwe
  , zambia
  , malawi
  , mozambique
  , angola
  , madagascar
  , mauritius
  , lesotho
  , eswatini
  , comoros
  , seychelles
  ]

-- | South Africa
southAfrica :: Country
southAfrica = country
  (unsafeCountryCode "ZA")
  (unsafeDialCode 27)
  "South Africa"
  "🇿🇦"
  (formatPattern_ "## ### ####")
  "71 234 5678"
  Africa

-- | Namibia
namibia :: Country
namibia = country
  (unsafeCountryCode "NA")
  (unsafeDialCode 264)
  "Namibia"
  "🇳🇦"
  (formatPattern_ "## ### ####")
  "81 123 4567"
  Africa

-- | Botswana
botswana :: Country
botswana = country
  (unsafeCountryCode "BW")
  (unsafeDialCode 267)
  "Botswana"
  "🇧🇼"
  (formatPattern_ "## ### ###")
  "71 123 456"
  Africa

-- | Zimbabwe
zimbabwe :: Country
zimbabwe = country
  (unsafeCountryCode "ZW")
  (unsafeDialCode 263)
  "Zimbabwe"
  "🇿🇼"
  (formatPattern_ "## ### ####")
  "71 234 5678"
  Africa

-- | Zambia
zambia :: Country
zambia = country
  (unsafeCountryCode "ZM")
  (unsafeDialCode 260)
  "Zambia"
  "🇿🇲"
  (formatPattern_ "## ### ####")
  "95 123 4567"
  Africa

-- | Malawi
malawi :: Country
malawi = country
  (unsafeCountryCode "MW")
  (unsafeDialCode 265)
  "Malawi"
  "🇲🇼"
  (formatPattern_ "### ## ## ##")
  "991 12 34 56"
  Africa

-- | Mozambique
mozambique :: Country
mozambique = country
  (unsafeCountryCode "MZ")
  (unsafeDialCode 258)
  "Mozambique"
  "🇲🇿"
  (formatPattern_ "## ### ####")
  "82 123 4567"
  Africa

-- | Angola
angola :: Country
angola = country
  (unsafeCountryCode "AO")
  (unsafeDialCode 244)
  "Angola"
  "🇦🇴"
  (formatPattern_ "### ### ###")
  "923 123 456"
  Africa

-- | Madagascar
madagascar :: Country
madagascar = country
  (unsafeCountryCode "MG")
  (unsafeDialCode 261)
  "Madagascar"
  "🇲🇬"
  (formatPattern_ "## ## ### ##")
  "32 12 345 67"
  Africa

-- | Mauritius
mauritius :: Country
mauritius = country
  (unsafeCountryCode "MU")
  (unsafeDialCode 230)
  "Mauritius"
  "🇲🇺"
  (formatPattern_ "#### ####")
  "5123 4567"
  Africa

-- | Lesotho
lesotho :: Country
lesotho = country
  (unsafeCountryCode "LS")
  (unsafeDialCode 266)
  "Lesotho"
  "🇱🇸"
  (formatPattern_ "## ### ###")
  "50 123 456"
  Africa

-- | Eswatini (Swaziland)
eswatini :: Country
eswatini = country
  (unsafeCountryCode "SZ")
  (unsafeDialCode 268)
  "Eswatini"
  "🇸🇿"
  (formatPattern_ "## ## ####")
  "76 12 3456"
  Africa

-- | Comoros
comoros :: Country
comoros = country
  (unsafeCountryCode "KM")
  (unsafeDialCode 269)
  "Comoros"
  "🇰🇲"
  (formatPattern_ "### ## ##")
  "321 23 45"
  Africa

-- | Seychelles
seychelles :: Country
seychelles = country
  (unsafeCountryCode "SC")
  (unsafeDialCode 248)
  "Seychelles"
  "🇸🇨"
  (formatPattern_ "# ### ###")
  "2 510 123"
  Africa
