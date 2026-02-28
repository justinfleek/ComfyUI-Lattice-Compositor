-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // phone // database // caribbean
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Caribbean countries phone database.
-- |
-- | Includes Caribbean island nations and territories.
-- | Many use the North American Numbering Plan (NANP) with +1 dial code.

module Hydrogen.Schema.Phone.Database.Caribbean
  ( caribbeanCountries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Phone.Country 
  ( Country
  , country
  , formatPattern_
  , Region(Caribbean)
  )
import Hydrogen.Schema.Phone.CountryCode (unsafeCountryCode)
import Hydrogen.Schema.Phone.DialCode (unsafeDialCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // caribbean countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | All Caribbean countries and territories.
caribbeanCountries :: Array Country
caribbeanCountries =
  [ cuba
  , dominicanRepublic
  , haiti
  , jamaica
  , puertoRico
  , trinidad
  , bahamas
  , barbados
  , saintLucia
  , grenada
  , saintVincent
  , antiguaBarbuda
  , dominica
  , saintKitts
  , curacao
  , aruba
  , usVirginIslands
  , britishVirginIslands
  , caymanIslands
  , turksAndCaicos
  , martinique
  , guadeloupe
  , bermuda
  ]

-- | Cuba
cuba :: Country
cuba = country
  (unsafeCountryCode "CU")
  (unsafeDialCode 53)
  "Cuba"
  "🇨🇺"
  (formatPattern_ "# ### ####")
  "5 123 4567"
  Caribbean

-- | Dominican Republic
dominicanRepublic :: Country
dominicanRepublic = country
  (unsafeCountryCode "DO")
  (unsafeDialCode 1)
  "Dominican Republic"
  "🇩🇴"
  (formatPattern_ "(###) ###-####")
  "(809) 123-4567"
  Caribbean

-- | Haiti
haiti :: Country
haiti = country
  (unsafeCountryCode "HT")
  (unsafeDialCode 509)
  "Haiti"
  "🇭🇹"
  (formatPattern_ "## ## ####")
  "34 12 3456"
  Caribbean

-- | Jamaica
jamaica :: Country
jamaica = country
  (unsafeCountryCode "JM")
  (unsafeDialCode 1)
  "Jamaica"
  "🇯🇲"
  (formatPattern_ "(###) ###-####")
  "(876) 123-4567"
  Caribbean

-- | Puerto Rico (US territory)
puertoRico :: Country
puertoRico = country
  (unsafeCountryCode "PR")
  (unsafeDialCode 1)
  "Puerto Rico"
  "🇵🇷"
  (formatPattern_ "(###) ###-####")
  "(787) 123-4567"
  Caribbean

-- | Trinidad and Tobago
trinidad :: Country
trinidad = country
  (unsafeCountryCode "TT")
  (unsafeDialCode 1)
  "Trinidad and Tobago"
  "🇹🇹"
  (formatPattern_ "(###) ###-####")
  "(868) 123-4567"
  Caribbean

-- | Bahamas
bahamas :: Country
bahamas = country
  (unsafeCountryCode "BS")
  (unsafeDialCode 1)
  "Bahamas"
  "🇧🇸"
  (formatPattern_ "(###) ###-####")
  "(242) 123-4567"
  Caribbean

-- | Barbados
barbados :: Country
barbados = country
  (unsafeCountryCode "BB")
  (unsafeDialCode 1)
  "Barbados"
  "🇧🇧"
  (formatPattern_ "(###) ###-####")
  "(246) 123-4567"
  Caribbean

-- | Saint Lucia
saintLucia :: Country
saintLucia = country
  (unsafeCountryCode "LC")
  (unsafeDialCode 1)
  "Saint Lucia"
  "🇱🇨"
  (formatPattern_ "(###) ###-####")
  "(758) 123-4567"
  Caribbean

-- | Grenada
grenada :: Country
grenada = country
  (unsafeCountryCode "GD")
  (unsafeDialCode 1)
  "Grenada"
  "🇬🇩"
  (formatPattern_ "(###) ###-####")
  "(473) 123-4567"
  Caribbean

-- | Saint Vincent and the Grenadines
saintVincent :: Country
saintVincent = country
  (unsafeCountryCode "VC")
  (unsafeDialCode 1)
  "Saint Vincent"
  "🇻🇨"
  (formatPattern_ "(###) ###-####")
  "(784) 123-4567"
  Caribbean

-- | Antigua and Barbuda
antiguaBarbuda :: Country
antiguaBarbuda = country
  (unsafeCountryCode "AG")
  (unsafeDialCode 1)
  "Antigua and Barbuda"
  "🇦🇬"
  (formatPattern_ "(###) ###-####")
  "(268) 123-4567"
  Caribbean

-- | Dominica
dominica :: Country
dominica = country
  (unsafeCountryCode "DM")
  (unsafeDialCode 1)
  "Dominica"
  "🇩🇲"
  (formatPattern_ "(###) ###-####")
  "(767) 123-4567"
  Caribbean

-- | Saint Kitts and Nevis
saintKitts :: Country
saintKitts = country
  (unsafeCountryCode "KN")
  (unsafeDialCode 1)
  "Saint Kitts and Nevis"
  "🇰🇳"
  (formatPattern_ "(###) ###-####")
  "(869) 123-4567"
  Caribbean

-- | Curaçao
curacao :: Country
curacao = country
  (unsafeCountryCode "CW")
  (unsafeDialCode 599)
  "Curaçao"
  "🇨🇼"
  (formatPattern_ "# ### ####")
  "9 512 3456"
  Caribbean

-- | Aruba
aruba :: Country
aruba = country
  (unsafeCountryCode "AW")
  (unsafeDialCode 297)
  "Aruba"
  "🇦🇼"
  (formatPattern_ "### ####")
  "560 1234"
  Caribbean

-- | US Virgin Islands
usVirginIslands :: Country
usVirginIslands = country
  (unsafeCountryCode "VI")
  (unsafeDialCode 1)
  "US Virgin Islands"
  "🇻🇮"
  (formatPattern_ "(###) ###-####")
  "(340) 123-4567"
  Caribbean

-- | British Virgin Islands
britishVirginIslands :: Country
britishVirginIslands = country
  (unsafeCountryCode "VG")
  (unsafeDialCode 1)
  "British Virgin Islands"
  "🇻🇬"
  (formatPattern_ "(###) ###-####")
  "(284) 123-4567"
  Caribbean

-- | Cayman Islands
caymanIslands :: Country
caymanIslands = country
  (unsafeCountryCode "KY")
  (unsafeDialCode 1)
  "Cayman Islands"
  "🇰🇾"
  (formatPattern_ "(###) ###-####")
  "(345) 123-4567"
  Caribbean

-- | Turks and Caicos Islands
turksAndCaicos :: Country
turksAndCaicos = country
  (unsafeCountryCode "TC")
  (unsafeDialCode 1)
  "Turks and Caicos"
  "🇹🇨"
  (formatPattern_ "(###) ###-####")
  "(649) 123-4567"
  Caribbean

-- | Martinique (French territory)
martinique :: Country
martinique = country
  (unsafeCountryCode "MQ")
  (unsafeDialCode 596)
  "Martinique"
  "🇲🇶"
  (formatPattern_ "### ## ## ##")
  "696 12 34 56"
  Caribbean

-- | Guadeloupe (French territory)
guadeloupe :: Country
guadeloupe = country
  (unsafeCountryCode "GP")
  (unsafeDialCode 590)
  "Guadeloupe"
  "🇬🇵"
  (formatPattern_ "### ## ## ##")
  "690 12 34 56"
  Caribbean

-- | Bermuda
bermuda :: Country
bermuda = country
  (unsafeCountryCode "BM")
  (unsafeDialCode 1)
  "Bermuda"
  "🇧🇲"
  (formatPattern_ "(###) ###-####")
  "(441) 123-4567"
  Caribbean
