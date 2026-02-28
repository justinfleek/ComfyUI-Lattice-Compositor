-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // phone // database // south-america
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | South American countries phone database.
-- |
-- | Includes all sovereign nations in South America.

module Hydrogen.Schema.Phone.Database.SouthAmerica
  ( southAmericanCountries
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Hydrogen.Schema.Phone.Country 
  ( Country
  , country
  , formatPattern_
  , Region(SouthAmerica)
  )
import Hydrogen.Schema.Phone.CountryCode (unsafeCountryCode)
import Hydrogen.Schema.Phone.DialCode (unsafeDialCode)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // south american countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | All South American countries.
southAmericanCountries :: Array Country
southAmericanCountries =
  [ brazil
  , argentina
  , colombia
  , peru
  , venezuela
  , chile
  , ecuador
  , bolivia
  , paraguay
  , uruguay
  , guyana
  , suriname
  , frenchGuiana
  ]

-- | Brazil
brazil :: Country
brazil = country
  (unsafeCountryCode "BR")
  (unsafeDialCode 55)
  "Brazil"
  "🇧🇷"
  (formatPattern_ "(##) #####-####")
  "(11) 91234-5678"
  SouthAmerica

-- | Argentina
argentina :: Country
argentina = country
  (unsafeCountryCode "AR")
  (unsafeDialCode 54)
  "Argentina"
  "🇦🇷"
  (formatPattern_ "## ####-####")
  "11 1234-5678"
  SouthAmerica

-- | Colombia
colombia :: Country
colombia = country
  (unsafeCountryCode "CO")
  (unsafeDialCode 57)
  "Colombia"
  "🇨🇴"
  (formatPattern_ "### ### ####")
  "310 123 4567"
  SouthAmerica

-- | Peru
peru :: Country
peru = country
  (unsafeCountryCode "PE")
  (unsafeDialCode 51)
  "Peru"
  "🇵🇪"
  (formatPattern_ "### ### ###")
  "912 345 678"
  SouthAmerica

-- | Venezuela
venezuela :: Country
venezuela = country
  (unsafeCountryCode "VE")
  (unsafeDialCode 58)
  "Venezuela"
  "🇻🇪"
  (formatPattern_ "###-#######")
  "412-1234567"
  SouthAmerica

-- | Chile
chile :: Country
chile = country
  (unsafeCountryCode "CL")
  (unsafeDialCode 56)
  "Chile"
  "🇨🇱"
  (formatPattern_ "# #### ####")
  "9 1234 5678"
  SouthAmerica

-- | Ecuador
ecuador :: Country
ecuador = country
  (unsafeCountryCode "EC")
  (unsafeDialCode 593)
  "Ecuador"
  "🇪🇨"
  (formatPattern_ "## ### ####")
  "99 123 4567"
  SouthAmerica

-- | Bolivia
bolivia :: Country
bolivia = country
  (unsafeCountryCode "BO")
  (unsafeDialCode 591)
  "Bolivia"
  "🇧🇴"
  (formatPattern_ "# ### ####")
  "7 123 4567"
  SouthAmerica

-- | Paraguay
paraguay :: Country
paraguay = country
  (unsafeCountryCode "PY")
  (unsafeDialCode 595)
  "Paraguay"
  "🇵🇾"
  (formatPattern_ "### ### ###")
  "981 123 456"
  SouthAmerica

-- | Uruguay
uruguay :: Country
uruguay = country
  (unsafeCountryCode "UY")
  (unsafeDialCode 598)
  "Uruguay"
  "🇺🇾"
  (formatPattern_ "## ### ###")
  "91 234 567"
  SouthAmerica

-- | Guyana
guyana :: Country
guyana = country
  (unsafeCountryCode "GY")
  (unsafeDialCode 592)
  "Guyana"
  "🇬🇾"
  (formatPattern_ "### ####")
  "612 3456"
  SouthAmerica

-- | Suriname
suriname :: Country
suriname = country
  (unsafeCountryCode "SR")
  (unsafeDialCode 597)
  "Suriname"
  "🇸🇷"
  (formatPattern_ "###-####")
  "812-3456"
  SouthAmerica

-- | French Guiana (Overseas France)
frenchGuiana :: Country
frenchGuiana = country
  (unsafeCountryCode "GF")
  (unsafeDialCode 594)
  "French Guiana"
  "🇬🇫"
  (formatPattern_ "### ## ## ##")
  "694 12 34 56"
  SouthAmerica
