-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // phone // database // europe
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | European countries phone database.
-- |
-- | Re-exports from regional submodules for Western and Eastern Europe.

module Hydrogen.Schema.Phone.Database.Europe
  ( europeanCountries
  , module WesternEurope
  , module EasternEurope
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude ((<>))

import Hydrogen.Schema.Phone.Country (Country)

import Hydrogen.Schema.Phone.Database.Europe.Western (westernEuropeanCountries) as WesternEurope
import Hydrogen.Schema.Phone.Database.Europe.Eastern (easternEuropeanCountries) as EasternEurope

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // european countries
-- ═════════════════════════════════════════════════════════════════════════════

-- | All European countries combined.
europeanCountries :: Array Country
europeanCountries = 
  WesternEurope.westernEuropeanCountries 
  <> EasternEurope.easternEuropeanCountries
