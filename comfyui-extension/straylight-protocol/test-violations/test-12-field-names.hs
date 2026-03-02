-- Test 12: Field names containing "null" (should be ignored)
-- These should NOT be flagged

module Test where

import Straylight.Script

data Config = Config
  { noNull :: Bool
  , null_ :: Maybe Int
  , nullValue :: String
  , _null :: Int
  }

getConfig :: Config -> Bool
getConfig cfg = noNull cfg  -- Should be OK
