-- Test 10: Try qualified null (Data.List.null)
-- Should be caught by STRAYLIGHT-007

module Test where

import Straylight.Script
import Data.List

badFunction :: [Int] -> Bool
badFunction xs = Data.List.null xs  -- Qualified null

badFunction2 :: [Int] -> Bool
badFunction2 xs = Prelude.null xs  -- Prelude.null
