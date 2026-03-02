-- Test 11: Try multiline null function call
-- Should be caught by STRAYLIGHT-007

module Test where

import Straylight.Script

badFunction :: [Int] -> Bool
badFunction xs = null
  xs  -- Multiline null call

badFunction2 :: [Int] -> Bool
badFunction2 xs = null
  $ xs  -- Multiline with $
