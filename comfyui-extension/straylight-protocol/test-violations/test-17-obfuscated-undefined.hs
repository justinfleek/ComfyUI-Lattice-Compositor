-- Test 17: Try to obfuscate undefined
-- Should still be caught

module Test where

import Straylight.Script

-- Try splitting across lines:
badFunction :: Int -> Int
badFunction x = undef
  ined

-- Try with spaces:
badFunction2 :: Int -> Int
badFunction2 x = undef ined

-- Try with comments in between:
badFunction3 :: Int -> Int
badFunction3 x = undef -- comment
  ined
