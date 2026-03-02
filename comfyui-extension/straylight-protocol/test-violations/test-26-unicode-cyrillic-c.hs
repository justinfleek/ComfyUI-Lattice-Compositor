-- Test 26: Unicode obfuscation with Cyrillic С (should be caught after fix)

module Test where

import Straylight.Script

-- Using Cyrillic С instead of C to hide undefined
badFunction :: Int -> Int
badFunction x = undefСined  -- Cyrillic С
