-- Test 18: Try unicode lookalikes to hide violations
-- Should still be caught

module Test where

import Straylight.Script

-- Using Cyrillic С instead of C
badFunction :: Int -> Int
badFunction x = undefСined  -- Cyrillic С

-- Using Greek letters
badFunction2 :: Int -> Int
badFunction2 x = null  -- Should still catch this
