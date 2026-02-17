-- Test 36: PureScript unsafe patterns (should be caught)

module Test where

import Straylight.Script

-- Violations:
badFunction1 :: Int -> Int
badFunction1 x = unsafeCoerce x

badFunction2 :: Int -> Int
badFunction2 x = unsafePartial (x `div` 0)

badFunction3 :: Effect Unit
badFunction3 = unsafePerformEffect (log "bad")
