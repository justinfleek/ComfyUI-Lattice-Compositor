-- Test 7: Try to hide violations in string literals
-- This should be ignored (strings are not code)

module Test where

import Straylight.Script

main :: IO ()
main = putStrLn "This string contains undefined null ?? || but should be ignored"

-- But actual violations should still be caught:
badFunction :: Int -> Int
badFunction x = undefined
