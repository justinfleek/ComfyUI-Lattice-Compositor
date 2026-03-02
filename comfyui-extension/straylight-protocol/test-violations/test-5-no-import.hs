-- Test 5: Missing Straylight.Script import
-- This should be caught by STRAYLIGHT-004

module Test where

-- Missing: import Straylight.Script

main :: IO ()
main = putStrLn "Hello"
