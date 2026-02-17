-- Test 2: Lazy code patterns (undefined, null, ??, ||, etc.)
-- This should be caught by STRAYLIGHT-007

module Test where

import Straylight.Script

-- Violation: undefined
badFunction1 :: Int -> Int
badFunction1 x = undefined

-- Violation: null
badFunction2 :: [Int] -> Bool
badFunction2 xs = null xs

-- Violation: Using || as default
badFunction3 :: Maybe Int -> Int
badFunction3 mx = fromMaybe 0 mx || 42

-- Violation: Using ?? (nullish coalescing pattern)
badFunction4 :: Maybe String -> String
badFunction4 ms = case ms of
  Nothing -> "default"
  Just s -> s ?? "fallback"
