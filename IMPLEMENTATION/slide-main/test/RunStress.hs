module Main where

import Test.Hspec (hspec)
import qualified StressSpec

main :: IO ()
main = hspec StressSpec.spec
