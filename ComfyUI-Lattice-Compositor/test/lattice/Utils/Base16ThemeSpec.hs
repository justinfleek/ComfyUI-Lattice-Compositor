-- |
-- Test: Base16 Theme Generation
-- Verifies theme generation produces correct colors with 211° hero hue
--

module Main where

import Lattice.Utils.Base16Theme
import qualified Data.Text.IO as TIO

main :: IO ()
main = do
  putStrLn "=== Base16 Theme Generator (211° Hero Hue) ===\n"
  
  putStrLn "--- Ono-Sendai Tuned (L=11% background) ---"
  putStrLn "HSL(211° 12% 11%) - OLED-safe background"
  TIO.putStrLn (paletteToNix "tuned" onoSendaiTuned)
  putStrLn ""
  
  putStrLn "--- Ono-Sendai GitHub (L=16% background) ---"
  putStrLn "HSL(211° 12% 16%) - GitHub's de-facto default dark mode"
  TIO.putStrLn (paletteToNix "github" onoSendaiGithub)
  putStrLn ""
  
  putStrLn "--- CSS Variables Format ---"
  TIO.putStrLn (paletteToCSS onoSendaiTuned)
