#!/usr/bin/env runhaskell
-- |
-- Quick script to show base16 theme output
-- Uses the Lean4 color system with 211° hero hue
--

import Lattice.Utils.Base16Theme
import qualified Data.Text.IO as TIO

main :: IO ()
main = do
  putStrLn "=== Base16 Theme: Ono-Sendai Tuned ===\n"
  putStrLn "Hero Hue: 211° (HSL locked)\n"
  
  putStrLn "--- Nix Format ---"
  TIO.putStrLn (paletteToNix "tuned" onoSendaiTuned)
  putStrLn ""
  
  putStrLn "--- CSS Variables ---"
  TIO.putStrLn (paletteToCSS onoSendaiTuned)
  putStrLn ""
  
  putStrLn "--- Hex Values ---"
  mapM_ (\(name, hex) -> putStrLn (name ++ " = " ++ show hex)) (paletteToHex onoSendaiTuned)
