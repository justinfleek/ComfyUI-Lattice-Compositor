#!/usr/bin/env runhaskell
-- |
-- Script to generate base16 color theme using the Lean4 color system
-- Outputs Nix format matching ono-sendai.nix structure
--

import Lattice.Utils.Base16Theme
import qualified Data.Text.IO as TIO

main :: IO ()
main = do
  putStrLn "-- Generated base16 theme using Lean4 color system (211° hero hue)"
  putStrLn ""
  
  putStrLn "-- Ono-Sendai Tuned (L=11% background)"
  TIO.putStrLn (paletteToNix "tuned" onoSendaiTuned)
  putStrLn ""
  
  putStrLn "-- Ono-Sendai GitHub (L=16% background)"
  TIO.putStrLn (paletteToNix "github" onoSendaiGithub)
  putStrLn ""
  
  putStrLn "-- Ono-Sendai Memphis (L=0% background - pure black)"
  TIO.putStrLn (paletteToNix "memphis" onoSendaiMemphis)
  putStrLn ""
  
  putStrLn "-- Ono-Sendai Chiba (L=4% background)"
  TIO.putStrLn (paletteToNix "chiba" onoSendaiChiba)
  putStrLn ""
  
  putStrLn "-- Ono-Sendai Razorgirl (L=8% background)"
  TIO.putStrLn (paletteToNix "razorgirl" onoSendaiRazorgirl)
  putStrLn ""
  
  putStrLn "-- Ono-Sendai Sprawl (L=11% background - best compromise)"
  TIO.putStrLn (paletteToNix "sprawl" onoSendaiSprawl)
