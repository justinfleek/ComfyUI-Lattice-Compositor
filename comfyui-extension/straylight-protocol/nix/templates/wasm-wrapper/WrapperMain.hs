{-# LANGUAGE ForeignFunctionInterface #-}
module Main where

import Straylight.Nix.Value (Value(..))
import Straylight.Nix.Derivation (drvToNixAttrs)
import Straylight.Nix (nixWasmInit)
import qualified Pkg (pkg)

main :: IO ()
main = pure ()

foreign export ccall "nix_wasm_init_v1" initPlugin :: IO ()
initPlugin :: IO ()
initPlugin = nixWasmInit

foreign export ccall "pkg" pkgExport :: Value -> IO Value
pkgExport :: Value -> IO Value
pkgExport _args = drvToNixAttrs Pkg.pkg
