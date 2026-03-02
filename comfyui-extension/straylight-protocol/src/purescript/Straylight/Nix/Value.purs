-- | High-level interface to Nix values from WASM modules (PureScript)
--
-- This module provides PureScript bindings for the Nix WASM host interface.
-- Values are represented as opaque handles managed by the host.
--
-- PureScript FFI bindings for the same C functions used by Haskell.
module Straylight.Nix.Value where

import Effect (Effect)
import Data.Int (Int64)
import Data.Maybe (Maybe)

-- | A handle to a Nix value in the host evaluator.
-- Opaque type - actual value lives in host memory.
foreign import data Value :: Type

-- | Get the type of a Nix value (returns type ID as Word32)
foreign import getType :: Value -> Effect Int

-- | Panic and warnings
foreign import panic :: String -> Effect Unit
foreign import warn :: String -> Effect Unit

-- | Constructing values
foreign import mkInt :: Int64 -> Effect Value
foreign import mkFloat :: Number -> Effect Value
foreign import mkString :: String -> Effect Value
foreign import mkBool :: Boolean -> Effect Value
foreign import mkNull :: Effect Value
foreign import mkPath :: String -> Effect Value
foreign import mkList :: Array Value -> Effect Value
foreign import mkAttrs :: Array { key :: String, value :: Value } -> Effect Value

-- | Inspecting values
foreign import getInt :: Value -> Effect Int64
foreign import getFloat :: Value -> Effect Number
foreign import getString :: Value -> Effect String
foreign import getBool :: Value -> Effect Boolean
foreign import getPath :: Value -> Effect String
foreign import getList :: Value -> Effect (Array Value)
foreign import getAttrs :: Value -> Effect (Array { key :: String, value :: Value })
foreign import getAttrsLen :: Value -> Effect Int
foreign import getAttr :: Value -> String -> Effect (Maybe Value)
foreign import hasAttr :: Value -> String -> Effect Boolean

-- | Calling Nix functions
foreign import call :: Value -> Value -> Effect Value
foreign import call1 :: Value -> Value -> Effect Value
foreign import call2 :: Value -> Value -> Value -> Effect Value

-- | Module initialization (called by host)
foreign import nixWasmInit :: Effect Unit
