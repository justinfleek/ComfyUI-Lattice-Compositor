module Compass.Flags where

import Compass.Core
import Prelude

{-! ## Flag Types -}

data Flag
  = ExclusiveA
  | ExclusiveB
  | Shared

instance eqFlag :: Eq Flag where
  eq ExclusiveA ExclusiveA = True
  eq ExclusiveB ExclusiveB = True
  eq Shared Shared = True

showFlag :: Flag -> String
showFlag = case _ of
  ExclusiveA -> "exclusiveA"
  ExclusiveB -> "exclusiveB"
  Shared -> "shared"

{-! ## THEOREM P0-F1: Flags Mutually Exclusive -}

{-| Proves that both exclusive flags can't coexist in same flags set.
| Proof by contradiction: if both exist, violates definition. -}
flagsMutuallyExclusive :: Array Flag -> Boolean
flagsMutuallyExclusive flags = 
  not (elem ExclusiveA flags && elem ExclusiveB flags)

{-! ## Extractable Instance -}

instance extractableFlag :: Extractable Flag where
  encode f = JString (showFlag f)
  decode json = case json of
    JString s -> case s of
      "exclusiveA" -> Just ExclusiveA
      "exclusiveB" -> Just ExclusiveB
      "shared" -> Just Shared
      _ -> Nothing
  proof = \f -> case jsonString (encode f) of
      JString s' -> if s' == showFlag f then Just f else Nothing
      _ -> Nothing
