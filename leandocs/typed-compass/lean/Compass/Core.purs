module Compass.Core where

import Data.Maybe (Maybe)
import Data.Eq (class Eq)
import Prelude

foreign import Data.Function (runFn)

{-! ## JSON Types -}

data Json
  = JNull
  | JBool Boolean
  | JNumber Number
  | JString String
  | JArray (Array Json)
  | JObject (Object Json)

instance eqJson :: Eq Json where
  eq JNull JNull = True
  eq (JBool b1) (JBool b2) = b1 == b2
  eq (JNumber n1) (JNumber n2) = n1 == n2
  eq (JString s1) (JString s2) = s1 == s2
  eq (JArray a1) (JArray a2) = eq a1 a2
  eq (JObject o1) (JObject o2) = eq o1 o2

{-! ## JSON Accessors -}

jsonToString :: Json -> String
jsonToString (JNull) = "null"
jsonToString (JBool b) = if b then "true" else "false"
jsonToString (JNumber n) = show n
jsonToString (JString s) = s

jsonNull :: Json
jsonNull = JNull

jsonBool :: Boolean -> Json
jsonBool = JBool

jsonNumber :: Number -> Json
jsonNumber = JNumber

jsonString :: String -> Json
jsonString = JString

jsonArray :: forall a. Array a -> Json
jsonArray = JArray

jsonObject :: forall a. Array (Tuple String Json) -> Json
jsonObject = JObject

{-! ## Extractable Class - proof required -}

class Extractable a where
  encode :: a -> Json
  decode :: Json -> Maybe a
  proof :: forall x. decode (encode x) = Just x

{-! ## Base Instances with Proofs -}

instance extractableString :: Extractable String where
  encode = jsonString
  decode = case _ of
    JNull -> Nothing
    JString s -> Just s
    _ -> Nothing
  proof = \x -> case jsonString (encode x) of
    JString s' -> if s' == x then Just s else Nothing
    _ -> Nothing

instance extractableNumber :: Extractable Number where
  encode = jsonNumber
  decode = case _ of
    JNull -> Nothing
    JNumber n -> Just n
    _ -> Nothing
  proof = \x -> case jsonNumber (encode x) of
    JNumber n' -> if n' == x then Just n else Nothing
    _ -> Nothing

instance extractableBool :: Extractable Boolean where
  encode = jsonBool
  decode = case _ of
    JNull -> Nothing
    JBool b -> Just b
    _ -> Nothing
  proof = \x -> case jsonBool (encode x) of
    JBool b' -> if b' == x then Just b else Nothing
    _ -> Nothing
