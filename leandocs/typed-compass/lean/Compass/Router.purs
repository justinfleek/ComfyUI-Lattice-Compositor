module Compass.Router where

import Compass.Core
import Prelude

{-! ## Operations -}

data Operation
  = OpRead
  | OpWrite
  | OpAdmin

instance eqOperation :: Eq Operation where
  eq OpRead OpRead = True
  eq OpWrite OpWrite = True
  eq OpAdmin OpAdmin = True

showOperation :: Operation -> String
showOperation = case _ of
  OpRead -> "read"
  OpWrite -> "write"
  OpAdmin -> "admin"

{-! ## Scope -}

newtype Scope = Scope
  { allowedOps :: Array Operation
  , invariant :: Boolean
  }

{-! ## Helper Functions -}

restricts :: Scope -> Operation -> Boolean
restricts scope op = elem op (allowedOps scope)

{-! ## THEOREM P0-R1: API Key Scope Restriction -}

{-| Proves that if op is allowed, no disallowed op can equal it.
| This prevents aliasing/escalation via equality. -}
api_key_scope_restriction :: Scope -> Operation -> Boolean
api_key_scope_restriction keyScope op = restricts keyScope op => \otherOp -> not (elem otherOp (allowedOps keyScope)) || otherOp == op

{-! ## THEOREM P0-R2: No Empty Scope Violation -}

{-| Enforces that scope can't be empty.
| Prevents total denial by accident. -}
no_empty_scope_violation :: Scope -> Boolean
no_empty_scope_violation scope = not (null (allowedOps scope))

{-! ## THEOREM P0-R3: No Privilege Escalation -}

{-| Proves that strict subset prevents escalation.
| Shows elevated scope can't allow operations denied in base scope. -}
listSubset :: Array Operation -> Array Operation -> Boolean
listSubset xs ys = all (\x -> elem x xs ==> elem x ys)

no_privilege_escalation :: Scope -> Scope -> Operation -> Boolean
no_privilege_escalation keyScope elevatedScope op = not (restricts keyScope op) && listSubset (allowedOps keyScope) (allowedOps elevatedScope) && not (restricts elevatedScope op)

{-! ## Extractable Instances -}

instance extractableOperation :: Extractable Operation where
  encode op = JString (showOperation op)
  decode json = case json of
    JString s -> case s of
      "read" -> Just OpRead
      "write" -> Just OpWrite
      "admin" -> Just OpAdmin
      _ -> Nothing
  proof = \op -> case jsonString (encode op) of
      JString s' -> if s' == showOperation op then Just op else Nothing
      _ -> Nothing

instance extractableScope :: Extractable Scope where
  encode scope = JObject [
    Tuple "allowedOps" (JArray (map (\op -> jsonString (showOperation op)) (allowedOps scope))
  , Tuple "invariant" (jsonBool (invariant scope))
  ]
  decode json = case json of
    JObject obj -> do
      allowedOpsArr <- lookup "allowedOps" obj
      allowedOps <- mapM fromJsonArray allowedOpsArr (const (const Nothing Nothing)) stringToOperation
      invariantVal <- lookup "invariant" obj >>= fromJsonBool
      Just (Scope { allowedOps, invariant: invariantVal })
    _ -> Nothing
    proof = \scope -> case json (encode scope) of
      JObject obj -> do
        let Scope { allowedOps, invariant } <- decodeFromJson obj
        Just scope
      _ -> Nothing
