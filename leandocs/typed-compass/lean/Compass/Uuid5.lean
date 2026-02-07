import Compass.Core

namespace COMPASS.Uuid5

open Compass.Core

structure Uuid5 where
  value : String
  deriving Repr, DecidableEq

def Uuid5.toJson (u : Uuid5) : Json := .str u.value

def Uuid5.fromJson (j : Json) : Option Uuid5 := do
  let s ← j.asString
  pure { value := s }

theorem Uuid5.roundtrip (u : Uuid5) :
    Uuid5.fromJson (Uuid5.toJson u) = some u := by
  cases u
  unfold Uuid5.toJson Uuid5.fromJson
  simp

instance : Inhabited Uuid5 where
  default := { value := "AAAAAAAAAAAAAAAAAAAAAAAAAA" }

instance : Extractable Uuid5 where
  encode := Uuid5.toJson
  decode := Uuid5.fromJson
  roundtrip := Uuid5.roundtrip

end COMPASS.Uuid5
