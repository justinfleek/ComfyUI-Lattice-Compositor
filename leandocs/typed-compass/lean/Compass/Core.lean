/-!
  Compass.Core - JSON infrastructure for COMPASS types

  This module provides:
  - Custom JSON type (no external dependencies)
  - Extractable typeclass with roundtrip proof requirement
  - Base instances for primitives
  - Helper functions for encoding/decoding

  All types in COMPASS must implement Extractable with proven roundtrip.
-/

namespace Compass.Core

/-! ## Type Aliases -/

abbrev DateTime := String  -- ISO 8601 format

/-! ## Security Constants -/

def SECURITY_SIGNIFICANCE_LEVEL : Float := 0.001
def CRYPTO_SECURITY_BITS : Nat := 256
def MAX_FAILURE_PROBABILITY : Float := 1e-9

/-! ## JSON Model -/

inductive Json where
  | null : Json
  | bool : Bool → Json
  | int : Int → Json
  | num : Float → Json
  | str : String → Json
  | arr : List Json → Json
  | obj : List (String × Json) → Json
  deriving Repr, Inhabited

/-! ## JSON Accessors -/

def Json.asString : Json → Option String
  | .str s => some s
  | _ => none

def Json.asBool : Json → Option Bool
  | .bool b => some b
  | _ => none

def Json.asInt : Json → Option Int
  | .int n => some n
  | _ => none

def Json.asFloat : Json → Option Float
  | .num n => some n
  | _ => none

/-! ## JSON Field Accessors -/

/-- Access the nth field value of a JSON object by index -/
def Json.fieldN (n : Nat) : Json → Option Json
  | .obj fields => 
    match fields[n]? with
    | some (_, v) => some v
    | none => none
  | _ => none

/-- Encode an optional string field -/
def Json.encodeOptString : Option String → Json
  | some s => .str s
  | none => .null

/-- Decode an optional string field -/  
def Json.decodeOptString : Json → Option (Option String)
  | .str s => some (some s)
  | .null => some none
  | _ => none

/-! ## Extractable Typeclass -/

/-- Typeclass for types that can be extracted to/from JSON with roundtrip proofs -/
class Extractable (α : Type) where
  encode : α → Json
  decode : Json → Option α
  roundtrip : ∀ x, decode (encode x) = some x

/-! ## Simp Lemmas -/

@[simp] theorem Json.asString_str (s : String) : (Json.str s).asString = some s := rfl
@[simp] theorem Json.asBool_bool (b : Bool) : (Json.bool b).asBool = some b := rfl
@[simp] theorem Json.asInt_int (n : Int) : (Json.int n).asInt = some n := rfl
@[simp] theorem Json.asFloat_num (n : Float) : (Json.num n).asFloat = some n := rfl
@[simp] theorem Json.decodeOptString_str (s : String) : Json.decodeOptString (.str s) = some (some s) := rfl
@[simp] theorem Json.decodeOptString_null : Json.decodeOptString .null = some none := rfl
@[simp] theorem Json.encodeOptString_some (s : String) : Json.encodeOptString (some s) = .str s := rfl
@[simp] theorem Json.encodeOptString_none : Json.encodeOptString none = .null := rfl

/-! ## Base Extractable Instances -/

instance : Extractable String where
  encode := Json.str
  decode := Json.asString
  roundtrip _ := rfl

instance : Extractable Bool where
  encode := Json.bool
  decode := Json.asBool
  roundtrip b := by cases b <;> rfl

instance : Extractable Int where
  encode := Json.int
  decode := Json.asInt
  roundtrip _ := rfl

instance : Extractable Float where
  encode := Json.num
  decode := Json.asFloat
  roundtrip _ := rfl

end Compass.Core
