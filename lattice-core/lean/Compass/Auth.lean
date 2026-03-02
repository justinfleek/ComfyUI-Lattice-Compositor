/-
  Compass.Auth - Authentication types with roundtrip proofs
  Uses Compass.Core JSON infrastructure
-/

import Compass.Core
import Compass.Permissions

namespace Compass.Auth

open Compass.Core Compass.Permissions

/-! ## Organization -/

structure Organization where
  id : String
  name : String
  slug : String
  max_users : Int
  monthly_budget : Float
  is_active : Bool
  created_at : DateTime
  updated_at : DateTime
  deriving Repr

def Organization.toJson (o : Organization) : Json := .obj [
    ("id", .str o.id),
    ("name", .str o.name),
    ("slug", .str o.slug),
    ("max_users", .int o.max_users),
    ("monthly_budget", .num o.monthly_budget),
    ("is_active", .bool o.is_active),
    ("created_at", .str o.created_at),
    ("updated_at", .str o.updated_at)
  ]

def Organization.fromJson (j : Json) : Option Organization := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let name ← Json.fieldN 1 j >>= Json.asString
  let slug ← Json.fieldN 2 j >>= Json.asString
  let max_users ← Json.fieldN 3 j >>= Json.asInt
  let monthly_budget ← Json.fieldN 4 j >>= Json.asFloat
  let is_active ← Json.fieldN 5 j >>= Json.asBool
  let created_at ← Json.fieldN 6 j >>= Json.asString
  let updated_at ← Json.fieldN 7 j >>= Json.asString
  pure ⟨id, name, slug, max_users, monthly_budget, is_active, created_at, updated_at⟩

theorem Organization.roundtrip (o : Organization) :
    Organization.fromJson (Organization.toJson o) = some o := by
  cases o; rfl

instance : Extractable Organization where
  encode := Organization.toJson
  decode := Organization.fromJson
  roundtrip := Organization.roundtrip

/-! ## User -/

structure User where
  id : String
  org_id : String
  name : String
  email : String
  role : Role
  mfa_enabled : Bool
  daily_budget : Float
  monthly_budget : Float
  is_active : Bool
  created_at : DateTime
  updated_at : DateTime
  deriving Repr

def User.toJson (u : User) : Json := .obj [
    ("id", .str u.id),
    ("org_id", .str u.org_id),
    ("name", .str u.name),
    ("email", .str u.email),
    ("role", .str (Role.toString u.role)),
    ("mfa_enabled", .bool u.mfa_enabled),
    ("daily_budget", .num u.daily_budget),
    ("monthly_budget", .num u.monthly_budget),
    ("is_active", .bool u.is_active),
    ("created_at", .str u.created_at),
    ("updated_at", .str u.updated_at)
  ]

def User.fromJson (j : Json) : Option User := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let org_id ← Json.fieldN 1 j >>= Json.asString
  let name ← Json.fieldN 2 j >>= Json.asString
  let email ← Json.fieldN 3 j >>= Json.asString
  let role_str ← Json.fieldN 4 j >>= Json.asString
  let role ← Role.fromString role_str
  let mfa_enabled ← Json.fieldN 5 j >>= Json.asBool
  let daily_budget ← Json.fieldN 6 j >>= Json.asFloat
  let monthly_budget ← Json.fieldN 7 j >>= Json.asFloat
  let is_active ← Json.fieldN 8 j >>= Json.asBool
  let created_at ← Json.fieldN 9 j >>= Json.asString
  let updated_at ← Json.fieldN 10 j >>= Json.asString
  pure ⟨id, org_id, name, email, role, mfa_enabled, daily_budget, monthly_budget, is_active, created_at, updated_at⟩

theorem User.roundtrip (u : User) : User.fromJson (User.toJson u) = some u := by
  cases u with
  | mk id org_id name email role mfa_enabled daily_budget monthly_budget is_active created_at updated_at =>
    cases role <;> rfl

instance : Extractable User where
  encode := User.toJson
  decode := User.fromJson
  roundtrip := User.roundtrip

end Compass.Auth
