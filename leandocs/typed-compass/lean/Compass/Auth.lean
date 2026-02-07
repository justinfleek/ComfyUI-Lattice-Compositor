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

/-! ## Session -/

structure Session where
  id : String
  user_id : String
  token_hash : String
  created_at : DateTime
  expires_at : DateTime
  last_activity : DateTime
  mfa_verified : Bool
  deriving Repr

def Session.toJson (s : Session) : Json := .obj [
    ("id", .str s.id),
    ("user_id", .str s.user_id),
    ("token_hash", .str s.token_hash),
    ("created_at", .str s.created_at),
    ("expires_at", .str s.expires_at),
    ("last_activity", .str s.last_activity),
    ("mfa_verified", .bool s.mfa_verified)
  ]

def Session.fromJson (j : Json) : Option Session := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let user_id ← Json.fieldN 1 j >>= Json.asString
  let token_hash ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let expires_at ← Json.fieldN 4 j >>= Json.asString
  let last_activity ← Json.fieldN 5 j >>= Json.asString
  let mfa_verified ← Json.fieldN 6 j >>= Json.asBool
  pure ⟨id, user_id, token_hash, created_at, expires_at, last_activity, mfa_verified⟩

theorem Session.roundtrip (s : Session) :
    Session.fromJson (Session.toJson s) = some s := by
  cases s; rfl

instance : Extractable Session where
  encode := Session.toJson
  decode := Session.fromJson
  roundtrip := Session.roundtrip

/-! ## Session Invariants -/

def Session.isValid (s : Session) : Prop :=
  s.mfa_verified = true

/-! THEOREM: Session requires MFA verification -/
theorem session_requires_mfa (s : Session) (h : s.isValid) :
    s.mfa_verified = true := h

/-! ## APIKey -/

structure APIKey where
  id : String
  org_id : String
  user_id : String
  key_prefix : String
  key_hash : String
  name : String
  description : String
  is_active : Bool
  created_at : DateTime
  deriving Repr

def APIKey.toJson (k : APIKey) : Json := .obj [
    ("id", .str k.id),
    ("org_id", .str k.org_id),
    ("user_id", .str k.user_id),
    ("key_prefix", .str k.key_prefix),
    ("key_hash", .str k.key_hash),
    ("name", .str k.name),
    ("description", .str k.description),
    ("is_active", .bool k.is_active),
    ("created_at", .str k.created_at)
  ]

def APIKey.fromJson (j : Json) : Option APIKey := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let org_id ← Json.fieldN 1 j >>= Json.asString
  let user_id ← Json.fieldN 2 j >>= Json.asString
  let key_prefix ← Json.fieldN 3 j >>= Json.asString
  let key_hash ← Json.fieldN 4 j >>= Json.asString
  let name ← Json.fieldN 5 j >>= Json.asString
  let description ← Json.fieldN 6 j >>= Json.asString
  let is_active ← Json.fieldN 7 j >>= Json.asBool
  let created_at ← Json.fieldN 8 j >>= Json.asString
  pure ⟨id, org_id, user_id, key_prefix, key_hash, name, description, is_active, created_at⟩

theorem APIKey.roundtrip (k : APIKey) :
    APIKey.fromJson (APIKey.toJson k) = some k := by
  cases k; rfl

instance : Extractable APIKey where
  encode := APIKey.toJson
  decode := APIKey.fromJson
  roundtrip := APIKey.roundtrip

/-! ## Security Invariants -/

def APIKey.prefixValid (k : APIKey) : Prop :=
  k.key_prefix.length = 8 ∧ k.key_prefix.startsWith "flk_"

/-! THEOREM: Valid API key prefix starts with flk_ -/
theorem apikey_prefix_format (k : APIKey) (h : k.prefixValid) :
    k.key_prefix.startsWith "flk_" := h.2

end Compass.Auth
