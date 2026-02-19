/-
  Compass.Permissions - Permission and Role types with Extractable instances
-/

import Compass.Core

namespace Compass.Permissions

open Compass.Core

/-! ## Permission Enum -/

inductive Permission where
  -- Twitter
  | TWITTER_READ : Permission
  | TWITTER_WRITE : Permission
  | TWITTER_DELETE : Permission
  -- Reddit
  | REDDIT_READ : Permission
  | REDDIT_WRITE : Permission
  -- LinkedIn
  | LINKEDIN_READ : Permission
  | LINKEDIN_WRITE : Permission
  -- Mastodon
  | MASTODON_READ : Permission
  | MASTODON_WRITE : Permission
  -- LLM
  | LLM_LOCAL : Permission
  | LLM_API : Permission
  | LLM_EXPENSIVE : Permission
  -- Search
  | SEARCH_WEB : Permission
  | SEARCH_NEWS : Permission
  -- Internal
  | CONTENT_CREATE : Permission
  | CONTENT_APPROVE : Permission
  | CONTENT_PUBLISH : Permission
  | CAMPAIGN_MANAGE : Permission
  -- Lattice-specific permissions
  | EXPORT_VIDEO : Permission
  | AI_GENERATE : Permission
  | LAYER_CREATE : Permission
  | LAYER_MODIFY : Permission
  -- Admin
  | ADMIN_USERS : Permission
  | ADMIN_BUDGETS : Permission
  | ADMIN_AUDIT : Permission
  deriving Repr, DecidableEq, Inhabited

def Permission.toString : Permission → String
  | .TWITTER_READ => "TWITTER_READ"
  | .TWITTER_WRITE => "TWITTER_WRITE"
  | .TWITTER_DELETE => "TWITTER_DELETE"
  | .REDDIT_READ => "REDDIT_READ"
  | .REDDIT_WRITE => "REDDIT_WRITE"
  | .LINKEDIN_READ => "LINKEDIN_READ"
  | .LINKEDIN_WRITE => "LINKEDIN_WRITE"
  | .MASTODON_READ => "MASTODON_READ"
  | .MASTODON_WRITE => "MASTODON_WRITE"
  | .LLM_LOCAL => "LLM_LOCAL"
  | .LLM_API => "LLM_API"
  | .LLM_EXPENSIVE => "LLM_EXPENSIVE"
  | .SEARCH_WEB => "SEARCH_WEB"
  | .SEARCH_NEWS => "SEARCH_NEWS"
  | .CONTENT_CREATE => "CONTENT_CREATE"
  | .CONTENT_APPROVE => "CONTENT_APPROVE"
  | .CONTENT_PUBLISH => "CONTENT_PUBLISH"
  | .CAMPAIGN_MANAGE => "CAMPAIGN_MANAGE"
  | .EXPORT_VIDEO => "EXPORT_VIDEO"
  | .AI_GENERATE => "AI_GENERATE"
  | .LAYER_CREATE => "LAYER_CREATE"
  | .LAYER_MODIFY => "LAYER_MODIFY"
  | .ADMIN_USERS => "ADMIN_USERS"
  | .ADMIN_BUDGETS => "ADMIN_BUDGETS"
  | .ADMIN_AUDIT => "ADMIN_AUDIT"

def Permission.fromString : String → Option Permission
  | "TWITTER_READ" => some .TWITTER_READ
  | "TWITTER_WRITE" => some .TWITTER_WRITE
  | "TWITTER_DELETE" => some .TWITTER_DELETE
  | "REDDIT_READ" => some .REDDIT_READ
  | "REDDIT_WRITE" => some .REDDIT_WRITE
  | "LINKEDIN_READ" => some .LINKEDIN_READ
  | "LINKEDIN_WRITE" => some .LINKEDIN_WRITE
  | "MASTODON_READ" => some .MASTODON_READ
  | "MASTODON_WRITE" => some .MASTODON_WRITE
  | "LLM_LOCAL" => some .LLM_LOCAL
  | "LLM_API" => some .LLM_API
  | "LLM_EXPENSIVE" => some .LLM_EXPENSIVE
  | "SEARCH_WEB" => some .SEARCH_WEB
  | "SEARCH_NEWS" => some .SEARCH_NEWS
  | "CONTENT_CREATE" => some .CONTENT_CREATE
  | "CONTENT_APPROVE" => some .CONTENT_APPROVE
  | "CONTENT_PUBLISH" => some .CONTENT_PUBLISH
  | "CAMPAIGN_MANAGE" => some .CAMPAIGN_MANAGE
  | "EXPORT_VIDEO" => some .EXPORT_VIDEO
  | "AI_GENERATE" => some .AI_GENERATE
  | "LAYER_CREATE" => some .LAYER_CREATE
  | "LAYER_MODIFY" => some .LAYER_MODIFY
  | "ADMIN_USERS" => some .ADMIN_USERS
  | "ADMIN_BUDGETS" => some .ADMIN_BUDGETS
  | "ADMIN_AUDIT" => some .ADMIN_AUDIT
  | _ => none

theorem permission_roundtrip (p : Permission) :
    Permission.fromString (Permission.toString p) = some p := by
  cases p <;> rfl

instance : Extractable Permission where
  encode p := .str (Permission.toString p)
  decode j := do
    let s ← j.asString
    Permission.fromString s
  roundtrip p := by simp [Json.asString, permission_roundtrip]

/-! ## Role Enum -/

inductive Role where
  | ADMIN : Role
  | MANAGER : Role
  | CREATOR : Role
  | VIEWER : Role
  deriving Repr, DecidableEq, Inhabited

def Role.toString : Role → String
  | .ADMIN => "ADMIN"
  | .MANAGER => "MANAGER"
  | .CREATOR => "CREATOR"
  | .VIEWER => "VIEWER"

def Role.fromString : String → Option Role
  | "ADMIN" => some .ADMIN
  | "MANAGER" => some .MANAGER
  | "CREATOR" => some .CREATOR
  | "VIEWER" => some .VIEWER
  | _ => none

theorem role_roundtrip (r : Role) :
    Role.fromString (Role.toString r) = some r := by
  cases r <;> rfl

instance : Extractable Role where
  encode r := .str (Role.toString r)
  decode j := do
    let s ← j.asString
    Role.fromString s
  roundtrip r := by simp [Json.asString, role_roundtrip]

/-! ## Role → Permissions mapping -/

def Role.defaultPermissions : Role → List Permission
  | .ADMIN => [
      .TWITTER_READ, .TWITTER_WRITE, .TWITTER_DELETE,
      .REDDIT_READ, .REDDIT_WRITE,
      .LINKEDIN_READ, .LINKEDIN_WRITE,
      .MASTODON_READ, .MASTODON_WRITE,
      .LLM_LOCAL, .LLM_API, .LLM_EXPENSIVE,
      .SEARCH_WEB, .SEARCH_NEWS,
      .CONTENT_CREATE, .CONTENT_APPROVE, .CONTENT_PUBLISH,
      .CAMPAIGN_MANAGE,
      .EXPORT_VIDEO, .AI_GENERATE, .LAYER_CREATE, .LAYER_MODIFY,
      .ADMIN_USERS, .ADMIN_BUDGETS, .ADMIN_AUDIT
    ]
  | .MANAGER => [
      .TWITTER_READ, .TWITTER_WRITE,
      .REDDIT_READ,
      .LINKEDIN_READ, .LINKEDIN_WRITE,
      .MASTODON_READ, .MASTODON_WRITE,
      .LLM_LOCAL, .LLM_API,
      .SEARCH_WEB, .SEARCH_NEWS,
      .CONTENT_CREATE, .CONTENT_APPROVE, .CONTENT_PUBLISH,
      .CAMPAIGN_MANAGE,
      .EXPORT_VIDEO, .AI_GENERATE, .LAYER_CREATE, .LAYER_MODIFY
    ]
  | .CREATOR => [
      .TWITTER_READ,
      .REDDIT_READ,
      .LINKEDIN_READ,
      .MASTODON_READ,
      .LLM_LOCAL, .LLM_API,
      .SEARCH_WEB, .SEARCH_NEWS,
      .CONTENT_CREATE,
      .LAYER_CREATE, .LAYER_MODIFY
    ]
  | .VIEWER => [
      .TWITTER_READ,
      .REDDIT_READ,
      .LINKEDIN_READ,
      .MASTODON_READ
    ]

def Role.hasPermission (r : Role) (p : Permission) : Bool :=
  (Role.defaultPermissions r).contains p

/-! ## Security Theorems -/

/-- THEOREM: Admin has all permissions -/
theorem admin_has_all_permissions (p : Permission) :
    Role.hasPermission .ADMIN p = true := by
  cases p <;> rfl

/-- THEOREM: Viewer cannot write -/
theorem viewer_cannot_write :
    Role.hasPermission .VIEWER .TWITTER_WRITE = false := rfl

end Compass.Permissions
