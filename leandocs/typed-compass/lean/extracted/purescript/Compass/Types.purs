-- AUTO-EXTRACTED FROM LEAN PROOFS
-- Every type here has a corresponding Extractable instance in Lean
-- with a proven roundtrip theorem.
--
-- DO NOT EDIT - regenerate with `lake exe compass-extract purescript`

module Compass.Types where

import Prelude
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (decodeJson, (.:), (.:?))
import Data.Argonaut.Encode (encodeJson)


-- TYPES

data Permission
  = TWITTER_READ
  | TWITTER_WRITE
  | TWITTER_DELETE
  | REDDIT_READ
  | REDDIT_WRITE
  | LINKEDIN_READ
  | LINKEDIN_WRITE
  | MASTODON_READ
  | MASTODON_WRITE
  | LLM_LOCAL
  | LLM_API
  | LLM_EXPENSIVE
  | SEARCH_WEB
  | SEARCH_NEWS
  | CONTENT_CREATE
  | CONTENT_APPROVE
  | CONTENT_PUBLISH
  | CAMPAIGN_MANAGE
  | ADMIN_USERS
  | ADMIN_BUDGETS
  | ADMIN_AUDIT

derive instance eqPermission :: Eq Permission
derive instance ordPermission :: Ord Permission
derive instance genericPermission :: Generic Permission _

data Role
  = Admin
  | Manager
  | Creator
  | Viewer

derive instance eqRole :: Eq Role
derive instance ordRole :: Ord Role
derive instance genericRole :: Generic Role _

type User =
  { id :: String
  , orgId :: String
  , name :: String
  , email :: String
  , role :: Role
  , mfaEnabled :: Boolean
  , dailyBudget :: Number
  , monthlyBudget :: Number
  , isActive :: Boolean
  , createdAt :: String
  , updatedAt :: String
  }

data JobStatus
  = Pending
  | Running
  | WaitingApproval
  | Approved
  | Completed
  | Failed
  | Cancelled

derive instance eqJobStatus :: Eq JobStatus
derive instance genericJobStatus :: Generic JobStatus _


-- DECODERS

decodePermission :: String -> Either String Permission
decodePermission = case _ of
  "TWITTER_READ" -> Right TWITTER_READ
  "TWITTER_WRITE" -> Right TWITTER_WRITE
  "TWITTER_DELETE" -> Right TWITTER_DELETE
  "REDDIT_READ" -> Right REDDIT_READ
  "REDDIT_WRITE" -> Right REDDIT_WRITE
  "LINKEDIN_READ" -> Right LINKEDIN_READ
  "LINKEDIN_WRITE" -> Right LINKEDIN_WRITE
  "MASTODON_READ" -> Right MASTODON_READ
  "MASTODON_WRITE" -> Right MASTODON_WRITE
  "LLM_LOCAL" -> Right LLM_LOCAL
  "LLM_API" -> Right LLM_API
  "LLM_EXPENSIVE" -> Right LLM_EXPENSIVE
  "SEARCH_WEB" -> Right SEARCH_WEB
  "SEARCH_NEWS" -> Right SEARCH_NEWS
  "CONTENT_CREATE" -> Right CONTENT_CREATE
  "CONTENT_APPROVE" -> Right CONTENT_APPROVE
  "CONTENT_PUBLISH" -> Right CONTENT_PUBLISH
  "CAMPAIGN_MANAGE" -> Right CAMPAIGN_MANAGE
  "ADMIN_USERS" -> Right ADMIN_USERS
  "ADMIN_BUDGETS" -> Right ADMIN_BUDGETS
  "ADMIN_AUDIT" -> Right ADMIN_AUDIT
  s -> Left $ "Unknown permission: " <> s

decodeRole :: String -> Either String Role
decodeRole = case _ of
  "ADMIN" -> Right Admin
  "MANAGER" -> Right Manager
  "CREATOR" -> Right Creator
  "VIEWER" -> Right Viewer
  s -> Left $ "Unknown role: " <> s

decodeUser :: Json -> Either String User
decodeUser json = do
  obj <- decodeJson json
  id <- obj .: "id"
  orgId <- obj .: "org_id"
  name <- obj .: "name"
  email <- obj .: "email"
  role <- obj .: "role" >>= decodeRole
  mfaEnabled <- obj .: "mfa_enabled"
  dailyBudget <- obj .: "daily_budget"
  monthlyBudget <- obj .: "monthly_budget"
  isActive <- obj .: "is_active"
  createdAt <- obj .: "created_at"
  updatedAt <- obj .: "updated_at"
  pure { id, orgId, name, email, role, mfaEnabled, dailyBudget, monthlyBudget, isActive, createdAt, updatedAt }

decodeJobStatus :: String -> Either String JobStatus
decodeJobStatus = case _ of
  "pending" -> Right Pending
  "running" -> Right Running
  "waiting_approval" -> Right WaitingApproval
  "approved" -> Right Approved
  "completed" -> Right Completed
  "failed" -> Right Failed
  "cancelled" -> Right Cancelled
  s -> Left $ "Unknown job status: " <> s


-- ENCODERS

encodePermission :: Permission -> String
encodePermission = case _ of
  TWITTER_READ -> "TWITTER_READ"
  TWITTER_WRITE -> "TWITTER_WRITE"
  TWITTER_DELETE -> "TWITTER_DELETE"
  REDDIT_READ -> "REDDIT_READ"
  REDDIT_WRITE -> "REDDIT_WRITE"
  LINKEDIN_READ -> "LINKEDIN_READ"
  LINKEDIN_WRITE -> "LINKEDIN_WRITE"
  MASTODON_READ -> "MASTODON_READ"
  MASTODON_WRITE -> "MASTODON_WRITE"
  LLM_LOCAL -> "LLM_LOCAL"
  LLM_API -> "LLM_API"
  LLM_EXPENSIVE -> "LLM_EXPENSIVE"
  SEARCH_WEB -> "SEARCH_WEB"
  SEARCH_NEWS -> "SEARCH_NEWS"
  CONTENT_CREATE -> "CONTENT_CREATE"
  CONTENT_APPROVE -> "CONTENT_APPROVE"
  CONTENT_PUBLISH -> "CONTENT_PUBLISH"
  CAMPAIGN_MANAGE -> "CAMPAIGN_MANAGE"
  ADMIN_USERS -> "ADMIN_USERS"
  ADMIN_BUDGETS -> "ADMIN_BUDGETS"
  ADMIN_AUDIT -> "ADMIN_AUDIT"

encodeRole :: Role -> String
encodeRole = case _ of
  Admin -> "ADMIN"
  Manager -> "MANAGER"
  Creator -> "CREATOR"
  Viewer -> "VIEWER"

encodeUser :: User -> Json
encodeUser u = encodeJson
  { id: u.id
  , org_id: u.orgId
  , name: u.name
  , email: u.email
  , role: encodeRole u.role
  , mfa_enabled: u.mfaEnabled
  , daily_budget: u.dailyBudget
  , monthly_budget: u.monthlyBudget
  , is_active: u.isActive
  , created_at: u.createdAt
  , updated_at: u.updatedAt
  }

encodeJobStatus :: JobStatus -> String
encodeJobStatus = case _ of
  Pending -> "pending"
  Running -> "running"
  WaitingApproval -> "waiting_approval"
  Approved -> "approved"
  Completed -> "completed"
  Failed -> "failed"
  Cancelled -> "cancelled"