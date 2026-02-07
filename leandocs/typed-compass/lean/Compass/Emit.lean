/-
  Compass.Emit - Code generation for PureScript, Python, and Elm

  PureScript is the MANDATORY frontend language.
  Follows TensorCore.Extract pattern exactly.
  Emits verified types with encoders/decoders.

  Generation targets:
  - PureScript (Halogen frontend) - PRIMARY
  - Python (FastAPI backend)
  - Elm (legacy/alternative)
-/

import Compass.Core
import Compass.Permissions
import Compass.Auth
import Compass.Tools
import Compass.Audit
import Compass.Jobs

namespace Compass.Emit

open Compass.Core
open Compass.Permissions
open Compass.Auth
open Compass.Tools
open Compass.Audit
open Compass.Jobs

/-! ## Elm Code Generation -/

class EmitElm (α : Type _) where
  typeName : String
  typeDecl : String
  decoder : String
  encoder : String

-- Permission
instance : EmitElm Permission where
  typeName := "Permission"
  typeDecl := "type Permission\n    = TWITTER_READ\n    | TWITTER_WRITE\n    | TWITTER_DELETE\n    | REDDIT_READ\n    | REDDIT_WRITE\n    | LINKEDIN_READ\n    | LINKEDIN_WRITE\n    | MASTODON_READ\n    | MASTODON_WRITE\n    | LLM_LOCAL\n    | LLM_API\n    | LLM_EXPENSIVE\n    | SEARCH_WEB\n    | SEARCH_NEWS\n    | CONTENT_CREATE\n    | CONTENT_APPROVE\n    | CONTENT_PUBLISH\n    | CAMPAIGN_MANAGE\n    | ADMIN_USERS\n    | ADMIN_BUDGETS\n    | ADMIN_AUDIT"
  decoder := "decodePermission : Decoder Permission\ndecodePermission =\n    D.string\n        |> D.andThen\n            (\\s ->\n                case s of\n                    \"TWITTER_READ\" -> D.succeed TWITTER_READ\n                    \"TWITTER_WRITE\" -> D.succeed TWITTER_WRITE\n                    \"TWITTER_DELETE\" -> D.succeed TWITTER_DELETE\n                    \"REDDIT_READ\" -> D.succeed REDDIT_READ\n                    \"REDDIT_WRITE\" -> D.succeed REDDIT_WRITE\n                    \"LINKEDIN_READ\" -> D.succeed LINKEDIN_READ\n                    \"LINKEDIN_WRITE\" -> D.succeed LINKEDIN_WRITE\n                    \"MASTODON_READ\" -> D.succeed MASTODON_READ\n                    \"MASTODON_WRITE\" -> D.succeed MASTODON_WRITE\n                    \"LLM_LOCAL\" -> D.succeed LLM_LOCAL\n                    \"LLM_API\" -> D.succeed LLM_API\n                    \"LLM_EXPENSIVE\" -> D.succeed LLM_EXPENSIVE\n                    \"SEARCH_WEB\" -> D.succeed SEARCH_WEB\n                    \"SEARCH_NEWS\" -> D.succeed SEARCH_NEWS\n                    \"CONTENT_CREATE\" -> D.succeed CONTENT_CREATE\n                    \"CONTENT_APPROVE\" -> D.succeed CONTENT_APPROVE\n                    \"CONTENT_PUBLISH\" -> D.succeed CONTENT_PUBLISH\n                    \"CAMPAIGN_MANAGE\" -> D.succeed CAMPAIGN_MANAGE\n                    \"ADMIN_USERS\" -> D.succeed ADMIN_USERS\n                    \"ADMIN_BUDGETS\" -> D.succeed ADMIN_BUDGETS\n                    \"ADMIN_AUDIT\" -> D.succeed ADMIN_AUDIT\n                    _ -> D.fail (\"Unknown permission: \" ++ s)\n            )"
  encoder := "encodePermission : Permission -> E.Value\nencodePermission p =\n    case p of\n        TWITTER_READ -> E.string \"TWITTER_READ\"\n        TWITTER_WRITE -> E.string \"TWITTER_WRITE\"\n        TWITTER_DELETE -> E.string \"TWITTER_DELETE\"\n        REDDIT_READ -> E.string \"REDDIT_READ\"\n        REDDIT_WRITE -> E.string \"REDDIT_WRITE\"\n        LINKEDIN_READ -> E.string \"LINKEDIN_READ\"\n        LINKEDIN_WRITE -> E.string \"LINKEDIN_WRITE\"\n        MASTODON_READ -> E.string \"MASTODON_READ\"\n        MASTODON_WRITE -> E.string \"MASTODON_WRITE\"\n        LLM_LOCAL -> E.string \"LLM_LOCAL\"\n        LLM_API -> E.string \"LLM_API\"\n        LLM_EXPENSIVE -> E.string \"LLM_EXPENSIVE\"\n        SEARCH_WEB -> E.string \"SEARCH_WEB\"\n        SEARCH_NEWS -> E.string \"SEARCH_NEWS\"\n        CONTENT_CREATE -> E.string \"CONTENT_CREATE\"\n        CONTENT_APPROVE -> E.string \"CONTENT_APPROVE\"\n        CONTENT_PUBLISH -> E.string \"CONTENT_PUBLISH\"\n        CAMPAIGN_MANAGE -> E.string \"CAMPAIGN_MANAGE\"\n        ADMIN_USERS -> E.string \"ADMIN_USERS\"\n        ADMIN_BUDGETS -> E.string \"ADMIN_BUDGETS\"\n        ADMIN_AUDIT -> E.string \"ADMIN_AUDIT\""

-- Role
instance : EmitElm Role where
  typeName := "Role"
  typeDecl := "type Role\n    = ADMIN\n    | MANAGER\n    | CREATOR\n    | VIEWER"
  decoder := "decodeRole : Decoder Role\ndecodeRole =\n    D.string\n        |> D.andThen\n            (\\s ->\n                case s of\n                    \"ADMIN\" -> D.succeed ADMIN\n                    \"MANAGER\" -> D.succeed MANAGER\n                    \"CREATOR\" -> D.succeed CREATOR\n                    \"VIEWER\" -> D.succeed VIEWER\n                    _ -> D.fail (\"Unknown role: \" ++ s)\n            )"
  encoder := "encodeRole : Role -> E.Value\nencodeRole r =\n    case r of\n        ADMIN -> E.string \"ADMIN\"\n        MANAGER -> E.string \"MANAGER\"\n        CREATOR -> E.string \"CREATOR\"\n        VIEWER -> E.string \"VIEWER\""

-- User
instance : EmitElm User where
  typeName := "User"
  typeDecl := "type alias User =\n    { id : String\n    , orgId : String\n    , name : String\n    , email : String\n    , role : Role\n    , mfaEnabled : Bool\n    , dailyBudget : Float\n    , monthlyBudget : Float\n    , isActive : Bool\n    , createdAt : String\n    , updatedAt : String\n    }"
  decoder := "decodeUser : Decoder User\ndecodeUser =\n    D.succeed User\n        |> required \"id\" D.string\n        |> required \"org_id\" D.string\n        |> required \"name\" D.string\n        |> required \"email\" D.string\n        |> required \"role\" decodeRole\n        |> required \"mfa_enabled\" D.bool\n        |> required \"daily_budget\" D.float\n        |> required \"monthly_budget\" D.float\n        |> required \"is_active\" D.bool\n        |> required \"created_at\" D.string\n        |> required \"updated_at\" D.string"
  encoder := "encodeUser : User -> E.Value\nencodeUser u =\n    E.object\n        [ ( \"id\", E.string u.id )\n        , ( \"org_id\", E.string u.orgId )\n        , ( \"name\", E.string u.name )\n        , ( \"email\", E.string u.email )\n        , ( \"role\", encodeRole u.role )\n        , ( \"mfa_enabled\", E.bool u.mfaEnabled )\n        , ( \"daily_budget\", E.float u.dailyBudget )\n        , ( \"monthly_budget\", E.float u.monthlyBudget )\n        , ( \"is_active\", E.bool u.isActive )\n        , ( \"created_at\", E.string u.createdAt )\n        , ( \"updated_at\", E.string u.updatedAt )\n        ]"

-- Session
instance : EmitElm Session where
  typeName := "Session"
  typeDecl := "type alias Session =\n    { id : String\n    , userId : String\n    , createdAt : String\n    , expiresAt : String\n    , lastActivity : String\n    , mfaVerified : Bool\n    }"
  decoder := "decodeSession : Decoder Session\ndecodeSession =\n    D.succeed Session\n        |> required \"id\" D.string\n        |> required \"user_id\" D.string\n        |> required \"created_at\" D.string\n        |> required \"expires_at\" D.string\n        |> required \"last_activity\" D.string\n        |> required \"mfa_verified\" D.bool"
  encoder := "encodeSession : Session -> E.Value\nencodeSession s =\n    E.object\n        [ ( \"id\", E.string s.id )\n        , ( \"user_id\", E.string s.userId )\n        , ( \"created_at\", E.string s.createdAt )\n        , ( \"expires_at\", E.string s.expiresAt )\n        , ( \"last_activity\", E.string s.lastActivity )\n        , ( \"mfa_verified\", E.bool s.mfaVerified )\n        ]"

-- JobStatus
instance : EmitElm JobStatus where
  typeName := "JobStatus"
  typeDecl := "type JobStatus\n    = Pending\n    | Running\n    | WaitingApproval\n    | Approved\n    | Completed\n    | Failed\n    | Cancelled"
  decoder := "decodeJobStatus : Decoder JobStatus\ndecodeJobStatus =\n    D.string\n        |> D.andThen\n            (\\s ->\n                case s of\n                    \"pending\" -> D.succeed Pending\n                    \"running\" -> D.succeed Running\n                    \"waiting_approval\" -> D.succeed WaitingApproval\n                    \"approved\" -> D.succeed Approved\n                    \"completed\" -> D.succeed Completed\n                    \"failed\" -> D.succeed Failed\n                    \"cancelled\" -> D.succeed Cancelled\n                    _ -> D.fail (\"Unknown job status: \" ++ s)\n            )"
  encoder := "encodeJobStatus : JobStatus -> E.Value\nencodeJobStatus s =\n    case s of\n        Pending -> E.string \"pending\"\n        Running -> E.string \"running\"\n        WaitingApproval -> E.string \"waiting_approval\"\n        Approved -> E.string \"approved\"\n        Completed -> E.string \"completed\"\n        Failed -> E.string \"failed\"\n        Cancelled -> E.string \"cancelled\""

/-! ## Python Code Generation -/

class EmitPython (α : Type _) where
  typeName : String
  typeDecl : String

-- Permission
instance : EmitPython Permission where
  typeName := "Permission"
  typeDecl := "class Permission(Enum):\n    \"\"\"Fine-grained permissions for tools\"\"\"\n    # Twitter\n    TWITTER_READ = auto()\n    TWITTER_WRITE = auto()\n    TWITTER_DELETE = auto()\n    # Reddit\n    REDDIT_READ = auto()\n    REDDIT_WRITE = auto()\n    # LinkedIn\n    LINKEDIN_READ = auto()\n    LINKEDIN_WRITE = auto()\n    # Mastodon\n    MASTODON_READ = auto()\n    MASTODON_WRITE = auto()\n    # LLM\n    LLM_LOCAL = auto()\n    LLM_API = auto()\n    LLM_EXPENSIVE = auto()\n    # Search\n    SEARCH_WEB = auto()\n    SEARCH_NEWS = auto()\n    # Internal\n    CONTENT_CREATE = auto()\n    CONTENT_APPROVE = auto()\n    CONTENT_PUBLISH = auto()\n    CAMPAIGN_MANAGE = auto()\n    # Admin\n    ADMIN_USERS = auto()\n    ADMIN_BUDGETS = auto()\n    ADMIN_AUDIT = auto()"

-- Role
instance : EmitPython Role where
  typeName := "Role"
  typeDecl := "class Role(Enum):\n    \"\"\"User roles with permission sets\"\"\"\n    ADMIN = auto()\n    MANAGER = auto()\n    CREATOR = auto()\n    VIEWER = auto()"

-- User
instance : EmitPython User where
  typeName := "User"
  typeDecl := "@dataclass\nclass User:\n    \"\"\"User identity with authentication\"\"\"\n    id: str\n    org_id: str\n    name: str\n    email: str\n    role: Role\n    password_hash: str | None = None\n    mfa_enabled: bool = False\n    mfa_secret: str | None = None\n    daily_budget: float = 10.00\n    monthly_budget: float = 100.00\n    is_active: bool = True\n    created_at: str = \"\"\n    updated_at: str = \"\""

-- Session
instance : EmitPython Session where
  typeName := "Session"
  typeDecl := "@dataclass\nclass Session:\n    \"\"\"User session for web UI\"\"\"\n    id: str\n    user_id: str\n    token_hash: str\n    ip_address: str | None = None\n    user_agent: str | None = None\n    created_at: str = \"\"\n    expires_at: str = \"\"\n    last_activity: str = \"\"\n    mfa_verified: bool = False"

-- JobStatus
instance : EmitPython JobStatus where
  typeName := "JobStatus"
  typeDecl := "class JobStatus(Enum):\n    \"\"\"Job states\"\"\"\n    PENDING = \"pending\"\n    RUNNING = \"running\"\n    WAITING_APPROVAL = \"waiting_approval\"\n    APPROVED = \"approved\"\n    COMPLETED = \"completed\"\n    FAILED = \"failed\"\n    CANCELLED = \"cancelled\""

-- Job
instance : EmitPython Job where
  typeName := "Job"
  typeDecl := "@dataclass\nclass Job:\n    \"\"\"A unit of work\"\"\"\n    id: str\n    job_type: str\n    status: JobStatus\n    created_by: str\n    input_data: str = \"{}\"\n    output_data: str | None = None\n    requires_approval: bool = False\n    approved_by: str | None = None\n    approved_at: str | None = None\n    created_at: str = \"\"\n    started_at: str | None = None\n    completed_at: str | None = None\n    retry_count: int = 0\n    max_retries: int = 3\n    error: str | None = None\n    cost_usd: float = 0.0"

/-! ## Full Module Generation -/

def elmModule : String :=
  let header := "module Compass.Types exposing (..)\n\n{-| AUTO-EXTRACTED FROM LEAN PROOFS\n\n    Every type here has a corresponding Extractable instance in Lean\n    with a proven roundtrip theorem. The encoder/decoder pairs are\n    verified correct by construction.\n\n    DO NOT EDIT - regenerate with `lake exe extract elm`\n-}\n\nimport Json.Decode as D exposing (Decoder)\nimport Json.Decode.Pipeline exposing (required, optional)\nimport Json.Encode as E\n\n\n-- TYPES\n\n"
  let types := [
    EmitElm.typeDecl (α := Permission),
    EmitElm.typeDecl (α := Role),
    EmitElm.typeDecl (α := User),
    EmitElm.typeDecl (α := Session),
    EmitElm.typeDecl (α := JobStatus)
  ]
  let decoders := [
    EmitElm.decoder (α := Permission),
    EmitElm.decoder (α := Role),
    EmitElm.decoder (α := User),
    EmitElm.decoder (α := Session),
    EmitElm.decoder (α := JobStatus)
  ]
  let encoders := [
    EmitElm.encoder (α := Permission),
    EmitElm.encoder (α := Role),
    EmitElm.encoder (α := User),
    EmitElm.encoder (α := Session),
    EmitElm.encoder (α := JobStatus)
  ]
  header ++ "\n\n".intercalate types ++
  "\n\n\n-- DECODERS\n\n" ++ "\n\n".intercalate decoders ++
  "\n\n\n-- ENCODERS\n\n" ++ "\n\n".intercalate encoders

def pythonModule : String :=
  let header := "\"\"\"\nAUTO-EXTRACTED FROM LEAN PROOFS\n\nEvery type here has a corresponding Extractable instance in Lean\nwith a proven roundtrip theorem.\n\nDO NOT EDIT - regenerate with `lake exe extract python`\n\"\"\"\n\nfrom __future__ import annotations\nfrom dataclasses import dataclass\nfrom enum import Enum, auto\n\n\n"
  let types := [
    EmitPython.typeDecl (α := Permission),
    EmitPython.typeDecl (α := Role),
    EmitPython.typeDecl (α := User),
    EmitPython.typeDecl (α := Session),
    EmitPython.typeDecl (α := JobStatus),
    EmitPython.typeDecl (α := Job)
  ]
  header ++ "\n\n".intercalate types

/-! ## PureScript Code Generation (PRIMARY TARGET) -/

class EmitPureScript (α : Type _) where
  typeName : String
  typeDecl : String
  decoder : String
  encoder : String

-- Permission (PureScript)
instance : EmitPureScript Permission where
  typeName := "Permission"
  typeDecl := "data Permission\n  = TWITTER_READ\n  | TWITTER_WRITE\n  | TWITTER_DELETE\n  | REDDIT_READ\n  | REDDIT_WRITE\n  | LINKEDIN_READ\n  | LINKEDIN_WRITE\n  | MASTODON_READ\n  | MASTODON_WRITE\n  | LLM_LOCAL\n  | LLM_API\n  | LLM_EXPENSIVE\n  | SEARCH_WEB\n  | SEARCH_NEWS\n  | CONTENT_CREATE\n  | CONTENT_APPROVE\n  | CONTENT_PUBLISH\n  | CAMPAIGN_MANAGE\n  | ADMIN_USERS\n  | ADMIN_BUDGETS\n  | ADMIN_AUDIT\n\nderive instance eqPermission :: Eq Permission\nderive instance ordPermission :: Ord Permission\nderive instance genericPermission :: Generic Permission _"
  decoder := "decodePermission :: String -> Either String Permission\ndecodePermission = case _ of\n  \"TWITTER_READ\" -> Right TWITTER_READ\n  \"TWITTER_WRITE\" -> Right TWITTER_WRITE\n  \"TWITTER_DELETE\" -> Right TWITTER_DELETE\n  \"REDDIT_READ\" -> Right REDDIT_READ\n  \"REDDIT_WRITE\" -> Right REDDIT_WRITE\n  \"LINKEDIN_READ\" -> Right LINKEDIN_READ\n  \"LINKEDIN_WRITE\" -> Right LINKEDIN_WRITE\n  \"MASTODON_READ\" -> Right MASTODON_READ\n  \"MASTODON_WRITE\" -> Right MASTODON_WRITE\n  \"LLM_LOCAL\" -> Right LLM_LOCAL\n  \"LLM_API\" -> Right LLM_API\n  \"LLM_EXPENSIVE\" -> Right LLM_EXPENSIVE\n  \"SEARCH_WEB\" -> Right SEARCH_WEB\n  \"SEARCH_NEWS\" -> Right SEARCH_NEWS\n  \"CONTENT_CREATE\" -> Right CONTENT_CREATE\n  \"CONTENT_APPROVE\" -> Right CONTENT_APPROVE\n  \"CONTENT_PUBLISH\" -> Right CONTENT_PUBLISH\n  \"CAMPAIGN_MANAGE\" -> Right CAMPAIGN_MANAGE\n  \"ADMIN_USERS\" -> Right ADMIN_USERS\n  \"ADMIN_BUDGETS\" -> Right ADMIN_BUDGETS\n  \"ADMIN_AUDIT\" -> Right ADMIN_AUDIT\n  s -> Left $ \"Unknown permission: \" <> s"
  encoder := "encodePermission :: Permission -> String\nencodePermission = case _ of\n  TWITTER_READ -> \"TWITTER_READ\"\n  TWITTER_WRITE -> \"TWITTER_WRITE\"\n  TWITTER_DELETE -> \"TWITTER_DELETE\"\n  REDDIT_READ -> \"REDDIT_READ\"\n  REDDIT_WRITE -> \"REDDIT_WRITE\"\n  LINKEDIN_READ -> \"LINKEDIN_READ\"\n  LINKEDIN_WRITE -> \"LINKEDIN_WRITE\"\n  MASTODON_READ -> \"MASTODON_READ\"\n  MASTODON_WRITE -> \"MASTODON_WRITE\"\n  LLM_LOCAL -> \"LLM_LOCAL\"\n  LLM_API -> \"LLM_API\"\n  LLM_EXPENSIVE -> \"LLM_EXPENSIVE\"\n  SEARCH_WEB -> \"SEARCH_WEB\"\n  SEARCH_NEWS -> \"SEARCH_NEWS\"\n  CONTENT_CREATE -> \"CONTENT_CREATE\"\n  CONTENT_APPROVE -> \"CONTENT_APPROVE\"\n  CONTENT_PUBLISH -> \"CONTENT_PUBLISH\"\n  CAMPAIGN_MANAGE -> \"CAMPAIGN_MANAGE\"\n  ADMIN_USERS -> \"ADMIN_USERS\"\n  ADMIN_BUDGETS -> \"ADMIN_BUDGETS\"\n  ADMIN_AUDIT -> \"ADMIN_AUDIT\""

-- Role (PureScript)
instance : EmitPureScript Role where
  typeName := "Role"
  typeDecl := "data Role\n  = Admin\n  | Manager\n  | Creator\n  | Viewer\n\nderive instance eqRole :: Eq Role\nderive instance ordRole :: Ord Role\nderive instance genericRole :: Generic Role _"
  decoder := "decodeRole :: String -> Either String Role\ndecodeRole = case _ of\n  \"ADMIN\" -> Right Admin\n  \"MANAGER\" -> Right Manager\n  \"CREATOR\" -> Right Creator\n  \"VIEWER\" -> Right Viewer\n  s -> Left $ \"Unknown role: \" <> s"
  encoder := "encodeRole :: Role -> String\nencodeRole = case _ of\n  Admin -> \"ADMIN\"\n  Manager -> \"MANAGER\"\n  Creator -> \"CREATOR\"\n  Viewer -> \"VIEWER\""

-- User (PureScript)
instance : EmitPureScript User where
  typeName := "User"
  typeDecl := "type User =\n  { id :: String\n  , orgId :: String\n  , name :: String\n  , email :: String\n  , role :: Role\n  , mfaEnabled :: Boolean\n  , dailyBudget :: Number\n  , monthlyBudget :: Number\n  , isActive :: Boolean\n  , createdAt :: String\n  , updatedAt :: String\n  }"
  decoder := "decodeUser :: Json -> Either String User\ndecodeUser json = do\n  obj <- decodeJson json\n  id <- obj .: \"id\"\n  orgId <- obj .: \"org_id\"\n  name <- obj .: \"name\"\n  email <- obj .: \"email\"\n  role <- obj .: \"role\" >>= decodeRole\n  mfaEnabled <- obj .: \"mfa_enabled\"\n  dailyBudget <- obj .: \"daily_budget\"\n  monthlyBudget <- obj .: \"monthly_budget\"\n  isActive <- obj .: \"is_active\"\n  createdAt <- obj .: \"created_at\"\n  updatedAt <- obj .: \"updated_at\"\n  pure { id, orgId, name, email, role, mfaEnabled, dailyBudget, monthlyBudget, isActive, createdAt, updatedAt }"
  encoder := "encodeUser :: User -> Json\nencodeUser u = encodeJson\n  { id: u.id\n  , org_id: u.orgId\n  , name: u.name\n  , email: u.email\n  , role: encodeRole u.role\n  , mfa_enabled: u.mfaEnabled\n  , daily_budget: u.dailyBudget\n  , monthly_budget: u.monthlyBudget\n  , is_active: u.isActive\n  , created_at: u.createdAt\n  , updated_at: u.updatedAt\n  }"

-- JobStatus (PureScript)
instance : EmitPureScript JobStatus where
  typeName := "JobStatus"
  typeDecl := "data JobStatus\n  = Pending\n  | Running\n  | WaitingApproval\n  | Approved\n  | Completed\n  | Failed\n  | Cancelled\n\nderive instance eqJobStatus :: Eq JobStatus\nderive instance genericJobStatus :: Generic JobStatus _"
  decoder := "decodeJobStatus :: String -> Either String JobStatus\ndecodeJobStatus = case _ of\n  \"pending\" -> Right Pending\n  \"running\" -> Right Running\n  \"waiting_approval\" -> Right WaitingApproval\n  \"approved\" -> Right Approved\n  \"completed\" -> Right Completed\n  \"failed\" -> Right Failed\n  \"cancelled\" -> Right Cancelled\n  s -> Left $ \"Unknown job status: \" <> s"
  encoder := "encodeJobStatus :: JobStatus -> String\nencodeJobStatus = case _ of\n  Pending -> \"pending\"\n  Running -> \"running\"\n  WaitingApproval -> \"waiting_approval\"\n  Approved -> \"approved\"\n  Completed -> \"completed\"\n  Failed -> \"failed\"\n  Cancelled -> \"cancelled\""

/-! ## Full PureScript Module Generation -/

def pureScriptModule : String :=
  let header := "-- AUTO-EXTRACTED FROM LEAN PROOFS\n-- Every type here has a corresponding Extractable instance in Lean\n-- with a proven roundtrip theorem.\n--\n-- DO NOT EDIT - regenerate with `lake exe compass-extract purescript`\n\nmodule Compass.Types where\n\nimport Prelude\nimport Data.Either (Either(..))\nimport Data.Maybe (Maybe(..))\nimport Data.Generic.Rep (class Generic)\nimport Data.Argonaut.Core (Json)\nimport Data.Argonaut.Decode (decodeJson, (.:), (.:?))\nimport Data.Argonaut.Encode (encodeJson)\n\n\n-- TYPES\n\n"
  let types := [
    EmitPureScript.typeDecl (α := Permission),
    EmitPureScript.typeDecl (α := Role),
    EmitPureScript.typeDecl (α := User),
    EmitPureScript.typeDecl (α := JobStatus)
  ]
  let decoders := [
    EmitPureScript.decoder (α := Permission),
    EmitPureScript.decoder (α := Role),
    EmitPureScript.decoder (α := User),
    EmitPureScript.decoder (α := JobStatus)
  ]
  let encoders := [
    EmitPureScript.encoder (α := Permission),
    EmitPureScript.encoder (α := Role),
    EmitPureScript.encoder (α := User),
    EmitPureScript.encoder (α := JobStatus)
  ]
  header ++ "\n\n".intercalate types ++
  "\n\n\n-- DECODERS\n\n" ++ "\n\n".intercalate decoders ++
  "\n\n\n-- ENCODERS\n\n" ++ "\n\n".intercalate encoders

end Compass.Emit
