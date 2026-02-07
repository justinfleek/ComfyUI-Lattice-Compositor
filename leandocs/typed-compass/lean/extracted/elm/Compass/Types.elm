module Compass.Types exposing (..)

{-| AUTO-EXTRACTED FROM LEAN PROOFS

    Every type here has a corresponding Extractable instance in Lean
    with a proven roundtrip theorem. The encoder/decoder pairs are
    verified correct by construction.

    DO NOT EDIT - regenerate with `lake exe extract elm`
-}

import Json.Decode as D exposing (Decoder)
import Json.Decode.Pipeline exposing (required, optional)
import Json.Encode as E


-- TYPES

type Permission
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

type Role
    = ADMIN
    | MANAGER
    | CREATOR
    | VIEWER

type alias User =
    { id : String
    , orgId : String
    , name : String
    , email : String
    , role : Role
    , mfaEnabled : Bool
    , dailyBudget : Float
    , monthlyBudget : Float
    , isActive : Bool
    , createdAt : String
    , updatedAt : String
    }

type alias Session =
    { id : String
    , userId : String
    , createdAt : String
    , expiresAt : String
    , lastActivity : String
    , mfaVerified : Bool
    }

type JobStatus
    = Pending
    | Running
    | WaitingApproval
    | Approved
    | Completed
    | Failed
    | Cancelled


-- DECODERS

decodePermission : Decoder Permission
decodePermission =
    D.string
        |> D.andThen
            (\s ->
                case s of
                    "TWITTER_READ" -> D.succeed TWITTER_READ
                    "TWITTER_WRITE" -> D.succeed TWITTER_WRITE
                    "TWITTER_DELETE" -> D.succeed TWITTER_DELETE
                    "REDDIT_READ" -> D.succeed REDDIT_READ
                    "REDDIT_WRITE" -> D.succeed REDDIT_WRITE
                    "LINKEDIN_READ" -> D.succeed LINKEDIN_READ
                    "LINKEDIN_WRITE" -> D.succeed LINKEDIN_WRITE
                    "MASTODON_READ" -> D.succeed MASTODON_READ
                    "MASTODON_WRITE" -> D.succeed MASTODON_WRITE
                    "LLM_LOCAL" -> D.succeed LLM_LOCAL
                    "LLM_API" -> D.succeed LLM_API
                    "LLM_EXPENSIVE" -> D.succeed LLM_EXPENSIVE
                    "SEARCH_WEB" -> D.succeed SEARCH_WEB
                    "SEARCH_NEWS" -> D.succeed SEARCH_NEWS
                    "CONTENT_CREATE" -> D.succeed CONTENT_CREATE
                    "CONTENT_APPROVE" -> D.succeed CONTENT_APPROVE
                    "CONTENT_PUBLISH" -> D.succeed CONTENT_PUBLISH
                    "CAMPAIGN_MANAGE" -> D.succeed CAMPAIGN_MANAGE
                    "ADMIN_USERS" -> D.succeed ADMIN_USERS
                    "ADMIN_BUDGETS" -> D.succeed ADMIN_BUDGETS
                    "ADMIN_AUDIT" -> D.succeed ADMIN_AUDIT
                    _ -> D.fail ("Unknown permission: " ++ s)
            )

decodeRole : Decoder Role
decodeRole =
    D.string
        |> D.andThen
            (\s ->
                case s of
                    "ADMIN" -> D.succeed ADMIN
                    "MANAGER" -> D.succeed MANAGER
                    "CREATOR" -> D.succeed CREATOR
                    "VIEWER" -> D.succeed VIEWER
                    _ -> D.fail ("Unknown role: " ++ s)
            )

decodeUser : Decoder User
decodeUser =
    D.succeed User
        |> required "id" D.string
        |> required "org_id" D.string
        |> required "name" D.string
        |> required "email" D.string
        |> required "role" decodeRole
        |> required "mfa_enabled" D.bool
        |> required "daily_budget" D.float
        |> required "monthly_budget" D.float
        |> required "is_active" D.bool
        |> required "created_at" D.string
        |> required "updated_at" D.string

decodeSession : Decoder Session
decodeSession =
    D.succeed Session
        |> required "id" D.string
        |> required "user_id" D.string
        |> required "created_at" D.string
        |> required "expires_at" D.string
        |> required "last_activity" D.string
        |> required "mfa_verified" D.bool

decodeJobStatus : Decoder JobStatus
decodeJobStatus =
    D.string
        |> D.andThen
            (\s ->
                case s of
                    "pending" -> D.succeed Pending
                    "running" -> D.succeed Running
                    "waiting_approval" -> D.succeed WaitingApproval
                    "approved" -> D.succeed Approved
                    "completed" -> D.succeed Completed
                    "failed" -> D.succeed Failed
                    "cancelled" -> D.succeed Cancelled
                    _ -> D.fail ("Unknown job status: " ++ s)
            )


-- ENCODERS

encodePermission : Permission -> E.Value
encodePermission p =
    case p of
        TWITTER_READ -> E.string "TWITTER_READ"
        TWITTER_WRITE -> E.string "TWITTER_WRITE"
        TWITTER_DELETE -> E.string "TWITTER_DELETE"
        REDDIT_READ -> E.string "REDDIT_READ"
        REDDIT_WRITE -> E.string "REDDIT_WRITE"
        LINKEDIN_READ -> E.string "LINKEDIN_READ"
        LINKEDIN_WRITE -> E.string "LINKEDIN_WRITE"
        MASTODON_READ -> E.string "MASTODON_READ"
        MASTODON_WRITE -> E.string "MASTODON_WRITE"
        LLM_LOCAL -> E.string "LLM_LOCAL"
        LLM_API -> E.string "LLM_API"
        LLM_EXPENSIVE -> E.string "LLM_EXPENSIVE"
        SEARCH_WEB -> E.string "SEARCH_WEB"
        SEARCH_NEWS -> E.string "SEARCH_NEWS"
        CONTENT_CREATE -> E.string "CONTENT_CREATE"
        CONTENT_APPROVE -> E.string "CONTENT_APPROVE"
        CONTENT_PUBLISH -> E.string "CONTENT_PUBLISH"
        CAMPAIGN_MANAGE -> E.string "CAMPAIGN_MANAGE"
        ADMIN_USERS -> E.string "ADMIN_USERS"
        ADMIN_BUDGETS -> E.string "ADMIN_BUDGETS"
        ADMIN_AUDIT -> E.string "ADMIN_AUDIT"

encodeRole : Role -> E.Value
encodeRole r =
    case r of
        ADMIN -> E.string "ADMIN"
        MANAGER -> E.string "MANAGER"
        CREATOR -> E.string "CREATOR"
        VIEWER -> E.string "VIEWER"

encodeUser : User -> E.Value
encodeUser u =
    E.object
        [ ( "id", E.string u.id )
        , ( "org_id", E.string u.orgId )
        , ( "name", E.string u.name )
        , ( "email", E.string u.email )
        , ( "role", encodeRole u.role )
        , ( "mfa_enabled", E.bool u.mfaEnabled )
        , ( "daily_budget", E.float u.dailyBudget )
        , ( "monthly_budget", E.float u.monthlyBudget )
        , ( "is_active", E.bool u.isActive )
        , ( "created_at", E.string u.createdAt )
        , ( "updated_at", E.string u.updatedAt )
        ]

encodeSession : Session -> E.Value
encodeSession s =
    E.object
        [ ( "id", E.string s.id )
        , ( "user_id", E.string s.userId )
        , ( "created_at", E.string s.createdAt )
        , ( "expires_at", E.string s.expiresAt )
        , ( "last_activity", E.string s.lastActivity )
        , ( "mfa_verified", E.bool s.mfaVerified )
        ]

encodeJobStatus : JobStatus -> E.Value
encodeJobStatus s =
    case s of
        Pending -> E.string "pending"
        Running -> E.string "running"
        WaitingApproval -> E.string "waiting_approval"
        Approved -> E.string "approved"
        Completed -> E.string "completed"
        Failed -> E.string "failed"
        Cancelled -> E.string "cancelled"