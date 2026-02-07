// Lean compiler output
// Module: Compass.Emit
// Imports: public import Init public import Compass.Core public import Compass.Permissions public import Compass.Auth public import Compass.Tools public import Compass.Audit public import Compass.Jobs
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static lean_object* l_Compass_Emit_pureScriptModule___closed__11;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitPythonPermission;
static lean_object* l_Compass_Emit_instEmitPythonJob___closed__1;
static lean_object* l_Compass_Emit_instEmitElmUser___closed__0;
static lean_object* l_Compass_Emit_elmModule___closed__3;
static lean_object* l_Compass_Emit_elmModule___closed__16;
static lean_object* l_Compass_Emit_elmModule___closed__18;
static lean_object* l_Compass_Emit_elmModule___closed__8;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitPureScriptUser;
static lean_object* l_Compass_Emit_pythonModule___closed__1;
static lean_object* l_Compass_Emit_elmModule___closed__20;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitPureScriptPermission;
static lean_object* l_Compass_Emit_elmModule___closed__2;
static lean_object* l_Compass_Emit_elmModule___closed__19;
static lean_object* l_Compass_Emit_instEmitPureScriptJobStatus___closed__3;
static lean_object* l_Compass_Emit_elmModule___closed__6;
static lean_object* l_Compass_Emit_instEmitElmRole___closed__4;
static lean_object* l_Compass_Emit_pureScriptModule___closed__5;
static lean_object* l_Compass_Emit_instEmitPythonRole___closed__1;
static lean_object* l_Compass_Emit_instEmitElmSession___closed__4;
static lean_object* l_Compass_Emit_pureScriptModule___closed__1;
static lean_object* l_Compass_Emit_instEmitElmRole___closed__1;
static lean_object* l_Compass_Emit_elmModule___closed__12;
static lean_object* l_Compass_Emit_pureScriptModule___closed__13;
static lean_object* l_Compass_Emit_instEmitPureScriptJobStatus___closed__2;
static lean_object* l_Compass_Emit_elmModule___closed__0;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitPythonJob;
static lean_object* l_Compass_Emit_pythonModule___closed__7;
static lean_object* l_Compass_Emit_instEmitElmPermission___closed__0;
static lean_object* l_Compass_Emit_instEmitElmJobStatus___closed__4;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitElmRole;
static lean_object* l_Compass_Emit_elmModule___closed__4;
static lean_object* l_Compass_Emit_instEmitPythonUser___closed__0;
static lean_object* l_Compass_Emit_pythonModule___closed__2;
static lean_object* l_Compass_Emit_instEmitPythonJobStatus___closed__1;
static lean_object* l_Compass_Emit_pythonModule___closed__5;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitPythonJobStatus;
static lean_object* l_Compass_Emit_instEmitPureScriptUser___closed__3;
static lean_object* l_Compass_Emit_instEmitElmJobStatus___closed__3;
LEAN_EXPORT lean_object* l_Compass_Emit_EmitPureScript_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitPureScriptRole;
static lean_object* l_Compass_Emit_instEmitElmRole___closed__0;
static lean_object* l_Compass_Emit_instEmitPythonJob___closed__2;
static lean_object* l_Compass_Emit_pythonModule___closed__0;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitPythonUser;
static lean_object* l_Compass_Emit_instEmitPythonJob___closed__0;
static lean_object* l_Compass_Emit_instEmitElmJobStatus___closed__1;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitPythonRole;
static lean_object* l_Compass_Emit_elmModule___closed__21;
static lean_object* l_Compass_Emit_elmModule___closed__10;
static lean_object* l_Compass_Emit_pureScriptModule___closed__10;
static lean_object* l_Compass_Emit_pureScriptModule___closed__12;
static lean_object* l_Compass_Emit_instEmitPureScriptUser___closed__0;
static lean_object* l_Compass_Emit_pureScriptModule___closed__19;
static lean_object* l_Compass_Emit_instEmitPureScriptJobStatus___closed__0;
LEAN_EXPORT lean_object* l_Compass_Emit_pureScriptModule;
LEAN_EXPORT lean_object* l_Compass_Emit_EmitPureScript_ctorIdx(lean_object*, lean_object*);
static lean_object* l_Compass_Emit_instEmitPythonPermission___closed__1;
static lean_object* l_Compass_Emit_elmModule___closed__13;
static lean_object* l_Compass_Emit_instEmitElmPermission___closed__4;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitPureScriptJobStatus;
static lean_object* l_Compass_Emit_instEmitPureScriptJobStatus___closed__1;
static lean_object* l_Compass_Emit_instEmitPureScriptRole___closed__1;
static lean_object* l_Compass_Emit_instEmitElmSession___closed__3;
static lean_object* l_Compass_Emit_instEmitPythonPermission___closed__0;
static lean_object* l_Compass_Emit_pureScriptModule___closed__17;
static lean_object* l_Compass_Emit_pureScriptModule___closed__3;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitPythonSession;
static lean_object* l_Compass_Emit_instEmitPureScriptRole___closed__2;
static lean_object* l_Compass_Emit_instEmitElmPermission___closed__3;
static lean_object* l_Compass_Emit_pureScriptModule___closed__18;
static lean_object* l_Compass_Emit_instEmitElmUser___closed__1;
static lean_object* l_Compass_Emit_elmModule___closed__14;
static lean_object* l_Compass_Emit_elmModule___closed__24;
static lean_object* l_Compass_Emit_pureScriptModule___closed__14;
static lean_object* l_Compass_Emit_elmModule___closed__25;
LEAN_EXPORT lean_object* l_Compass_Emit_EmitPython_ctorIdx(lean_object*, lean_object*);
static lean_object* l_Compass_Emit_pureScriptModule___closed__16;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitElmUser;
static lean_object* l_Compass_Emit_instEmitPureScriptRole___closed__3;
static lean_object* l_Compass_Emit_elmModule___closed__15;
static lean_object* l_Compass_Emit_instEmitPureScriptPermission___closed__0;
static lean_object* l_Compass_Emit_elmModule___closed__11;
LEAN_EXPORT lean_object* l_Compass_Emit_EmitPython_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitElmJobStatus;
static lean_object* l_Compass_Emit_elmModule___closed__5;
static lean_object* l_Compass_Emit_elmModule___closed__17;
static lean_object* l_Compass_Emit_pureScriptModule___closed__20;
LEAN_EXPORT lean_object* l_Compass_Emit_EmitElm_ctorIdx(lean_object*, lean_object*);
static lean_object* l_Compass_Emit_instEmitElmUser___closed__3;
static lean_object* l_Compass_Emit_pureScriptModule___closed__15;
static lean_object* l_Compass_Emit_instEmitElmRole___closed__2;
static lean_object* l_Compass_Emit_instEmitElmSession___closed__2;
LEAN_EXPORT lean_object* l_Compass_Emit_elmModule;
static lean_object* l_Compass_Emit_pythonModule___closed__8;
static lean_object* l_Compass_Emit_instEmitPureScriptUser___closed__1;
static lean_object* l_Compass_Emit_instEmitPureScriptRole___closed__0;
static lean_object* l_Compass_Emit_elmModule___closed__26;
static lean_object* l_Compass_Emit_pureScriptModule___closed__7;
static lean_object* l_Compass_Emit_instEmitElmUser___closed__4;
static lean_object* l_Compass_Emit_instEmitPythonSession___closed__0;
static lean_object* l_Compass_Emit_instEmitElmUser___closed__2;
static lean_object* l_Compass_Emit_instEmitPythonUser___closed__1;
static lean_object* l_Compass_Emit_pythonModule___closed__3;
static lean_object* l_Compass_Emit_instEmitPureScriptPermission___closed__3;
static lean_object* l_Compass_Emit_elmModule___closed__1;
static lean_object* l_Compass_Emit_elmModule___closed__9;
LEAN_EXPORT lean_object* l_Compass_Emit_pythonModule;
static lean_object* l_Compass_Emit_pureScriptModule___closed__2;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitElmSession;
static lean_object* l_Compass_Emit_instEmitPureScriptPermission___closed__2;
LEAN_EXPORT lean_object* l_Compass_Emit_EmitElm_ctorIdx___boxed(lean_object*, lean_object*);
static lean_object* l_Compass_Emit_pythonModule___closed__4;
static lean_object* l_Compass_Emit_instEmitElmPermission___closed__2;
lean_object* l_String_intercalate(lean_object*, lean_object*);
static lean_object* l_Compass_Emit_instEmitPureScriptUser___closed__2;
static lean_object* l_Compass_Emit_elmModule___closed__22;
static lean_object* l_Compass_Emit_elmModule___closed__7;
static lean_object* l_Compass_Emit_instEmitPythonRole___closed__0;
static lean_object* l_Compass_Emit_pureScriptModule___closed__0;
static lean_object* l_Compass_Emit_instEmitPureScriptPermission___closed__1;
LEAN_EXPORT lean_object* l_Compass_Emit_instEmitElmPermission;
static lean_object* l_Compass_Emit_pureScriptModule___closed__4;
static lean_object* l_Compass_Emit_pureScriptModule___closed__9;
static lean_object* l_Compass_Emit_instEmitElmSession___closed__0;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Compass_Emit_pureScriptModule___closed__8;
static lean_object* l_Compass_Emit_instEmitElmPermission___closed__1;
static lean_object* l_Compass_Emit_pythonModule___closed__6;
static lean_object* l_Compass_Emit_instEmitElmSession___closed__1;
static lean_object* l_Compass_Emit_instEmitPythonJobStatus___closed__0;
static lean_object* l_Compass_Emit_instEmitElmJobStatus___closed__2;
static lean_object* l_Compass_Emit_instEmitPythonSession___closed__1;
static lean_object* l_Compass_Emit_pureScriptModule___closed__6;
static lean_object* l_Compass_Emit_elmModule___closed__23;
static lean_object* l_Compass_Emit_instEmitElmJobStatus___closed__0;
static lean_object* l_Compass_Emit_instEmitElmRole___closed__3;
LEAN_EXPORT lean_object* l_Compass_Emit_EmitElm_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_Emit_EmitElm_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_Emit_EmitElm_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmPermission___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Permission", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmPermission___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type Permission\n    = TWITTER_READ\n    | TWITTER_WRITE\n    | TWITTER_DELETE\n    | REDDIT_READ\n    | REDDIT_WRITE\n    | LINKEDIN_READ\n    | LINKEDIN_WRITE\n    | MASTODON_READ\n    | MASTODON_WRITE\n    | LLM_LOCAL\n    | LLM_API\n    | LLM_EXPENSIVE\n    | SEARCH_WEB\n    | SEARCH_NEWS\n    | CONTENT_CREATE\n    | CONTENT_APPROVE\n    | CONTENT_PUBLISH\n    | CAMPAIGN_MANAGE\n    | ADMIN_USERS\n    | ADMIN_BUDGETS\n    | ADMIN_AUDIT", 422, 422);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmPermission___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decodePermission : Decoder Permission\ndecodePermission =\n    D.string\n        |> D.andThen\n            (\\s ->\n                case s of\n                    \"TWITTER_READ\" -> D.succeed TWITTER_READ\n                    \"TWITTER_WRITE\" -> D.succeed TWITTER_WRITE\n                    \"TWITTER_DELETE\" -> D.succeed TWITTER_DELETE\n                    \"REDDIT_READ\" -> D.succeed REDDIT_READ\n                    \"REDDIT_WRITE\" -> D.succeed REDDIT_WRITE\n                    \"LINKEDIN_READ\" -> D.succeed LINKEDIN_READ\n                    \"LINKEDIN_WRITE\" -> D.succeed LINKEDIN_WRITE\n                    \"MASTODON_READ\" -> D.succeed MASTODON_READ\n                    \"MASTODON_WRITE\" -> D.succeed MASTODON_WRITE\n                    \"LLM_LOCAL\" -> D.succeed LLM_LOCAL\n                    \"LLM_API\" -> D.succeed LLM_API\n                    \"LLM_EXPENSIVE\" -> D.succeed LLM_EXPENSIVE\n                    \"SEARCH_WEB\" -> D.succeed SEARCH_WEB\n                    \"SEARCH_NEWS\" -> D.succeed SEARCH_NEWS\n                    \"CONTENT_CREATE\" -> D.succeed CONTENT_CREATE\n                    \"CONTENT_APPROVE\" -> D.succeed CONTENT_APPROVE\n                    \"CONTENT_PUBLISH\" -> D.succeed CONTENT_PUBLISH\n                    \"CAMPAIGN_MANAGE\" -> D.succeed CAMPAIGN_MANAGE\n                    \"ADMIN_USERS\" -> D.succeed ADMIN_USERS\n                    \"ADMIN_BUDGETS\" -> D.succeed ADMIN_BUDGETS\n                    \"ADMIN_AUDIT\" -> D.succeed ADMIN_AUDIT\n                    _ -> D.fail (\"Unknown permission: \" ++ s)\n            )", 1508, 1508);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmPermission___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("encodePermission : Permission -> E.Value\nencodePermission p =\n    case p of\n        TWITTER_READ -> E.string \"TWITTER_READ\"\n        TWITTER_WRITE -> E.string \"TWITTER_WRITE\"\n        TWITTER_DELETE -> E.string \"TWITTER_DELETE\"\n        REDDIT_READ -> E.string \"REDDIT_READ\"\n        REDDIT_WRITE -> E.string \"REDDIT_WRITE\"\n        LINKEDIN_READ -> E.string \"LINKEDIN_READ\"\n        LINKEDIN_WRITE -> E.string \"LINKEDIN_WRITE\"\n        MASTODON_READ -> E.string \"MASTODON_READ\"\n        MASTODON_WRITE -> E.string \"MASTODON_WRITE\"\n        LLM_LOCAL -> E.string \"LLM_LOCAL\"\n        LLM_API -> E.string \"LLM_API\"\n        LLM_EXPENSIVE -> E.string \"LLM_EXPENSIVE\"\n        SEARCH_WEB -> E.string \"SEARCH_WEB\"\n        SEARCH_NEWS -> E.string \"SEARCH_NEWS\"\n        CONTENT_CREATE -> E.string \"CONTENT_CREATE\"\n        CONTENT_APPROVE -> E.string \"CONTENT_APPROVE\"\n        CONTENT_PUBLISH -> E.string \"CONTENT_PUBLISH\"\n        CAMPAIGN_MANAGE -> E.string \"CAMPAIGN_MANAGE\"\n        ADMIN_USERS -> E.string \"ADMIN_USERS\"\n        ADMIN_BUDGETS -> E.string \"ADMIN_BUDGETS\"\n        ADMIN_AUDIT -> E.string \"ADMIN_AUDIT\"", 1099, 1099);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmPermission___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Compass_Emit_instEmitElmPermission___closed__3;
x_2 = l_Compass_Emit_instEmitElmPermission___closed__2;
x_3 = l_Compass_Emit_instEmitElmPermission___closed__1;
x_4 = l_Compass_Emit_instEmitElmPermission___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmPermission() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitElmPermission___closed__4;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmRole___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Role", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmRole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type Role\n    = ADMIN\n    | MANAGER\n    | CREATOR\n    | VIEWER", 62, 62);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmRole___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decodeRole : Decoder Role\ndecodeRole =\n    D.string\n        |> D.andThen\n            (\\s ->\n                case s of\n                    \"ADMIN\" -> D.succeed ADMIN\n                    \"MANAGER\" -> D.succeed MANAGER\n                    \"CREATOR\" -> D.succeed CREATOR\n                    \"VIEWER\" -> D.succeed VIEWER\n                    _ -> D.fail (\"Unknown role: \" ++ s)\n            )", 385, 385);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmRole___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("encodeRole : Role -> E.Value\nencodeRole r =\n    case r of\n        ADMIN -> E.string \"ADMIN\"\n        MANAGER -> E.string \"MANAGER\"\n        CREATOR -> E.string \"CREATOR\"\n        VIEWER -> E.string \"VIEWER\"", 203, 203);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmRole___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Compass_Emit_instEmitElmRole___closed__3;
x_2 = l_Compass_Emit_instEmitElmRole___closed__2;
x_3 = l_Compass_Emit_instEmitElmRole___closed__1;
x_4 = l_Compass_Emit_instEmitElmRole___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmRole() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitElmRole___closed__4;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmUser___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("User", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmUser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type alias User =\n    { id : String\n    , orgId : String\n    , name : String\n    , email : String\n    , role : Role\n    , mfaEnabled : Bool\n    , dailyBudget : Float\n    , monthlyBudget : Float\n    , isActive : Bool\n    , createdAt : String\n    , updatedAt : String\n    }", 271, 271);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmUser___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decodeUser : Decoder User\ndecodeUser =\n    D.succeed User\n        |> required \"id\" D.string\n        |> required \"org_id\" D.string\n        |> required \"name\" D.string\n        |> required \"email\" D.string\n        |> required \"role\" decodeRole\n        |> required \"mfa_enabled\" D.bool\n        |> required \"daily_budget\" D.float\n        |> required \"monthly_budget\" D.float\n        |> required \"is_active\" D.bool\n        |> required \"created_at\" D.string\n        |> required \"updated_at\" D.string", 492, 492);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmUser___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("encodeUser : User -> E.Value\nencodeUser u =\n    E.object\n        [ ( \"id\", E.string u.id )\n        , ( \"org_id\", E.string u.orgId )\n        , ( \"name\", E.string u.name )\n        , ( \"email\", E.string u.email )\n        , ( \"role\", encodeRole u.role )\n        , ( \"mfa_enabled\", E.bool u.mfaEnabled )\n        , ( \"daily_budget\", E.float u.dailyBudget )\n        , ( \"monthly_budget\", E.float u.monthlyBudget )\n        , ( \"is_active\", E.bool u.isActive )\n        , ( \"created_at\", E.string u.createdAt )\n        , ( \"updated_at\", E.string u.updatedAt )\n        ]", 559, 559);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmUser___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Compass_Emit_instEmitElmUser___closed__3;
x_2 = l_Compass_Emit_instEmitElmUser___closed__2;
x_3 = l_Compass_Emit_instEmitElmUser___closed__1;
x_4 = l_Compass_Emit_instEmitElmUser___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmUser() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitElmUser___closed__4;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmSession___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Session", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmSession___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type alias Session =\n    { id : String\n    , userId : String\n    , createdAt : String\n    , expiresAt : String\n    , lastActivity : String\n    , mfaVerified : Bool\n    }", 169, 169);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmSession___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decodeSession : Decoder Session\ndecodeSession =\n    D.succeed Session\n        |> required \"id\" D.string\n        |> required \"user_id\" D.string\n        |> required \"created_at\" D.string\n        |> required \"expires_at\" D.string\n        |> required \"last_activity\" D.string\n        |> required \"mfa_verified\" D.bool", 313, 313);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmSession___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("encodeSession : Session -> E.Value\nencodeSession s =\n    E.object\n        [ ( \"id\", E.string s.id )\n        , ( \"user_id\", E.string s.userId )\n        , ( \"created_at\", E.string s.createdAt )\n        , ( \"expires_at\", E.string s.expiresAt )\n        , ( \"last_activity\", E.string s.lastActivity )\n        , ( \"mfa_verified\", E.bool s.mfaVerified )\n        ]", 356, 356);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmSession___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Compass_Emit_instEmitElmSession___closed__3;
x_2 = l_Compass_Emit_instEmitElmSession___closed__2;
x_3 = l_Compass_Emit_instEmitElmSession___closed__1;
x_4 = l_Compass_Emit_instEmitElmSession___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmSession() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitElmSession___closed__4;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmJobStatus___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("JobStatus", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmJobStatus___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type JobStatus\n    = Pending\n    | Running\n    | WaitingApproval\n    | Approved\n    | Completed\n    | Failed\n    | Cancelled", 124, 124);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmJobStatus___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decodeJobStatus : Decoder JobStatus\ndecodeJobStatus =\n    D.string\n        |> D.andThen\n            (\\s ->\n                case s of\n                    \"pending\" -> D.succeed Pending\n                    \"running\" -> D.succeed Running\n                    \"waiting_approval\" -> D.succeed WaitingApproval\n                    \"approved\" -> D.succeed Approved\n                    \"completed\" -> D.succeed Completed\n                    \"failed\" -> D.succeed Failed\n                    \"cancelled\" -> D.succeed Cancelled\n                    _ -> D.fail (\"Unknown job status: \" ++ s)\n            )", 590, 590);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmJobStatus___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("encodeJobStatus : JobStatus -> E.Value\nencodeJobStatus s =\n    case s of\n        Pending -> E.string \"pending\"\n        Running -> E.string \"running\"\n        WaitingApproval -> E.string \"waiting_approval\"\n        Approved -> E.string \"approved\"\n        Completed -> E.string \"completed\"\n        Failed -> E.string \"failed\"\n        Cancelled -> E.string \"cancelled\"", 363, 363);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmJobStatus___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Compass_Emit_instEmitElmJobStatus___closed__3;
x_2 = l_Compass_Emit_instEmitElmJobStatus___closed__2;
x_3 = l_Compass_Emit_instEmitElmJobStatus___closed__1;
x_4 = l_Compass_Emit_instEmitElmJobStatus___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Compass_Emit_instEmitElmJobStatus() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitElmJobStatus___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Compass_Emit_EmitPython_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_Emit_EmitPython_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_Emit_EmitPython_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonPermission___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("class Permission(Enum):\n    \"\"\"Fine-grained permissions for tools\"\"\"\n    # Twitter\n    TWITTER_READ = auto()\n    TWITTER_WRITE = auto()\n    TWITTER_DELETE = auto()\n    # Reddit\n    REDDIT_READ = auto()\n    REDDIT_WRITE = auto()\n    # LinkedIn\n    LINKEDIN_READ = auto()\n    LINKEDIN_WRITE = auto()\n    # Mastodon\n    MASTODON_READ = auto()\n    MASTODON_WRITE = auto()\n    # LLM\n    LLM_LOCAL = auto()\n    LLM_API = auto()\n    LLM_EXPENSIVE = auto()\n    # Search\n    SEARCH_WEB = auto()\n    SEARCH_NEWS = auto()\n    # Internal\n    CONTENT_CREATE = auto()\n    CONTENT_APPROVE = auto()\n    CONTENT_PUBLISH = auto()\n    CAMPAIGN_MANAGE = auto()\n    # Admin\n    ADMIN_USERS = auto()\n    ADMIN_BUDGETS = auto()\n    ADMIN_AUDIT = auto()", 729, 729);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonPermission___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_instEmitPythonPermission___closed__0;
x_2 = l_Compass_Emit_instEmitElmPermission___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonPermission() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitPythonPermission___closed__1;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonRole___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("class Role(Enum):\n    \"\"\"User roles with permission sets\"\"\"\n    ADMIN = auto()\n    MANAGER = auto()\n    CREATOR = auto()\n    VIEWER = auto()", 140, 140);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonRole___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_instEmitPythonRole___closed__0;
x_2 = l_Compass_Emit_instEmitElmRole___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonRole() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitPythonRole___closed__1;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonUser___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@dataclass\nclass User:\n    \"\"\"User identity with authentication\"\"\"\n    id: str\n    org_id: str\n    name: str\n    email: str\n    role: Role\n    password_hash: str | None = None\n    mfa_enabled: bool = False\n    mfa_secret: str | None = None\n    daily_budget: float = 10.00\n    monthly_budget: float = 100.00\n    is_active: bool = True\n    created_at: str = \"\"\n    updated_at: str = \"\"", 383, 383);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonUser___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_instEmitPythonUser___closed__0;
x_2 = l_Compass_Emit_instEmitElmUser___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonUser() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitPythonUser___closed__1;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonSession___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@dataclass\nclass Session:\n    \"\"\"User session for web UI\"\"\"\n    id: str\n    user_id: str\n    token_hash: str\n    ip_address: str | None = None\n    user_agent: str | None = None\n    created_at: str = \"\"\n    expires_at: str = \"\"\n    last_activity: str = \"\"\n    mfa_verified: bool = False", 285, 285);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonSession___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_instEmitPythonSession___closed__0;
x_2 = l_Compass_Emit_instEmitElmSession___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonSession() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitPythonSession___closed__1;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonJobStatus___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("class JobStatus(Enum):\n    \"\"\"Job states\"\"\"\n    PENDING = \"pending\"\n    RUNNING = \"running\"\n    WAITING_APPROVAL = \"waiting_approval\"\n    APPROVED = \"approved\"\n    COMPLETED = \"completed\"\n    FAILED = \"failed\"\n    CANCELLED = \"cancelled\"", 237, 237);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonJobStatus___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_instEmitPythonJobStatus___closed__0;
x_2 = l_Compass_Emit_instEmitElmJobStatus___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonJobStatus() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitPythonJobStatus___closed__1;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonJob___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Job", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonJob___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@dataclass\nclass Job:\n    \"\"\"A unit of work\"\"\"\n    id: str\n    job_type: str\n    status: JobStatus\n    created_by: str\n    input_data: str = \"{}\"\n    output_data: str | None = None\n    requires_approval: bool = False\n    approved_by: str | None = None\n    approved_at: str | None = None\n    created_at: str = \"\"\n    started_at: str | None = None\n    completed_at: str | None = None\n    retry_count: int = 0\n    max_retries: int = 3\n    error: str | None = None\n    cost_usd: float = 0.0", 486, 486);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonJob___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_instEmitPythonJob___closed__1;
x_2 = l_Compass_Emit_instEmitPythonJob___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPythonJob() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitPythonJob___closed__2;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("module Compass.Types exposing (..)\n\n{-| AUTO-EXTRACTED FROM LEAN PROOFS\n\n    Every type here has a corresponding Extractable instance in Lean\n    with a proven roundtrip theorem. The encoder/decoder pairs are\n    verified correct by construction.\n\n    DO NOT EDIT - regenerate with `lake exe extract elm`\n-}\n\nimport Json.Decode as D exposing (Decoder)\nimport Json.Decode.Pipeline exposing (required, optional)\nimport Json.Encode as E\n\n\n-- TYPES\n\n", 446, 446);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_Emit_instEmitElmJobStatus___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__1;
x_2 = l_Compass_Emit_instEmitElmSession___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__2;
x_2 = l_Compass_Emit_instEmitElmUser___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__3;
x_2 = l_Compass_Emit_instEmitElmRole___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__4;
x_2 = l_Compass_Emit_instEmitElmPermission___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_Emit_instEmitElmJobStatus___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__6;
x_2 = l_Compass_Emit_instEmitElmSession___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__7;
x_2 = l_Compass_Emit_instEmitElmUser___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__8;
x_2 = l_Compass_Emit_instEmitElmRole___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__9;
x_2 = l_Compass_Emit_instEmitElmPermission___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_Emit_instEmitElmJobStatus___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__11;
x_2 = l_Compass_Emit_instEmitElmSession___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__12;
x_2 = l_Compass_Emit_instEmitElmUser___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__13;
x_2 = l_Compass_Emit_instEmitElmRole___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__14;
x_2 = l_Compass_Emit_instEmitElmPermission___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__5;
x_2 = l_Compass_Emit_elmModule___closed__16;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__17;
x_2 = l_Compass_Emit_elmModule___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n\n-- DECODERS\n\n", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__19;
x_2 = l_Compass_Emit_elmModule___closed__18;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__10;
x_2 = l_Compass_Emit_elmModule___closed__16;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__21;
x_2 = l_Compass_Emit_elmModule___closed__20;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n\n-- ENCODERS\n\n", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__23;
x_2 = l_Compass_Emit_elmModule___closed__22;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__15;
x_2 = l_Compass_Emit_elmModule___closed__16;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__25;
x_2 = l_Compass_Emit_elmModule___closed__24;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_elmModule() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_elmModule___closed__26;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_pythonModule___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\"\"\"\nAUTO-EXTRACTED FROM LEAN PROOFS\n\nEvery type here has a corresponding Extractable instance in Lean\nwith a proven roundtrip theorem.\n\nDO NOT EDIT - regenerate with `lake exe extract python`\n\"\"\"\n\nfrom __future__ import annotations\nfrom dataclasses import dataclass\nfrom enum import Enum, auto\n\n\n", 296, 296);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_pythonModule___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_Emit_instEmitPythonJob___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pythonModule___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pythonModule___closed__1;
x_2 = l_Compass_Emit_instEmitPythonJobStatus___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pythonModule___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pythonModule___closed__2;
x_2 = l_Compass_Emit_instEmitPythonSession___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pythonModule___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pythonModule___closed__3;
x_2 = l_Compass_Emit_instEmitPythonUser___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pythonModule___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pythonModule___closed__4;
x_2 = l_Compass_Emit_instEmitPythonRole___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pythonModule___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pythonModule___closed__5;
x_2 = l_Compass_Emit_instEmitPythonPermission___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pythonModule___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pythonModule___closed__6;
x_2 = l_Compass_Emit_elmModule___closed__16;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pythonModule___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pythonModule___closed__7;
x_2 = l_Compass_Emit_pythonModule___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pythonModule() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_pythonModule___closed__8;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Compass_Emit_EmitPureScript_ctorIdx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_Emit_EmitPureScript_ctorIdx___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_Emit_EmitPureScript_ctorIdx(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptPermission___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("data Permission\n  = TWITTER_READ\n  | TWITTER_WRITE\n  | TWITTER_DELETE\n  | REDDIT_READ\n  | REDDIT_WRITE\n  | LINKEDIN_READ\n  | LINKEDIN_WRITE\n  | MASTODON_READ\n  | MASTODON_WRITE\n  | LLM_LOCAL\n  | LLM_API\n  | LLM_EXPENSIVE\n  | SEARCH_WEB\n  | SEARCH_NEWS\n  | CONTENT_CREATE\n  | CONTENT_APPROVE\n  | CONTENT_PUBLISH\n  | CAMPAIGN_MANAGE\n  | ADMIN_USERS\n  | ADMIN_BUDGETS\n  | ADMIN_AUDIT\n\nderive instance eqPermission :: Eq Permission\nderive instance ordPermission :: Ord Permission\nderive instance genericPermission :: Generic Permission _", 533, 533);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptPermission___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decodePermission :: String -> Either String Permission\ndecodePermission = case _ of\n  \"TWITTER_READ\" -> Right TWITTER_READ\n  \"TWITTER_WRITE\" -> Right TWITTER_WRITE\n  \"TWITTER_DELETE\" -> Right TWITTER_DELETE\n  \"REDDIT_READ\" -> Right REDDIT_READ\n  \"REDDIT_WRITE\" -> Right REDDIT_WRITE\n  \"LINKEDIN_READ\" -> Right LINKEDIN_READ\n  \"LINKEDIN_WRITE\" -> Right LINKEDIN_WRITE\n  \"MASTODON_READ\" -> Right MASTODON_READ\n  \"MASTODON_WRITE\" -> Right MASTODON_WRITE\n  \"LLM_LOCAL\" -> Right LLM_LOCAL\n  \"LLM_API\" -> Right LLM_API\n  \"LLM_EXPENSIVE\" -> Right LLM_EXPENSIVE\n  \"SEARCH_WEB\" -> Right SEARCH_WEB\n  \"SEARCH_NEWS\" -> Right SEARCH_NEWS\n  \"CONTENT_CREATE\" -> Right CONTENT_CREATE\n  \"CONTENT_APPROVE\" -> Right CONTENT_APPROVE\n  \"CONTENT_PUBLISH\" -> Right CONTENT_PUBLISH\n  \"CAMPAIGN_MANAGE\" -> Right CAMPAIGN_MANAGE\n  \"ADMIN_USERS\" -> Right ADMIN_USERS\n  \"ADMIN_BUDGETS\" -> Right ADMIN_BUDGETS\n  \"ADMIN_AUDIT\" -> Right ADMIN_AUDIT\n  s -> Left $ \"Unknown permission: \" <> s", 960, 960);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptPermission___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("encodePermission :: Permission -> String\nencodePermission = case _ of\n  TWITTER_READ -> \"TWITTER_READ\"\n  TWITTER_WRITE -> \"TWITTER_WRITE\"\n  TWITTER_DELETE -> \"TWITTER_DELETE\"\n  REDDIT_READ -> \"REDDIT_READ\"\n  REDDIT_WRITE -> \"REDDIT_WRITE\"\n  LINKEDIN_READ -> \"LINKEDIN_READ\"\n  LINKEDIN_WRITE -> \"LINKEDIN_WRITE\"\n  MASTODON_READ -> \"MASTODON_READ\"\n  MASTODON_WRITE -> \"MASTODON_WRITE\"\n  LLM_LOCAL -> \"LLM_LOCAL\"\n  LLM_API -> \"LLM_API\"\n  LLM_EXPENSIVE -> \"LLM_EXPENSIVE\"\n  SEARCH_WEB -> \"SEARCH_WEB\"\n  SEARCH_NEWS -> \"SEARCH_NEWS\"\n  CONTENT_CREATE -> \"CONTENT_CREATE\"\n  CONTENT_APPROVE -> \"CONTENT_APPROVE\"\n  CONTENT_PUBLISH -> \"CONTENT_PUBLISH\"\n  CAMPAIGN_MANAGE -> \"CAMPAIGN_MANAGE\"\n  ADMIN_USERS -> \"ADMIN_USERS\"\n  ADMIN_BUDGETS -> \"ADMIN_BUDGETS\"\n  ADMIN_AUDIT -> \"ADMIN_AUDIT\"", 778, 778);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptPermission___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Compass_Emit_instEmitPureScriptPermission___closed__2;
x_2 = l_Compass_Emit_instEmitPureScriptPermission___closed__1;
x_3 = l_Compass_Emit_instEmitPureScriptPermission___closed__0;
x_4 = l_Compass_Emit_instEmitElmPermission___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptPermission() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitPureScriptPermission___closed__3;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptRole___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("data Role\n  = Admin\n  | Manager\n  | Creator\n  | Viewer\n\nderive instance eqRole :: Eq Role\nderive instance ordRole :: Ord Role\nderive instance genericRole :: Generic Role _", 171, 171);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptRole___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decodeRole :: String -> Either String Role\ndecodeRole = case _ of\n  \"ADMIN\" -> Right Admin\n  \"MANAGER\" -> Right Manager\n  \"CREATOR\" -> Right Creator\n  \"VIEWER\" -> Right Viewer\n  s -> Left $ \"Unknown role: \" <> s", 211, 211);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptRole___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("encodeRole :: Role -> String\nencodeRole = case _ of\n  Admin -> \"ADMIN\"\n  Manager -> \"MANAGER\"\n  Creator -> \"CREATOR\"\n  Viewer -> \"VIEWER\"", 137, 137);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptRole___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Compass_Emit_instEmitPureScriptRole___closed__2;
x_2 = l_Compass_Emit_instEmitPureScriptRole___closed__1;
x_3 = l_Compass_Emit_instEmitPureScriptRole___closed__0;
x_4 = l_Compass_Emit_instEmitElmRole___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptRole() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitPureScriptRole___closed__3;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptUser___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type User =\n  { id :: String\n  , orgId :: String\n  , name :: String\n  , email :: String\n  , role :: Role\n  , mfaEnabled :: Boolean\n  , dailyBudget :: Number\n  , monthlyBudget :: Number\n  , isActive :: Boolean\n  , createdAt :: String\n  , updatedAt :: String\n  }", 260, 260);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptUser___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decodeUser :: Json -> Either String User\ndecodeUser json = do\n  obj <- decodeJson json\n  id <- obj .: \"id\"\n  orgId <- obj .: \"org_id\"\n  name <- obj .: \"name\"\n  email <- obj .: \"email\"\n  role <- obj .: \"role\" >>= decodeRole\n  mfaEnabled <- obj .: \"mfa_enabled\"\n  dailyBudget <- obj .: \"daily_budget\"\n  monthlyBudget <- obj .: \"monthly_budget\"\n  isActive <- obj .: \"is_active\"\n  createdAt <- obj .: \"created_at\"\n  updatedAt <- obj .: \"updated_at\"\n  pure { id, orgId, name, email, role, mfaEnabled, dailyBudget, monthlyBudget, isActive, createdAt, updatedAt }", 556, 556);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptUser___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("encodeUser :: User -> Json\nencodeUser u = encodeJson\n  { id: u.id\n  , org_id: u.orgId\n  , name: u.name\n  , email: u.email\n  , role: encodeRole u.role\n  , mfa_enabled: u.mfaEnabled\n  , daily_budget: u.dailyBudget\n  , monthly_budget: u.monthlyBudget\n  , is_active: u.isActive\n  , created_at: u.createdAt\n  , updated_at: u.updatedAt\n  }", 333, 333);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptUser___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Compass_Emit_instEmitPureScriptUser___closed__2;
x_2 = l_Compass_Emit_instEmitPureScriptUser___closed__1;
x_3 = l_Compass_Emit_instEmitPureScriptUser___closed__0;
x_4 = l_Compass_Emit_instEmitElmUser___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptUser() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitPureScriptUser___closed__3;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptJobStatus___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("data JobStatus\n  = Pending\n  | Running\n  | WaitingApproval\n  | Approved\n  | Completed\n  | Failed\n  | Cancelled\n\nderive instance eqJobStatus :: Eq JobStatus\nderive instance genericJobStatus :: Generic JobStatus _", 211, 211);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptJobStatus___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decodeJobStatus :: String -> Either String JobStatus\ndecodeJobStatus = case _ of\n  \"pending\" -> Right Pending\n  \"running\" -> Right Running\n  \"waiting_approval\" -> Right WaitingApproval\n  \"approved\" -> Right Approved\n  \"completed\" -> Right Completed\n  \"failed\" -> Right Failed\n  \"cancelled\" -> Right Cancelled\n  s -> Left $ \"Unknown job status: \" <> s", 350, 350);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptJobStatus___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("encodeJobStatus :: JobStatus -> String\nencodeJobStatus = case _ of\n  Pending -> \"pending\"\n  Running -> \"running\"\n  WaitingApproval -> \"waiting_approval\"\n  Approved -> \"approved\"\n  Completed -> \"completed\"\n  Failed -> \"failed\"\n  Cancelled -> \"cancelled\"", 252, 252);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptJobStatus___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Compass_Emit_instEmitPureScriptJobStatus___closed__2;
x_2 = l_Compass_Emit_instEmitPureScriptJobStatus___closed__1;
x_3 = l_Compass_Emit_instEmitPureScriptJobStatus___closed__0;
x_4 = l_Compass_Emit_instEmitElmJobStatus___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Compass_Emit_instEmitPureScriptJobStatus() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_instEmitPureScriptJobStatus___closed__3;
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- AUTO-EXTRACTED FROM LEAN PROOFS\n-- Every type here has a corresponding Extractable instance in Lean\n-- with a proven roundtrip theorem.\n--\n-- DO NOT EDIT - regenerate with `lake exe compass-extract purescript`\n\nmodule Compass.Types where\n\nimport Prelude\nimport Data.Either (Either(..))\nimport Data.Maybe (Maybe(..))\nimport Data.Generic.Rep (class Generic)\nimport Data.Argonaut.Core (Json)\nimport Data.Argonaut.Decode (decodeJson, (.:), (.:\?))\nimport Data.Argonaut.Encode (encodeJson)\n\n\n-- TYPES\n\n", 499, 499);
return x_1;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_Emit_instEmitPureScriptJobStatus___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__1;
x_2 = l_Compass_Emit_instEmitPureScriptUser___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__2;
x_2 = l_Compass_Emit_instEmitPureScriptRole___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__3;
x_2 = l_Compass_Emit_instEmitPureScriptPermission___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_Emit_instEmitPureScriptJobStatus___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__5;
x_2 = l_Compass_Emit_instEmitPureScriptUser___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__6;
x_2 = l_Compass_Emit_instEmitPureScriptRole___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__7;
x_2 = l_Compass_Emit_instEmitPureScriptPermission___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_Emit_instEmitPureScriptJobStatus___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__9;
x_2 = l_Compass_Emit_instEmitPureScriptUser___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__10;
x_2 = l_Compass_Emit_instEmitPureScriptRole___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__11;
x_2 = l_Compass_Emit_instEmitPureScriptPermission___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__4;
x_2 = l_Compass_Emit_elmModule___closed__16;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__13;
x_2 = l_Compass_Emit_pureScriptModule___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__19;
x_2 = l_Compass_Emit_pureScriptModule___closed__14;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__8;
x_2 = l_Compass_Emit_elmModule___closed__16;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__16;
x_2 = l_Compass_Emit_pureScriptModule___closed__15;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_elmModule___closed__23;
x_2 = l_Compass_Emit_pureScriptModule___closed__17;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__12;
x_2 = l_Compass_Emit_elmModule___closed__16;
x_3 = l_String_intercalate(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Emit_pureScriptModule___closed__19;
x_2 = l_Compass_Emit_pureScriptModule___closed__18;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Emit_pureScriptModule() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Emit_pureScriptModule___closed__20;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Compass_Core(uint8_t builtin);
lean_object* initialize_Compass_Permissions(uint8_t builtin);
lean_object* initialize_Compass_Auth(uint8_t builtin);
lean_object* initialize_Compass_Tools(uint8_t builtin);
lean_object* initialize_Compass_Audit(uint8_t builtin);
lean_object* initialize_Compass_Jobs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Compass_Emit(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Permissions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Auth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Tools(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Audit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Jobs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Compass_Emit_instEmitElmPermission___closed__0 = _init_l_Compass_Emit_instEmitElmPermission___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitElmPermission___closed__0);
l_Compass_Emit_instEmitElmPermission___closed__1 = _init_l_Compass_Emit_instEmitElmPermission___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitElmPermission___closed__1);
l_Compass_Emit_instEmitElmPermission___closed__2 = _init_l_Compass_Emit_instEmitElmPermission___closed__2();
lean_mark_persistent(l_Compass_Emit_instEmitElmPermission___closed__2);
l_Compass_Emit_instEmitElmPermission___closed__3 = _init_l_Compass_Emit_instEmitElmPermission___closed__3();
lean_mark_persistent(l_Compass_Emit_instEmitElmPermission___closed__3);
l_Compass_Emit_instEmitElmPermission___closed__4 = _init_l_Compass_Emit_instEmitElmPermission___closed__4();
lean_mark_persistent(l_Compass_Emit_instEmitElmPermission___closed__4);
l_Compass_Emit_instEmitElmPermission = _init_l_Compass_Emit_instEmitElmPermission();
lean_mark_persistent(l_Compass_Emit_instEmitElmPermission);
l_Compass_Emit_instEmitElmRole___closed__0 = _init_l_Compass_Emit_instEmitElmRole___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitElmRole___closed__0);
l_Compass_Emit_instEmitElmRole___closed__1 = _init_l_Compass_Emit_instEmitElmRole___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitElmRole___closed__1);
l_Compass_Emit_instEmitElmRole___closed__2 = _init_l_Compass_Emit_instEmitElmRole___closed__2();
lean_mark_persistent(l_Compass_Emit_instEmitElmRole___closed__2);
l_Compass_Emit_instEmitElmRole___closed__3 = _init_l_Compass_Emit_instEmitElmRole___closed__3();
lean_mark_persistent(l_Compass_Emit_instEmitElmRole___closed__3);
l_Compass_Emit_instEmitElmRole___closed__4 = _init_l_Compass_Emit_instEmitElmRole___closed__4();
lean_mark_persistent(l_Compass_Emit_instEmitElmRole___closed__4);
l_Compass_Emit_instEmitElmRole = _init_l_Compass_Emit_instEmitElmRole();
lean_mark_persistent(l_Compass_Emit_instEmitElmRole);
l_Compass_Emit_instEmitElmUser___closed__0 = _init_l_Compass_Emit_instEmitElmUser___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitElmUser___closed__0);
l_Compass_Emit_instEmitElmUser___closed__1 = _init_l_Compass_Emit_instEmitElmUser___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitElmUser___closed__1);
l_Compass_Emit_instEmitElmUser___closed__2 = _init_l_Compass_Emit_instEmitElmUser___closed__2();
lean_mark_persistent(l_Compass_Emit_instEmitElmUser___closed__2);
l_Compass_Emit_instEmitElmUser___closed__3 = _init_l_Compass_Emit_instEmitElmUser___closed__3();
lean_mark_persistent(l_Compass_Emit_instEmitElmUser___closed__3);
l_Compass_Emit_instEmitElmUser___closed__4 = _init_l_Compass_Emit_instEmitElmUser___closed__4();
lean_mark_persistent(l_Compass_Emit_instEmitElmUser___closed__4);
l_Compass_Emit_instEmitElmUser = _init_l_Compass_Emit_instEmitElmUser();
lean_mark_persistent(l_Compass_Emit_instEmitElmUser);
l_Compass_Emit_instEmitElmSession___closed__0 = _init_l_Compass_Emit_instEmitElmSession___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitElmSession___closed__0);
l_Compass_Emit_instEmitElmSession___closed__1 = _init_l_Compass_Emit_instEmitElmSession___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitElmSession___closed__1);
l_Compass_Emit_instEmitElmSession___closed__2 = _init_l_Compass_Emit_instEmitElmSession___closed__2();
lean_mark_persistent(l_Compass_Emit_instEmitElmSession___closed__2);
l_Compass_Emit_instEmitElmSession___closed__3 = _init_l_Compass_Emit_instEmitElmSession___closed__3();
lean_mark_persistent(l_Compass_Emit_instEmitElmSession___closed__3);
l_Compass_Emit_instEmitElmSession___closed__4 = _init_l_Compass_Emit_instEmitElmSession___closed__4();
lean_mark_persistent(l_Compass_Emit_instEmitElmSession___closed__4);
l_Compass_Emit_instEmitElmSession = _init_l_Compass_Emit_instEmitElmSession();
lean_mark_persistent(l_Compass_Emit_instEmitElmSession);
l_Compass_Emit_instEmitElmJobStatus___closed__0 = _init_l_Compass_Emit_instEmitElmJobStatus___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitElmJobStatus___closed__0);
l_Compass_Emit_instEmitElmJobStatus___closed__1 = _init_l_Compass_Emit_instEmitElmJobStatus___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitElmJobStatus___closed__1);
l_Compass_Emit_instEmitElmJobStatus___closed__2 = _init_l_Compass_Emit_instEmitElmJobStatus___closed__2();
lean_mark_persistent(l_Compass_Emit_instEmitElmJobStatus___closed__2);
l_Compass_Emit_instEmitElmJobStatus___closed__3 = _init_l_Compass_Emit_instEmitElmJobStatus___closed__3();
lean_mark_persistent(l_Compass_Emit_instEmitElmJobStatus___closed__3);
l_Compass_Emit_instEmitElmJobStatus___closed__4 = _init_l_Compass_Emit_instEmitElmJobStatus___closed__4();
lean_mark_persistent(l_Compass_Emit_instEmitElmJobStatus___closed__4);
l_Compass_Emit_instEmitElmJobStatus = _init_l_Compass_Emit_instEmitElmJobStatus();
lean_mark_persistent(l_Compass_Emit_instEmitElmJobStatus);
l_Compass_Emit_instEmitPythonPermission___closed__0 = _init_l_Compass_Emit_instEmitPythonPermission___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitPythonPermission___closed__0);
l_Compass_Emit_instEmitPythonPermission___closed__1 = _init_l_Compass_Emit_instEmitPythonPermission___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitPythonPermission___closed__1);
l_Compass_Emit_instEmitPythonPermission = _init_l_Compass_Emit_instEmitPythonPermission();
lean_mark_persistent(l_Compass_Emit_instEmitPythonPermission);
l_Compass_Emit_instEmitPythonRole___closed__0 = _init_l_Compass_Emit_instEmitPythonRole___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitPythonRole___closed__0);
l_Compass_Emit_instEmitPythonRole___closed__1 = _init_l_Compass_Emit_instEmitPythonRole___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitPythonRole___closed__1);
l_Compass_Emit_instEmitPythonRole = _init_l_Compass_Emit_instEmitPythonRole();
lean_mark_persistent(l_Compass_Emit_instEmitPythonRole);
l_Compass_Emit_instEmitPythonUser___closed__0 = _init_l_Compass_Emit_instEmitPythonUser___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitPythonUser___closed__0);
l_Compass_Emit_instEmitPythonUser___closed__1 = _init_l_Compass_Emit_instEmitPythonUser___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitPythonUser___closed__1);
l_Compass_Emit_instEmitPythonUser = _init_l_Compass_Emit_instEmitPythonUser();
lean_mark_persistent(l_Compass_Emit_instEmitPythonUser);
l_Compass_Emit_instEmitPythonSession___closed__0 = _init_l_Compass_Emit_instEmitPythonSession___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitPythonSession___closed__0);
l_Compass_Emit_instEmitPythonSession___closed__1 = _init_l_Compass_Emit_instEmitPythonSession___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitPythonSession___closed__1);
l_Compass_Emit_instEmitPythonSession = _init_l_Compass_Emit_instEmitPythonSession();
lean_mark_persistent(l_Compass_Emit_instEmitPythonSession);
l_Compass_Emit_instEmitPythonJobStatus___closed__0 = _init_l_Compass_Emit_instEmitPythonJobStatus___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitPythonJobStatus___closed__0);
l_Compass_Emit_instEmitPythonJobStatus___closed__1 = _init_l_Compass_Emit_instEmitPythonJobStatus___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitPythonJobStatus___closed__1);
l_Compass_Emit_instEmitPythonJobStatus = _init_l_Compass_Emit_instEmitPythonJobStatus();
lean_mark_persistent(l_Compass_Emit_instEmitPythonJobStatus);
l_Compass_Emit_instEmitPythonJob___closed__0 = _init_l_Compass_Emit_instEmitPythonJob___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitPythonJob___closed__0);
l_Compass_Emit_instEmitPythonJob___closed__1 = _init_l_Compass_Emit_instEmitPythonJob___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitPythonJob___closed__1);
l_Compass_Emit_instEmitPythonJob___closed__2 = _init_l_Compass_Emit_instEmitPythonJob___closed__2();
lean_mark_persistent(l_Compass_Emit_instEmitPythonJob___closed__2);
l_Compass_Emit_instEmitPythonJob = _init_l_Compass_Emit_instEmitPythonJob();
lean_mark_persistent(l_Compass_Emit_instEmitPythonJob);
l_Compass_Emit_elmModule___closed__0 = _init_l_Compass_Emit_elmModule___closed__0();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__0);
l_Compass_Emit_elmModule___closed__1 = _init_l_Compass_Emit_elmModule___closed__1();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__1);
l_Compass_Emit_elmModule___closed__2 = _init_l_Compass_Emit_elmModule___closed__2();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__2);
l_Compass_Emit_elmModule___closed__3 = _init_l_Compass_Emit_elmModule___closed__3();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__3);
l_Compass_Emit_elmModule___closed__4 = _init_l_Compass_Emit_elmModule___closed__4();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__4);
l_Compass_Emit_elmModule___closed__5 = _init_l_Compass_Emit_elmModule___closed__5();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__5);
l_Compass_Emit_elmModule___closed__6 = _init_l_Compass_Emit_elmModule___closed__6();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__6);
l_Compass_Emit_elmModule___closed__7 = _init_l_Compass_Emit_elmModule___closed__7();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__7);
l_Compass_Emit_elmModule___closed__8 = _init_l_Compass_Emit_elmModule___closed__8();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__8);
l_Compass_Emit_elmModule___closed__9 = _init_l_Compass_Emit_elmModule___closed__9();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__9);
l_Compass_Emit_elmModule___closed__10 = _init_l_Compass_Emit_elmModule___closed__10();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__10);
l_Compass_Emit_elmModule___closed__11 = _init_l_Compass_Emit_elmModule___closed__11();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__11);
l_Compass_Emit_elmModule___closed__12 = _init_l_Compass_Emit_elmModule___closed__12();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__12);
l_Compass_Emit_elmModule___closed__13 = _init_l_Compass_Emit_elmModule___closed__13();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__13);
l_Compass_Emit_elmModule___closed__14 = _init_l_Compass_Emit_elmModule___closed__14();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__14);
l_Compass_Emit_elmModule___closed__15 = _init_l_Compass_Emit_elmModule___closed__15();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__15);
l_Compass_Emit_elmModule___closed__16 = _init_l_Compass_Emit_elmModule___closed__16();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__16);
l_Compass_Emit_elmModule___closed__17 = _init_l_Compass_Emit_elmModule___closed__17();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__17);
l_Compass_Emit_elmModule___closed__18 = _init_l_Compass_Emit_elmModule___closed__18();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__18);
l_Compass_Emit_elmModule___closed__19 = _init_l_Compass_Emit_elmModule___closed__19();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__19);
l_Compass_Emit_elmModule___closed__20 = _init_l_Compass_Emit_elmModule___closed__20();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__20);
l_Compass_Emit_elmModule___closed__21 = _init_l_Compass_Emit_elmModule___closed__21();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__21);
l_Compass_Emit_elmModule___closed__22 = _init_l_Compass_Emit_elmModule___closed__22();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__22);
l_Compass_Emit_elmModule___closed__23 = _init_l_Compass_Emit_elmModule___closed__23();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__23);
l_Compass_Emit_elmModule___closed__24 = _init_l_Compass_Emit_elmModule___closed__24();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__24);
l_Compass_Emit_elmModule___closed__25 = _init_l_Compass_Emit_elmModule___closed__25();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__25);
l_Compass_Emit_elmModule___closed__26 = _init_l_Compass_Emit_elmModule___closed__26();
lean_mark_persistent(l_Compass_Emit_elmModule___closed__26);
l_Compass_Emit_elmModule = _init_l_Compass_Emit_elmModule();
lean_mark_persistent(l_Compass_Emit_elmModule);
l_Compass_Emit_pythonModule___closed__0 = _init_l_Compass_Emit_pythonModule___closed__0();
lean_mark_persistent(l_Compass_Emit_pythonModule___closed__0);
l_Compass_Emit_pythonModule___closed__1 = _init_l_Compass_Emit_pythonModule___closed__1();
lean_mark_persistent(l_Compass_Emit_pythonModule___closed__1);
l_Compass_Emit_pythonModule___closed__2 = _init_l_Compass_Emit_pythonModule___closed__2();
lean_mark_persistent(l_Compass_Emit_pythonModule___closed__2);
l_Compass_Emit_pythonModule___closed__3 = _init_l_Compass_Emit_pythonModule___closed__3();
lean_mark_persistent(l_Compass_Emit_pythonModule___closed__3);
l_Compass_Emit_pythonModule___closed__4 = _init_l_Compass_Emit_pythonModule___closed__4();
lean_mark_persistent(l_Compass_Emit_pythonModule___closed__4);
l_Compass_Emit_pythonModule___closed__5 = _init_l_Compass_Emit_pythonModule___closed__5();
lean_mark_persistent(l_Compass_Emit_pythonModule___closed__5);
l_Compass_Emit_pythonModule___closed__6 = _init_l_Compass_Emit_pythonModule___closed__6();
lean_mark_persistent(l_Compass_Emit_pythonModule___closed__6);
l_Compass_Emit_pythonModule___closed__7 = _init_l_Compass_Emit_pythonModule___closed__7();
lean_mark_persistent(l_Compass_Emit_pythonModule___closed__7);
l_Compass_Emit_pythonModule___closed__8 = _init_l_Compass_Emit_pythonModule___closed__8();
lean_mark_persistent(l_Compass_Emit_pythonModule___closed__8);
l_Compass_Emit_pythonModule = _init_l_Compass_Emit_pythonModule();
lean_mark_persistent(l_Compass_Emit_pythonModule);
l_Compass_Emit_instEmitPureScriptPermission___closed__0 = _init_l_Compass_Emit_instEmitPureScriptPermission___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptPermission___closed__0);
l_Compass_Emit_instEmitPureScriptPermission___closed__1 = _init_l_Compass_Emit_instEmitPureScriptPermission___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptPermission___closed__1);
l_Compass_Emit_instEmitPureScriptPermission___closed__2 = _init_l_Compass_Emit_instEmitPureScriptPermission___closed__2();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptPermission___closed__2);
l_Compass_Emit_instEmitPureScriptPermission___closed__3 = _init_l_Compass_Emit_instEmitPureScriptPermission___closed__3();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptPermission___closed__3);
l_Compass_Emit_instEmitPureScriptPermission = _init_l_Compass_Emit_instEmitPureScriptPermission();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptPermission);
l_Compass_Emit_instEmitPureScriptRole___closed__0 = _init_l_Compass_Emit_instEmitPureScriptRole___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptRole___closed__0);
l_Compass_Emit_instEmitPureScriptRole___closed__1 = _init_l_Compass_Emit_instEmitPureScriptRole___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptRole___closed__1);
l_Compass_Emit_instEmitPureScriptRole___closed__2 = _init_l_Compass_Emit_instEmitPureScriptRole___closed__2();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptRole___closed__2);
l_Compass_Emit_instEmitPureScriptRole___closed__3 = _init_l_Compass_Emit_instEmitPureScriptRole___closed__3();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptRole___closed__3);
l_Compass_Emit_instEmitPureScriptRole = _init_l_Compass_Emit_instEmitPureScriptRole();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptRole);
l_Compass_Emit_instEmitPureScriptUser___closed__0 = _init_l_Compass_Emit_instEmitPureScriptUser___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptUser___closed__0);
l_Compass_Emit_instEmitPureScriptUser___closed__1 = _init_l_Compass_Emit_instEmitPureScriptUser___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptUser___closed__1);
l_Compass_Emit_instEmitPureScriptUser___closed__2 = _init_l_Compass_Emit_instEmitPureScriptUser___closed__2();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptUser___closed__2);
l_Compass_Emit_instEmitPureScriptUser___closed__3 = _init_l_Compass_Emit_instEmitPureScriptUser___closed__3();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptUser___closed__3);
l_Compass_Emit_instEmitPureScriptUser = _init_l_Compass_Emit_instEmitPureScriptUser();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptUser);
l_Compass_Emit_instEmitPureScriptJobStatus___closed__0 = _init_l_Compass_Emit_instEmitPureScriptJobStatus___closed__0();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptJobStatus___closed__0);
l_Compass_Emit_instEmitPureScriptJobStatus___closed__1 = _init_l_Compass_Emit_instEmitPureScriptJobStatus___closed__1();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptJobStatus___closed__1);
l_Compass_Emit_instEmitPureScriptJobStatus___closed__2 = _init_l_Compass_Emit_instEmitPureScriptJobStatus___closed__2();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptJobStatus___closed__2);
l_Compass_Emit_instEmitPureScriptJobStatus___closed__3 = _init_l_Compass_Emit_instEmitPureScriptJobStatus___closed__3();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptJobStatus___closed__3);
l_Compass_Emit_instEmitPureScriptJobStatus = _init_l_Compass_Emit_instEmitPureScriptJobStatus();
lean_mark_persistent(l_Compass_Emit_instEmitPureScriptJobStatus);
l_Compass_Emit_pureScriptModule___closed__0 = _init_l_Compass_Emit_pureScriptModule___closed__0();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__0);
l_Compass_Emit_pureScriptModule___closed__1 = _init_l_Compass_Emit_pureScriptModule___closed__1();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__1);
l_Compass_Emit_pureScriptModule___closed__2 = _init_l_Compass_Emit_pureScriptModule___closed__2();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__2);
l_Compass_Emit_pureScriptModule___closed__3 = _init_l_Compass_Emit_pureScriptModule___closed__3();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__3);
l_Compass_Emit_pureScriptModule___closed__4 = _init_l_Compass_Emit_pureScriptModule___closed__4();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__4);
l_Compass_Emit_pureScriptModule___closed__5 = _init_l_Compass_Emit_pureScriptModule___closed__5();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__5);
l_Compass_Emit_pureScriptModule___closed__6 = _init_l_Compass_Emit_pureScriptModule___closed__6();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__6);
l_Compass_Emit_pureScriptModule___closed__7 = _init_l_Compass_Emit_pureScriptModule___closed__7();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__7);
l_Compass_Emit_pureScriptModule___closed__8 = _init_l_Compass_Emit_pureScriptModule___closed__8();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__8);
l_Compass_Emit_pureScriptModule___closed__9 = _init_l_Compass_Emit_pureScriptModule___closed__9();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__9);
l_Compass_Emit_pureScriptModule___closed__10 = _init_l_Compass_Emit_pureScriptModule___closed__10();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__10);
l_Compass_Emit_pureScriptModule___closed__11 = _init_l_Compass_Emit_pureScriptModule___closed__11();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__11);
l_Compass_Emit_pureScriptModule___closed__12 = _init_l_Compass_Emit_pureScriptModule___closed__12();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__12);
l_Compass_Emit_pureScriptModule___closed__13 = _init_l_Compass_Emit_pureScriptModule___closed__13();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__13);
l_Compass_Emit_pureScriptModule___closed__14 = _init_l_Compass_Emit_pureScriptModule___closed__14();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__14);
l_Compass_Emit_pureScriptModule___closed__15 = _init_l_Compass_Emit_pureScriptModule___closed__15();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__15);
l_Compass_Emit_pureScriptModule___closed__16 = _init_l_Compass_Emit_pureScriptModule___closed__16();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__16);
l_Compass_Emit_pureScriptModule___closed__17 = _init_l_Compass_Emit_pureScriptModule___closed__17();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__17);
l_Compass_Emit_pureScriptModule___closed__18 = _init_l_Compass_Emit_pureScriptModule___closed__18();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__18);
l_Compass_Emit_pureScriptModule___closed__19 = _init_l_Compass_Emit_pureScriptModule___closed__19();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__19);
l_Compass_Emit_pureScriptModule___closed__20 = _init_l_Compass_Emit_pureScriptModule___closed__20();
lean_mark_persistent(l_Compass_Emit_pureScriptModule___closed__20);
l_Compass_Emit_pureScriptModule = _init_l_Compass_Emit_pureScriptModule();
lean_mark_persistent(l_Compass_Emit_pureScriptModule);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
