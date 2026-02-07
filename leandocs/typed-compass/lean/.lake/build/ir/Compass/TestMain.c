// Lean compiler output
// Module: Compass.TestMain
// Imports: public import Init public import Compass.Core public import Compass.Auth public import Compass.Router public import Compass.Budget public import Compass.BudgetState public import Compass.RateLimiter public import Compass.Flags
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
static lean_object* l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0___closed__0;
static lean_object* l_Compass_TestMain_authTestCases___closed__16;
static lean_object* l_Compass_TestMain_routerTestCases___closed__35;
static lean_object* l_Compass_TestMain_routerTestCases___closed__40;
static lean_object* l_Compass_TestMain_authTestCases___closed__11;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__11;
static lean_object* l_Compass_TestMain_main___closed__0;
LEAN_EXPORT lean_object* l_Compass_TestMain_budgetTestCases;
LEAN_EXPORT lean_object* l_Compass_TestMain_main();
static lean_object* l_Compass_TestMain_budgetTestCases___closed__26;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__25;
static lean_object* l_Compass_TestMain_routerTestCases___closed__37;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__28;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__5;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__16;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__17;
static lean_object* l_Compass_TestMain_routerTestCases___closed__42;
static lean_object* l_Compass_TestMain_authTestCases___closed__0;
static lean_object* l_Compass_TestMain_authTestCases___closed__23;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__20;
static lean_object* l_Compass_TestMain_routerTestCases___closed__46;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__4;
static lean_object* l_Compass_TestMain_authTestCases___closed__1;
static lean_object* l_Compass_TestMain_routerTestCases___closed__5;
static lean_object* l_Compass_TestMain_routerTestCases___closed__19;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__15;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__20;
static lean_object* l_Compass_TestMain_routerTestCases___closed__14;
static lean_object* l_Compass_TestMain_routerTestCases___closed__32;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__10;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__15;
static lean_object* l_Compass_TestMain_routerTestCases___closed__22;
static lean_object* l_Compass_TestMain_authTestCases___closed__32;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0(lean_object*, lean_object*);
static lean_object* l_Compass_TestMain_routerTestCases___closed__8;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__10;
static lean_object* l_Compass_TestMain_authTestCases___closed__15;
static lean_object* l_Compass_TestMain_routerTestCases___closed__24;
static lean_object* l_Compass_TestMain_authTestCases___closed__5;
static lean_object* l_Compass_TestMain_routerTestCases___closed__17;
static lean_object* l_Compass_TestMain_routerTestCases___closed__26;
static lean_object* l_Compass_TestMain_routerTestCases___closed__2;
static lean_object* l_Compass_TestMain_authTestCases___closed__2;
static lean_object* l_Compass_TestMain_generatePythonTests___closed__3;
static lean_object* l_Compass_TestMain_routerTestCases___closed__33;
static lean_object* l_Compass_TestMain_generatePythonTests___closed__0;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__14;
static lean_object* l_Compass_TestMain_generatePythonTests___closed__2;
static lean_object* l_Compass_TestMain_routerTestCases___closed__21;
static lean_object* l_Compass_TestMain_routerTestCases___closed__0;
static lean_object* l_Compass_TestMain_authTestCases___closed__29;
static lean_object* l_Compass_TestMain_routerTestCases___closed__45;
static lean_object* l_Compass_TestMain_routerTestCases___closed__9;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__24;
LEAN_EXPORT lean_object* l_Compass_TestMain_main___boxed(lean_object*);
static lean_object* l_Compass_TestMain_authTestCases___closed__25;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__6;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__14;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__13;
static lean_object* l_Compass_TestMain_routerTestCases___closed__16;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__3;
static lean_object* l_Compass_TestMain_routerTestCases___closed__10;
static lean_object* l_Compass_TestMain_routerTestCases___closed__18;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__30;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__23;
LEAN_EXPORT lean_object* l_Compass_TestMain_rateLimitTestCases;
static lean_object* l_Compass_TestMain_routerTestCases___closed__15;
static lean_object* l_Compass_TestMain_authTestCases___closed__33;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__8;
static lean_object* l_Compass_TestMain_routerTestCases___closed__30;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__22;
static lean_object* l_Compass_TestMain_routerTestCases___closed__27;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__6;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__7;
static lean_object* l_Compass_TestMain_authTestCases___closed__31;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__16;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__1;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__19;
LEAN_EXPORT lean_object* l_Compass_TestMain_generatePythonTests;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__21;
static lean_object* l_Compass_TestMain_authTestCases___closed__14;
lean_object* l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(lean_object*);
static lean_object* l_Compass_TestMain_routerTestCases___closed__39;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__7;
LEAN_EXPORT lean_object* l_Compass_TestMain_routerTestCases;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__13;
static lean_object* l_Compass_TestMain_routerTestCases___closed__4;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__18;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__21;
static lean_object* l_Compass_TestMain_routerTestCases___closed__11;
static lean_object* l_Compass_TestMain_routerTestCases___closed__38;
static lean_object* l_Compass_TestMain_authTestCases___closed__17;
static lean_object* l_Compass_TestMain_routerTestCases___closed__44;
static lean_object* l_Compass_TestMain_authTestCases___closed__24;
static lean_object* l_Compass_TestMain_authTestCases___closed__3;
static lean_object* l_Compass_TestMain_authTestCases___closed__34;
LEAN_EXPORT lean_object* l_Compass_TestMain_authTestCases;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__3;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__29;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__9;
static lean_object* l_Compass_TestMain_authTestCases___closed__12;
static lean_object* l_Compass_TestMain_routerTestCases___closed__29;
static lean_object* l_Compass_TestMain_routerTestCases___closed__6;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__27;
static lean_object* l_Compass_TestMain_routerTestCases___closed__20;
static lean_object* l_Compass_TestMain_main___closed__2;
static lean_object* l_Compass_TestMain_routerTestCases___closed__43;
static lean_object* l_Compass_TestMain_routerTestCases___closed__31;
static lean_object* l_Compass_TestMain_authTestCases___closed__7;
static lean_object* l_Compass_TestMain_routerTestCases___closed__12;
static lean_object* l_Compass_TestMain_authTestCases___closed__26;
static lean_object* l_Compass_TestMain_authTestCases___closed__4;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__4;
static lean_object* l_Compass_TestMain_authTestCases___closed__9;
static lean_object* l_Compass_TestMain_authTestCases___closed__8;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__17;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__2;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__18;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__12;
lean_object* l_List_reverse___redArg(lean_object*);
static lean_object* l_Compass_TestMain_routerTestCases___closed__34;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__12;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__5;
static lean_object* l_Compass_TestMain_authTestCases___closed__19;
static lean_object* l_Compass_TestMain_routerTestCases___closed__7;
static lean_object* l_Compass_TestMain_routerTestCases___closed__23;
static lean_object* l_Compass_TestMain_generatePythonTests___closed__1;
static lean_object* l_Compass_TestMain_authTestCases___closed__10;
static lean_object* l_Compass_TestMain_routerTestCases___closed__25;
static lean_object* l_Compass_TestMain_authTestCases___closed__21;
static lean_object* l_Compass_TestMain_authTestCases___closed__30;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__8;
static lean_object* l_Compass_TestMain_authTestCases___closed__27;
static lean_object* l_Compass_TestMain_authTestCases___closed__13;
static lean_object* l_Compass_TestMain_routerTestCases___closed__3;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__0;
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__1;
static lean_object* l_Compass_TestMain_authTestCases___closed__28;
static lean_object* l_Compass_TestMain_routerTestCases___closed__1;
static lean_object* l_Compass_TestMain_authTestCases___closed__6;
static lean_object* l_Compass_TestMain_routerTestCases___closed__47;
static lean_object* l_Compass_TestMain_authTestCases___closed__22;
lean_object* l_List_foldl___at___00Mathlib_Linter_EmptyLine_emptyLineLinter_spec__30(lean_object*, lean_object*);
static lean_object* l_Compass_TestMain_budgetTestCases___closed__2;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__11;
static lean_object* l_Compass_TestMain_routerTestCases___closed__13;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__19;
static lean_object* l_Compass_TestMain_authTestCases___closed__18;
static lean_object* l_Compass_TestMain_budgetTestCases___closed__9;
static lean_object* l_Compass_TestMain_routerTestCases___closed__36;
static lean_object* l_Compass_TestMain_routerTestCases___closed__28;
static lean_object* l_Compass_TestMain_rateLimitTestCases___closed__0;
static lean_object* l_Compass_TestMain_main___closed__1;
static lean_object* l_Compass_TestMain_authTestCases___closed__20;
static lean_object* l_Compass_TestMain_routerTestCases___closed__41;
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- Session MFA requirement", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@given(st.builds(Session, mfa_verified=st.booleans()))", 54, 54);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def test_session_mfa_requirement(s):", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    assume(s.mfa_verified == True)", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    assert s.isValid", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- API key prefix validation", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@given(st.text(min_size=8, max_size=8))", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def test_apikey_prefix_validation(prefix):", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    key = APIKey(key_prefix=prefix, ...)", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    if key.prefixValid:", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("        assert key.key_prefix.startswith('flk_')", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- User invariants", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@given(st.builds(User))", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def test_user_invariants(u):", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    assert len(u.email) > 0 and '@' in u['email']", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    assert len(u.id) > 0", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_TestMain_authTestCases___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__17;
x_2 = l_Compass_TestMain_authTestCases___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__18;
x_2 = l_Compass_TestMain_authTestCases___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__19;
x_2 = l_Compass_TestMain_authTestCases___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__20;
x_2 = l_Compass_TestMain_authTestCases___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__21;
x_2 = l_Compass_TestMain_authTestCases___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__22;
x_2 = l_Compass_TestMain_authTestCases___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__23;
x_2 = l_Compass_TestMain_authTestCases___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__24;
x_2 = l_Compass_TestMain_authTestCases___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__25;
x_2 = l_Compass_TestMain_authTestCases___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__26;
x_2 = l_Compass_TestMain_authTestCases___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__27;
x_2 = l_Compass_TestMain_authTestCases___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__28;
x_2 = l_Compass_TestMain_authTestCases___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__29;
x_2 = l_Compass_TestMain_authTestCases___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__30;
x_2 = l_Compass_TestMain_authTestCases___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__31;
x_2 = l_Compass_TestMain_authTestCases___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__32;
x_2 = l_Compass_TestMain_authTestCases___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_authTestCases___closed__33;
x_2 = l_Compass_TestMain_authTestCases___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_authTestCases() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_TestMain_authTestCases___closed__34;
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- API key scope restriction", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@given(st.lists(st.sampled_from(Operation), min_size=1), st.sampled_from(Operation))", 84, 84);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def test_scope_restriction(allowed_ops, op):", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    scope = Scope(allowedOps=allowed_ops)", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    if op in allowed_ops:", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("        assert restricts(scope, op)", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- Circuit breaker state", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@given(st.sampled_from(['closed', 'open', 'half_open']))", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def test_circuit_breaker_state(state):", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    cb = CircuitBreaker(state=state, ...)", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    if state == 'closed':", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("        assert cb.allowsRequest == True", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    elif state == 'open':", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("        assert cb.allowsRequest == False", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- Privilege escalation prevention", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@given(st.lists(st.sampled_from(Operation)), st.lists(st.sampled_from(Operation)))", 82, 82);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def test_privilege_escalation(base_ops, derived_ops):", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    assume(set(derived_ops).issubset(set(base_ops)))", 52, 52);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    base = Scope(allowedOps=base_ops)", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    derived = Scope(allowedOps=derived_ops)", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    for op in Operation:", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("        if not restricts(base, op):", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("            assert not restricts(derived, op)", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_TestMain_routerTestCases___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__23;
x_2 = l_Compass_TestMain_routerTestCases___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__24;
x_2 = l_Compass_TestMain_routerTestCases___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__25;
x_2 = l_Compass_TestMain_routerTestCases___closed__19;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__26;
x_2 = l_Compass_TestMain_routerTestCases___closed__18;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__27;
x_2 = l_Compass_TestMain_routerTestCases___closed__17;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__28;
x_2 = l_Compass_TestMain_routerTestCases___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__29;
x_2 = l_Compass_TestMain_routerTestCases___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__30;
x_2 = l_Compass_TestMain_routerTestCases___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__31;
x_2 = l_Compass_TestMain_authTestCases___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__32;
x_2 = l_Compass_TestMain_routerTestCases___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__33;
x_2 = l_Compass_TestMain_routerTestCases___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__34;
x_2 = l_Compass_TestMain_routerTestCases___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__35;
x_2 = l_Compass_TestMain_routerTestCases___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__36;
x_2 = l_Compass_TestMain_routerTestCases___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__37;
x_2 = l_Compass_TestMain_routerTestCases___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__38;
x_2 = l_Compass_TestMain_routerTestCases___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__39;
x_2 = l_Compass_TestMain_routerTestCases___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__40;
x_2 = l_Compass_TestMain_authTestCases___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__42() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__41;
x_2 = l_Compass_TestMain_routerTestCases___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__42;
x_2 = l_Compass_TestMain_routerTestCases___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__44() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__43;
x_2 = l_Compass_TestMain_routerTestCases___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__44;
x_2 = l_Compass_TestMain_routerTestCases___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__45;
x_2 = l_Compass_TestMain_routerTestCases___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_routerTestCases___closed__46;
x_2 = l_Compass_TestMain_routerTestCases___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_routerTestCases() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_TestMain_routerTestCases___closed__47;
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- Budget refill monotonicity", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@given(st.builds(BudgetState), st.integers(min_value=0, max_value=100))", 71, 71);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def test_budget_refill_monotonic(bs, amt):", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    refilled = refill(bs, amt)", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    assert refilled.current >= bs.current", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    assert refilled.current <= refilled.max", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- Budget consumption atomicity", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@given(st.builds(BudgetState), st.integers(min_value=0, max_value=50))", 70, 70);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def test_budget_consumption_atomic(bs, amt):", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    result = consume(bs, amt)", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    if bs.current >= amt:", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("        assert result is not None", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("        assert result.current == bs.current - amt", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    else:", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("        assert result is None", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_TestMain_budgetTestCases___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__15;
x_2 = l_Compass_TestMain_budgetTestCases___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__16;
x_2 = l_Compass_TestMain_budgetTestCases___closed__12;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__17;
x_2 = l_Compass_TestMain_budgetTestCases___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__18;
x_2 = l_Compass_TestMain_budgetTestCases___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__19;
x_2 = l_Compass_TestMain_budgetTestCases___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__20;
x_2 = l_Compass_TestMain_budgetTestCases___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__21;
x_2 = l_Compass_TestMain_budgetTestCases___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__22;
x_2 = l_Compass_TestMain_budgetTestCases___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__23;
x_2 = l_Compass_TestMain_authTestCases___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__24;
x_2 = l_Compass_TestMain_budgetTestCases___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__25;
x_2 = l_Compass_TestMain_budgetTestCases___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__26;
x_2 = l_Compass_TestMain_budgetTestCases___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__27;
x_2 = l_Compass_TestMain_budgetTestCases___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__28;
x_2 = l_Compass_TestMain_budgetTestCases___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__29;
x_2 = l_Compass_TestMain_budgetTestCases___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_budgetTestCases() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__30;
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- Token bucket capacity bounds", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@given(st.builds(Bucket))", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def test_bucket_bounds(bucket):", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    assert 0 <= bucket.current <= bucket.capacity", 49, 49);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- Bucket consumption", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@given(st.builds(Bucket), st.integers(min_value=1, max_value=10))", 65, 65);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def test_bucket_consume(bucket, amt):", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    result = tryConsume(bucket, amt)", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("    if bucket.current >= amt:", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("        assert result.current == bucket.current - amt", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_budgetTestCases___closed__16;
x_2 = l_Compass_TestMain_rateLimitTestCases___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__10;
x_2 = l_Compass_TestMain_budgetTestCases___closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__11;
x_2 = l_Compass_TestMain_rateLimitTestCases___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__12;
x_2 = l_Compass_TestMain_rateLimitTestCases___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__13;
x_2 = l_Compass_TestMain_rateLimitTestCases___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__14;
x_2 = l_Compass_TestMain_rateLimitTestCases___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__15;
x_2 = l_Compass_TestMain_rateLimitTestCases___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__16;
x_2 = l_Compass_TestMain_authTestCases___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__17;
x_2 = l_Compass_TestMain_rateLimitTestCases___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__18;
x_2 = l_Compass_TestMain_rateLimitTestCases___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__19;
x_2 = l_Compass_TestMain_rateLimitTestCases___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__20;
x_2 = l_Compass_TestMain_rateLimitTestCases___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_TestMain_rateLimitTestCases() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_TestMain_rateLimitTestCases___closed__21;
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0___closed__0;
x_8 = lean_string_append(x_5, x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0___closed__0;
x_13 = lean_string_append(x_10, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l_Compass_TestMain_generatePythonTests___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("# Generated by Lean4 - DO NOT EDIT MANUALLY\nimport hypothesis\nfrom hypothesis import strategies as st, given, assume\nimport pytest\n\n# Import generated COMPASS types\nfrom compass_types import *\n\n# Authentication Tests\n", 217, 217);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_generatePythonTests___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("# Router Security Tests\n", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_generatePythonTests___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("# Budget Control Tests\n", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_generatePythonTests___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("# Rate Limiting Tests\n", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_generatePythonTests() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_1 = l_Compass_TestMain_authTestCases;
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0(x_1, x_2);
x_4 = l_Compass_TestMain_authTestCases___closed__5;
x_5 = l_List_foldl___at___00Mathlib_Linter_EmptyLine_emptyLineLinter_spec__30(x_4, x_3);
lean_dec(x_3);
x_6 = l_Compass_TestMain_routerTestCases;
x_7 = l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0(x_6, x_2);
x_8 = l_List_foldl___at___00Mathlib_Linter_EmptyLine_emptyLineLinter_spec__30(x_4, x_7);
lean_dec(x_7);
x_9 = l_Compass_TestMain_budgetTestCases;
x_10 = l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0(x_9, x_2);
x_11 = l_List_foldl___at___00Mathlib_Linter_EmptyLine_emptyLineLinter_spec__30(x_4, x_10);
lean_dec(x_10);
x_12 = l_Compass_TestMain_rateLimitTestCases;
x_13 = l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0(x_12, x_2);
x_14 = l_List_foldl___at___00Mathlib_Linter_EmptyLine_emptyLineLinter_spec__30(x_4, x_13);
lean_dec(x_13);
x_15 = l_Compass_TestMain_generatePythonTests___closed__0;
x_16 = lean_string_append(x_15, x_5);
lean_dec_ref(x_5);
x_17 = l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0___closed__0;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_Compass_TestMain_generatePythonTests___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_20, x_8);
lean_dec_ref(x_8);
x_22 = lean_string_append(x_21, x_17);
x_23 = l_Compass_TestMain_generatePythonTests___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_11);
lean_dec_ref(x_11);
x_26 = lean_string_append(x_25, x_17);
x_27 = l_Compass_TestMain_generatePythonTests___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = lean_string_append(x_28, x_14);
lean_dec_ref(x_14);
return x_29;
}
}
static lean_object* _init_l_Compass_TestMain_main___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tests/generated_security_tests.py", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Generated security test suite", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Compass_TestMain_main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Python tests: tests/generated_security_tests.py", 47, 47);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Compass_TestMain_main() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Compass_TestMain_generatePythonTests;
x_3 = l_Compass_TestMain_main___closed__0;
x_4 = l_IO_FS_writeFile(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_4);
x_5 = l_Compass_TestMain_main___closed__1;
x_6 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec_ref(x_6);
x_7 = l_Compass_TestMain_main___closed__2;
x_8 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_7);
return x_8;
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Compass_TestMain_main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_TestMain_main();
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Compass_Core(uint8_t builtin);
lean_object* initialize_Compass_Auth(uint8_t builtin);
lean_object* initialize_Compass_Router(uint8_t builtin);
lean_object* initialize_Compass_Budget(uint8_t builtin);
lean_object* initialize_Compass_BudgetState(uint8_t builtin);
lean_object* initialize_Compass_RateLimiter(uint8_t builtin);
lean_object* initialize_Compass_Flags(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Compass_TestMain(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Auth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Router(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Budget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_BudgetState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_RateLimiter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Flags(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Compass_TestMain_authTestCases___closed__0 = _init_l_Compass_TestMain_authTestCases___closed__0();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__0);
l_Compass_TestMain_authTestCases___closed__1 = _init_l_Compass_TestMain_authTestCases___closed__1();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__1);
l_Compass_TestMain_authTestCases___closed__2 = _init_l_Compass_TestMain_authTestCases___closed__2();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__2);
l_Compass_TestMain_authTestCases___closed__3 = _init_l_Compass_TestMain_authTestCases___closed__3();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__3);
l_Compass_TestMain_authTestCases___closed__4 = _init_l_Compass_TestMain_authTestCases___closed__4();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__4);
l_Compass_TestMain_authTestCases___closed__5 = _init_l_Compass_TestMain_authTestCases___closed__5();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__5);
l_Compass_TestMain_authTestCases___closed__6 = _init_l_Compass_TestMain_authTestCases___closed__6();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__6);
l_Compass_TestMain_authTestCases___closed__7 = _init_l_Compass_TestMain_authTestCases___closed__7();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__7);
l_Compass_TestMain_authTestCases___closed__8 = _init_l_Compass_TestMain_authTestCases___closed__8();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__8);
l_Compass_TestMain_authTestCases___closed__9 = _init_l_Compass_TestMain_authTestCases___closed__9();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__9);
l_Compass_TestMain_authTestCases___closed__10 = _init_l_Compass_TestMain_authTestCases___closed__10();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__10);
l_Compass_TestMain_authTestCases___closed__11 = _init_l_Compass_TestMain_authTestCases___closed__11();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__11);
l_Compass_TestMain_authTestCases___closed__12 = _init_l_Compass_TestMain_authTestCases___closed__12();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__12);
l_Compass_TestMain_authTestCases___closed__13 = _init_l_Compass_TestMain_authTestCases___closed__13();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__13);
l_Compass_TestMain_authTestCases___closed__14 = _init_l_Compass_TestMain_authTestCases___closed__14();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__14);
l_Compass_TestMain_authTestCases___closed__15 = _init_l_Compass_TestMain_authTestCases___closed__15();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__15);
l_Compass_TestMain_authTestCases___closed__16 = _init_l_Compass_TestMain_authTestCases___closed__16();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__16);
l_Compass_TestMain_authTestCases___closed__17 = _init_l_Compass_TestMain_authTestCases___closed__17();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__17);
l_Compass_TestMain_authTestCases___closed__18 = _init_l_Compass_TestMain_authTestCases___closed__18();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__18);
l_Compass_TestMain_authTestCases___closed__19 = _init_l_Compass_TestMain_authTestCases___closed__19();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__19);
l_Compass_TestMain_authTestCases___closed__20 = _init_l_Compass_TestMain_authTestCases___closed__20();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__20);
l_Compass_TestMain_authTestCases___closed__21 = _init_l_Compass_TestMain_authTestCases___closed__21();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__21);
l_Compass_TestMain_authTestCases___closed__22 = _init_l_Compass_TestMain_authTestCases___closed__22();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__22);
l_Compass_TestMain_authTestCases___closed__23 = _init_l_Compass_TestMain_authTestCases___closed__23();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__23);
l_Compass_TestMain_authTestCases___closed__24 = _init_l_Compass_TestMain_authTestCases___closed__24();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__24);
l_Compass_TestMain_authTestCases___closed__25 = _init_l_Compass_TestMain_authTestCases___closed__25();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__25);
l_Compass_TestMain_authTestCases___closed__26 = _init_l_Compass_TestMain_authTestCases___closed__26();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__26);
l_Compass_TestMain_authTestCases___closed__27 = _init_l_Compass_TestMain_authTestCases___closed__27();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__27);
l_Compass_TestMain_authTestCases___closed__28 = _init_l_Compass_TestMain_authTestCases___closed__28();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__28);
l_Compass_TestMain_authTestCases___closed__29 = _init_l_Compass_TestMain_authTestCases___closed__29();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__29);
l_Compass_TestMain_authTestCases___closed__30 = _init_l_Compass_TestMain_authTestCases___closed__30();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__30);
l_Compass_TestMain_authTestCases___closed__31 = _init_l_Compass_TestMain_authTestCases___closed__31();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__31);
l_Compass_TestMain_authTestCases___closed__32 = _init_l_Compass_TestMain_authTestCases___closed__32();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__32);
l_Compass_TestMain_authTestCases___closed__33 = _init_l_Compass_TestMain_authTestCases___closed__33();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__33);
l_Compass_TestMain_authTestCases___closed__34 = _init_l_Compass_TestMain_authTestCases___closed__34();
lean_mark_persistent(l_Compass_TestMain_authTestCases___closed__34);
l_Compass_TestMain_authTestCases = _init_l_Compass_TestMain_authTestCases();
lean_mark_persistent(l_Compass_TestMain_authTestCases);
l_Compass_TestMain_routerTestCases___closed__0 = _init_l_Compass_TestMain_routerTestCases___closed__0();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__0);
l_Compass_TestMain_routerTestCases___closed__1 = _init_l_Compass_TestMain_routerTestCases___closed__1();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__1);
l_Compass_TestMain_routerTestCases___closed__2 = _init_l_Compass_TestMain_routerTestCases___closed__2();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__2);
l_Compass_TestMain_routerTestCases___closed__3 = _init_l_Compass_TestMain_routerTestCases___closed__3();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__3);
l_Compass_TestMain_routerTestCases___closed__4 = _init_l_Compass_TestMain_routerTestCases___closed__4();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__4);
l_Compass_TestMain_routerTestCases___closed__5 = _init_l_Compass_TestMain_routerTestCases___closed__5();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__5);
l_Compass_TestMain_routerTestCases___closed__6 = _init_l_Compass_TestMain_routerTestCases___closed__6();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__6);
l_Compass_TestMain_routerTestCases___closed__7 = _init_l_Compass_TestMain_routerTestCases___closed__7();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__7);
l_Compass_TestMain_routerTestCases___closed__8 = _init_l_Compass_TestMain_routerTestCases___closed__8();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__8);
l_Compass_TestMain_routerTestCases___closed__9 = _init_l_Compass_TestMain_routerTestCases___closed__9();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__9);
l_Compass_TestMain_routerTestCases___closed__10 = _init_l_Compass_TestMain_routerTestCases___closed__10();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__10);
l_Compass_TestMain_routerTestCases___closed__11 = _init_l_Compass_TestMain_routerTestCases___closed__11();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__11);
l_Compass_TestMain_routerTestCases___closed__12 = _init_l_Compass_TestMain_routerTestCases___closed__12();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__12);
l_Compass_TestMain_routerTestCases___closed__13 = _init_l_Compass_TestMain_routerTestCases___closed__13();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__13);
l_Compass_TestMain_routerTestCases___closed__14 = _init_l_Compass_TestMain_routerTestCases___closed__14();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__14);
l_Compass_TestMain_routerTestCases___closed__15 = _init_l_Compass_TestMain_routerTestCases___closed__15();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__15);
l_Compass_TestMain_routerTestCases___closed__16 = _init_l_Compass_TestMain_routerTestCases___closed__16();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__16);
l_Compass_TestMain_routerTestCases___closed__17 = _init_l_Compass_TestMain_routerTestCases___closed__17();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__17);
l_Compass_TestMain_routerTestCases___closed__18 = _init_l_Compass_TestMain_routerTestCases___closed__18();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__18);
l_Compass_TestMain_routerTestCases___closed__19 = _init_l_Compass_TestMain_routerTestCases___closed__19();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__19);
l_Compass_TestMain_routerTestCases___closed__20 = _init_l_Compass_TestMain_routerTestCases___closed__20();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__20);
l_Compass_TestMain_routerTestCases___closed__21 = _init_l_Compass_TestMain_routerTestCases___closed__21();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__21);
l_Compass_TestMain_routerTestCases___closed__22 = _init_l_Compass_TestMain_routerTestCases___closed__22();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__22);
l_Compass_TestMain_routerTestCases___closed__23 = _init_l_Compass_TestMain_routerTestCases___closed__23();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__23);
l_Compass_TestMain_routerTestCases___closed__24 = _init_l_Compass_TestMain_routerTestCases___closed__24();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__24);
l_Compass_TestMain_routerTestCases___closed__25 = _init_l_Compass_TestMain_routerTestCases___closed__25();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__25);
l_Compass_TestMain_routerTestCases___closed__26 = _init_l_Compass_TestMain_routerTestCases___closed__26();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__26);
l_Compass_TestMain_routerTestCases___closed__27 = _init_l_Compass_TestMain_routerTestCases___closed__27();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__27);
l_Compass_TestMain_routerTestCases___closed__28 = _init_l_Compass_TestMain_routerTestCases___closed__28();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__28);
l_Compass_TestMain_routerTestCases___closed__29 = _init_l_Compass_TestMain_routerTestCases___closed__29();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__29);
l_Compass_TestMain_routerTestCases___closed__30 = _init_l_Compass_TestMain_routerTestCases___closed__30();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__30);
l_Compass_TestMain_routerTestCases___closed__31 = _init_l_Compass_TestMain_routerTestCases___closed__31();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__31);
l_Compass_TestMain_routerTestCases___closed__32 = _init_l_Compass_TestMain_routerTestCases___closed__32();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__32);
l_Compass_TestMain_routerTestCases___closed__33 = _init_l_Compass_TestMain_routerTestCases___closed__33();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__33);
l_Compass_TestMain_routerTestCases___closed__34 = _init_l_Compass_TestMain_routerTestCases___closed__34();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__34);
l_Compass_TestMain_routerTestCases___closed__35 = _init_l_Compass_TestMain_routerTestCases___closed__35();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__35);
l_Compass_TestMain_routerTestCases___closed__36 = _init_l_Compass_TestMain_routerTestCases___closed__36();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__36);
l_Compass_TestMain_routerTestCases___closed__37 = _init_l_Compass_TestMain_routerTestCases___closed__37();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__37);
l_Compass_TestMain_routerTestCases___closed__38 = _init_l_Compass_TestMain_routerTestCases___closed__38();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__38);
l_Compass_TestMain_routerTestCases___closed__39 = _init_l_Compass_TestMain_routerTestCases___closed__39();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__39);
l_Compass_TestMain_routerTestCases___closed__40 = _init_l_Compass_TestMain_routerTestCases___closed__40();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__40);
l_Compass_TestMain_routerTestCases___closed__41 = _init_l_Compass_TestMain_routerTestCases___closed__41();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__41);
l_Compass_TestMain_routerTestCases___closed__42 = _init_l_Compass_TestMain_routerTestCases___closed__42();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__42);
l_Compass_TestMain_routerTestCases___closed__43 = _init_l_Compass_TestMain_routerTestCases___closed__43();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__43);
l_Compass_TestMain_routerTestCases___closed__44 = _init_l_Compass_TestMain_routerTestCases___closed__44();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__44);
l_Compass_TestMain_routerTestCases___closed__45 = _init_l_Compass_TestMain_routerTestCases___closed__45();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__45);
l_Compass_TestMain_routerTestCases___closed__46 = _init_l_Compass_TestMain_routerTestCases___closed__46();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__46);
l_Compass_TestMain_routerTestCases___closed__47 = _init_l_Compass_TestMain_routerTestCases___closed__47();
lean_mark_persistent(l_Compass_TestMain_routerTestCases___closed__47);
l_Compass_TestMain_routerTestCases = _init_l_Compass_TestMain_routerTestCases();
lean_mark_persistent(l_Compass_TestMain_routerTestCases);
l_Compass_TestMain_budgetTestCases___closed__0 = _init_l_Compass_TestMain_budgetTestCases___closed__0();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__0);
l_Compass_TestMain_budgetTestCases___closed__1 = _init_l_Compass_TestMain_budgetTestCases___closed__1();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__1);
l_Compass_TestMain_budgetTestCases___closed__2 = _init_l_Compass_TestMain_budgetTestCases___closed__2();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__2);
l_Compass_TestMain_budgetTestCases___closed__3 = _init_l_Compass_TestMain_budgetTestCases___closed__3();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__3);
l_Compass_TestMain_budgetTestCases___closed__4 = _init_l_Compass_TestMain_budgetTestCases___closed__4();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__4);
l_Compass_TestMain_budgetTestCases___closed__5 = _init_l_Compass_TestMain_budgetTestCases___closed__5();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__5);
l_Compass_TestMain_budgetTestCases___closed__6 = _init_l_Compass_TestMain_budgetTestCases___closed__6();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__6);
l_Compass_TestMain_budgetTestCases___closed__7 = _init_l_Compass_TestMain_budgetTestCases___closed__7();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__7);
l_Compass_TestMain_budgetTestCases___closed__8 = _init_l_Compass_TestMain_budgetTestCases___closed__8();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__8);
l_Compass_TestMain_budgetTestCases___closed__9 = _init_l_Compass_TestMain_budgetTestCases___closed__9();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__9);
l_Compass_TestMain_budgetTestCases___closed__10 = _init_l_Compass_TestMain_budgetTestCases___closed__10();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__10);
l_Compass_TestMain_budgetTestCases___closed__11 = _init_l_Compass_TestMain_budgetTestCases___closed__11();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__11);
l_Compass_TestMain_budgetTestCases___closed__12 = _init_l_Compass_TestMain_budgetTestCases___closed__12();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__12);
l_Compass_TestMain_budgetTestCases___closed__13 = _init_l_Compass_TestMain_budgetTestCases___closed__13();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__13);
l_Compass_TestMain_budgetTestCases___closed__14 = _init_l_Compass_TestMain_budgetTestCases___closed__14();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__14);
l_Compass_TestMain_budgetTestCases___closed__15 = _init_l_Compass_TestMain_budgetTestCases___closed__15();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__15);
l_Compass_TestMain_budgetTestCases___closed__16 = _init_l_Compass_TestMain_budgetTestCases___closed__16();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__16);
l_Compass_TestMain_budgetTestCases___closed__17 = _init_l_Compass_TestMain_budgetTestCases___closed__17();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__17);
l_Compass_TestMain_budgetTestCases___closed__18 = _init_l_Compass_TestMain_budgetTestCases___closed__18();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__18);
l_Compass_TestMain_budgetTestCases___closed__19 = _init_l_Compass_TestMain_budgetTestCases___closed__19();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__19);
l_Compass_TestMain_budgetTestCases___closed__20 = _init_l_Compass_TestMain_budgetTestCases___closed__20();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__20);
l_Compass_TestMain_budgetTestCases___closed__21 = _init_l_Compass_TestMain_budgetTestCases___closed__21();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__21);
l_Compass_TestMain_budgetTestCases___closed__22 = _init_l_Compass_TestMain_budgetTestCases___closed__22();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__22);
l_Compass_TestMain_budgetTestCases___closed__23 = _init_l_Compass_TestMain_budgetTestCases___closed__23();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__23);
l_Compass_TestMain_budgetTestCases___closed__24 = _init_l_Compass_TestMain_budgetTestCases___closed__24();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__24);
l_Compass_TestMain_budgetTestCases___closed__25 = _init_l_Compass_TestMain_budgetTestCases___closed__25();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__25);
l_Compass_TestMain_budgetTestCases___closed__26 = _init_l_Compass_TestMain_budgetTestCases___closed__26();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__26);
l_Compass_TestMain_budgetTestCases___closed__27 = _init_l_Compass_TestMain_budgetTestCases___closed__27();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__27);
l_Compass_TestMain_budgetTestCases___closed__28 = _init_l_Compass_TestMain_budgetTestCases___closed__28();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__28);
l_Compass_TestMain_budgetTestCases___closed__29 = _init_l_Compass_TestMain_budgetTestCases___closed__29();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__29);
l_Compass_TestMain_budgetTestCases___closed__30 = _init_l_Compass_TestMain_budgetTestCases___closed__30();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases___closed__30);
l_Compass_TestMain_budgetTestCases = _init_l_Compass_TestMain_budgetTestCases();
lean_mark_persistent(l_Compass_TestMain_budgetTestCases);
l_Compass_TestMain_rateLimitTestCases___closed__0 = _init_l_Compass_TestMain_rateLimitTestCases___closed__0();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__0);
l_Compass_TestMain_rateLimitTestCases___closed__1 = _init_l_Compass_TestMain_rateLimitTestCases___closed__1();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__1);
l_Compass_TestMain_rateLimitTestCases___closed__2 = _init_l_Compass_TestMain_rateLimitTestCases___closed__2();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__2);
l_Compass_TestMain_rateLimitTestCases___closed__3 = _init_l_Compass_TestMain_rateLimitTestCases___closed__3();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__3);
l_Compass_TestMain_rateLimitTestCases___closed__4 = _init_l_Compass_TestMain_rateLimitTestCases___closed__4();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__4);
l_Compass_TestMain_rateLimitTestCases___closed__5 = _init_l_Compass_TestMain_rateLimitTestCases___closed__5();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__5);
l_Compass_TestMain_rateLimitTestCases___closed__6 = _init_l_Compass_TestMain_rateLimitTestCases___closed__6();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__6);
l_Compass_TestMain_rateLimitTestCases___closed__7 = _init_l_Compass_TestMain_rateLimitTestCases___closed__7();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__7);
l_Compass_TestMain_rateLimitTestCases___closed__8 = _init_l_Compass_TestMain_rateLimitTestCases___closed__8();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__8);
l_Compass_TestMain_rateLimitTestCases___closed__9 = _init_l_Compass_TestMain_rateLimitTestCases___closed__9();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__9);
l_Compass_TestMain_rateLimitTestCases___closed__10 = _init_l_Compass_TestMain_rateLimitTestCases___closed__10();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__10);
l_Compass_TestMain_rateLimitTestCases___closed__11 = _init_l_Compass_TestMain_rateLimitTestCases___closed__11();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__11);
l_Compass_TestMain_rateLimitTestCases___closed__12 = _init_l_Compass_TestMain_rateLimitTestCases___closed__12();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__12);
l_Compass_TestMain_rateLimitTestCases___closed__13 = _init_l_Compass_TestMain_rateLimitTestCases___closed__13();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__13);
l_Compass_TestMain_rateLimitTestCases___closed__14 = _init_l_Compass_TestMain_rateLimitTestCases___closed__14();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__14);
l_Compass_TestMain_rateLimitTestCases___closed__15 = _init_l_Compass_TestMain_rateLimitTestCases___closed__15();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__15);
l_Compass_TestMain_rateLimitTestCases___closed__16 = _init_l_Compass_TestMain_rateLimitTestCases___closed__16();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__16);
l_Compass_TestMain_rateLimitTestCases___closed__17 = _init_l_Compass_TestMain_rateLimitTestCases___closed__17();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__17);
l_Compass_TestMain_rateLimitTestCases___closed__18 = _init_l_Compass_TestMain_rateLimitTestCases___closed__18();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__18);
l_Compass_TestMain_rateLimitTestCases___closed__19 = _init_l_Compass_TestMain_rateLimitTestCases___closed__19();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__19);
l_Compass_TestMain_rateLimitTestCases___closed__20 = _init_l_Compass_TestMain_rateLimitTestCases___closed__20();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__20);
l_Compass_TestMain_rateLimitTestCases___closed__21 = _init_l_Compass_TestMain_rateLimitTestCases___closed__21();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases___closed__21);
l_Compass_TestMain_rateLimitTestCases = _init_l_Compass_TestMain_rateLimitTestCases();
lean_mark_persistent(l_Compass_TestMain_rateLimitTestCases);
l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0___closed__0 = _init_l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0___closed__0();
lean_mark_persistent(l_List_mapTR_loop___at___00Compass_TestMain_generatePythonTests_spec__0___closed__0);
l_Compass_TestMain_generatePythonTests___closed__0 = _init_l_Compass_TestMain_generatePythonTests___closed__0();
lean_mark_persistent(l_Compass_TestMain_generatePythonTests___closed__0);
l_Compass_TestMain_generatePythonTests___closed__1 = _init_l_Compass_TestMain_generatePythonTests___closed__1();
lean_mark_persistent(l_Compass_TestMain_generatePythonTests___closed__1);
l_Compass_TestMain_generatePythonTests___closed__2 = _init_l_Compass_TestMain_generatePythonTests___closed__2();
lean_mark_persistent(l_Compass_TestMain_generatePythonTests___closed__2);
l_Compass_TestMain_generatePythonTests___closed__3 = _init_l_Compass_TestMain_generatePythonTests___closed__3();
lean_mark_persistent(l_Compass_TestMain_generatePythonTests___closed__3);
l_Compass_TestMain_generatePythonTests = _init_l_Compass_TestMain_generatePythonTests();
lean_mark_persistent(l_Compass_TestMain_generatePythonTests);
l_Compass_TestMain_main___closed__0 = _init_l_Compass_TestMain_main___closed__0();
lean_mark_persistent(l_Compass_TestMain_main___closed__0);
l_Compass_TestMain_main___closed__1 = _init_l_Compass_TestMain_main___closed__1();
lean_mark_persistent(l_Compass_TestMain_main___closed__1);
l_Compass_TestMain_main___closed__2 = _init_l_Compass_TestMain_main___closed__2();
lean_mark_persistent(l_Compass_TestMain_main___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
