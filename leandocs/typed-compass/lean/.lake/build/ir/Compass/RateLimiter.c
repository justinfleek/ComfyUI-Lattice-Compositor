// Lean compiler output
// Module: Compass.RateLimiter
// Imports: public import Init public import Compass.Core public import Compass.Auth public import Compass.Tools public import Mathlib.Tactic.SplitIfs
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
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_ctorIdx(lean_object*);
static lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr___closed__7;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
static lean_object* l_Compass_RateLimiter_instExtractableRateLimitStats___closed__2;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__13;
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqBucket(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__17;
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqAcquireResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_fromJson(lean_object*);
static lean_object* l_Compass_RateLimiter_AcquireResult_toJson___closed__4;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__18;
static lean_object* l_Compass_RateLimiter_AcquireResult_toJson___closed__1;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__10;
static lean_object* l_Compass_RateLimiter_instInhabitedBucket___closed__0;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_refill(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instExtractableBucket;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr___closed__6;
static lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr___closed__1;
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_instReprAcquireResult_repr_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprBucket_repr(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqBucket_decEq(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__23;
static lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr___closed__5;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr___boxed(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprAcquireResult___closed__0;
static lean_object* l_Compass_RateLimiter_AcquireResult_toJson___closed__3;
static lean_object* l_Compass_RateLimiter_AcquireResult_toString___closed__1;
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__6;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_isDenied___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__5;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_tryConsume(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_Allowed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_decodeOptInt(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_acquire___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_toString___boxed(lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__24;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprBucket;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_record(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_toJson(lean_object*);
static lean_object* l_Compass_RateLimiter_instExtractableAcquireResult___closed__0;
static lean_object* l_Compass_RateLimiter_AcquireResult_toString___closed__0;
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqAcquireResult_decEq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_ctorIdx___boxed(lean_object*);
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_AcquireResult_toJson___closed__6;
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_instReprAcquireResult_repr_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprRateLimitStats;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_acquire(lean_object*, lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_decodeOptInt___closed__0;
static lean_object* l_Compass_RateLimiter_instExtractableBucket___closed__1;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__3;
static lean_object* l_Compass_RateLimiter_instExtractableBucket___closed__0;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprAcquireResult;
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__9;
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__8;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__22;
static lean_object* l_Compass_RateLimiter_instExtractableAcquireResult___closed__1;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Compass_RateLimiter_AcquireResult_toJson___closed__2;
static lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr___closed__3;
lean_object* l_Compass_Core_Json_asInt(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_toString(lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__9;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_ctorIdx___boxed(lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket___closed__0;
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqBucket___boxed(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqAcquireResult_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg(lean_object*);
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_toJson(lean_object*);
lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instExtractableAcquireResult___closed__2;
static lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr___closed__0;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_toJson(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqRateLimitStats___boxed(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_Denied_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_isAllowed___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_AcquireResult_toJson___closed__7;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_fromJson___boxed(lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__12;
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__4;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__15;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_Allowed_elim___redArg(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_AcquireResult_toJson___closed__0;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_tryConsume___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instExtractableAcquireResult;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_calcRetrySeconds(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Compass_RateLimiter_AcquireResult_isAllowed(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_AcquireResult_toString___closed__2;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqAcquireResult___boxed(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__11;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__8;
lean_object* l_Compass_Core_Json_fieldN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_fresh___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqRateLimitStats(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instExtractableRateLimitStats___closed__1;
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__11;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__21;
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__4;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqBucket_decEq___boxed(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr___closed__2;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__10;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4;
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqRateLimitStats_decEq___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_AcquireResult_toJson___closed__5;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_empty;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__6;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__19;
static lean_object* l_Compass_RateLimiter_Bucket_fresh___closed__0;
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__2;
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats___closed__0;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_fresh(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_RateLimitStats_empty___closed__0;
lean_object* l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___boxed(lean_object*);
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__3;
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_toJson___boxed(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_Denied_elim___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__20;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_fromJson(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_encodeOptInt(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
uint8_t l_Option_instDecidableEq_decEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_ctorElim___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instExtractableBucket___closed__2;
static lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__7;
LEAN_EXPORT uint8_t l_Compass_RateLimiter_AcquireResult_isDenied(lean_object*);
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqRateLimitStats_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instInhabitedBucket;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instExtractableRateLimitStats;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_fromJson___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprBucket_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_record___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__16;
static lean_object* l_Compass_RateLimiter_instExtractableRateLimitStats___closed__0;
LEAN_EXPORT lean_object* l_Compass_RateLimiter_calcRetrySeconds___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_RateLimiter_Bucket_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__2;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tokens", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__7;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refill_rate", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(15u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max_tokens", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(14u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__10;
x_2 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__8;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__20;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("last_update_ms", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__22;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(18u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_21 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__10;
x_70 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__18;
x_71 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__19;
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_96 = lean_int_dec_lt(x_2, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = l_Int_repr(x_2);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_72 = x_98;
goto block_93;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = l_Int_repr(x_2);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = l_Repr_addAppParen(x_100, x_94);
x_72 = x_101;
goto block_93;
}
block_20:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_8);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__3;
x_14 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__4;
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__5;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_8);
return x_19;
}
block_45:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_26);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_23);
x_33 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__12;
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_21);
x_36 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__13;
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_39 = lean_int_dec_lt(x_5, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l_Int_repr(x_5);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_6 = x_35;
x_7 = x_36;
x_8 = x_26;
x_9 = x_41;
goto block_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Int_repr(x_5);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Repr_addAppParen(x_43, x_37);
x_6 = x_35;
x_7 = x_36;
x_8 = x_26;
x_9 = x_44;
goto block_20;
}
}
block_69:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_49);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
lean_inc(x_48);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_48);
lean_inc(x_46);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_46);
x_57 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__16;
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_21);
x_60 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__17;
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_63 = lean_int_dec_lt(x_4, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Int_repr(x_4);
x_65 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_22 = x_60;
x_23 = x_46;
x_24 = x_59;
x_25 = x_48;
x_26 = x_49;
x_27 = x_65;
goto block_45;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = l_Int_repr(x_4);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Repr_addAppParen(x_67, x_61);
x_22 = x_60;
x_23 = x_46;
x_24 = x_59;
x_25 = x_48;
x_26 = x_49;
x_27 = x_68;
goto block_45;
}
}
block_93:
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_73 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = 0;
x_75 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_70);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__21;
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_box(1);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__23;
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_21);
x_84 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__24;
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_87 = lean_int_dec_lt(x_3, x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Int_repr(x_3);
x_89 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_46 = x_79;
x_47 = x_84;
x_48 = x_77;
x_49 = x_74;
x_50 = x_83;
x_51 = x_89;
goto block_69;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = l_Int_repr(x_3);
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = l_Repr_addAppParen(x_91, x_85);
x_46 = x_79;
x_47 = x_84;
x_48 = x_77;
x_49 = x_74;
x_50 = x_83;
x_51 = x_92;
goto block_69;
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprBucket_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_RateLimiter_instReprBucket_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprBucket_repr___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_RateLimiter_instReprBucket_repr___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprBucket_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_RateLimiter_instReprBucket_repr(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_RateLimiter_instReprBucket_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprBucket() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_RateLimiter_instReprBucket___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqBucket_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_int_dec_eq(x_3, x_7);
if (x_11 == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_int_dec_eq(x_4, x_8);
if (x_12 == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_int_dec_eq(x_5, x_9);
if (x_13 == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_int_dec_eq(x_6, x_10);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqBucket_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Compass_RateLimiter_instDecidableEqBucket_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqBucket(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Compass_RateLimiter_instDecidableEqBucket_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqBucket___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Compass_RateLimiter_instDecidableEqBucket(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Compass_RateLimiter_instInhabitedBucket___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instInhabitedBucket() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_RateLimiter_instInhabitedBucket___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__6;
lean_inc(x_2);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__22;
lean_inc(x_3);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__15;
lean_inc(x_4);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__11;
lean_inc(x_5);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_toJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_RateLimiter_Bucket_toJson(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Compass_Core_Json_fieldN(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Compass_Core_Json_asInt(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Compass_Core_Json_fieldN(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_8);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Compass_Core_Json_asInt(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_8);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Compass_Core_Json_fieldN(x_16, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_8);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Compass_Core_Json_asInt(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_8);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Compass_Core_Json_fieldN(x_23, x_1);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_8);
x_25 = lean_box(0);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Compass_Core_Json_asInt(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_8);
x_28 = lean_box(0);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_15);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_15);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_fromJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_RateLimiter_Bucket_fromJson(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableBucket___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_RateLimiter_Bucket_toJson___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableBucket___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_RateLimiter_Bucket_fromJson___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableBucket___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_RateLimiter_instExtractableBucket___closed__1;
x_2 = l_Compass_RateLimiter_instExtractableBucket___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableBucket() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_RateLimiter_instExtractableBucket___closed__2;
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_Bucket_fresh___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1000u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_fresh(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_int_add(x_3, x_5);
x_7 = l_Compass_RateLimiter_Bucket_fresh___closed__0;
x_8 = lean_int_mul(x_6, x_7);
lean_dec(x_6);
x_9 = lean_int_mul(x_3, x_7);
x_10 = lean_int_ediv(x_9, x_4);
lean_dec(x_9);
lean_inc(x_8);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_8);
lean_ctor_set(x_11, 3, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_fresh___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_RateLimiter_Bucket_fresh(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_refill(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_int_sub(x_2, x_4);
x_8 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_9 = lean_int_dec_le(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_1, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
x_15 = lean_int_mul(x_6, x_7);
lean_dec(x_7);
x_16 = l_Compass_RateLimiter_Bucket_fresh___closed__0;
x_17 = lean_int_ediv(x_15, x_16);
lean_dec(x_15);
x_18 = lean_int_add(x_3, x_17);
lean_dec(x_17);
lean_dec(x_3);
x_19 = lean_int_dec_le(x_5, x_18);
if (x_19 == 0)
{
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
else
{
lean_dec(x_18);
lean_inc(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_1);
x_20 = lean_int_mul(x_6, x_7);
lean_dec(x_7);
x_21 = l_Compass_RateLimiter_Bucket_fresh___closed__0;
x_22 = lean_int_ediv(x_20, x_21);
lean_dec(x_20);
x_23 = lean_int_add(x_3, x_22);
lean_dec(x_22);
lean_dec(x_3);
x_24 = lean_int_dec_le(x_5, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set(x_25, 2, x_5);
lean_ctor_set(x_25, 3, x_6);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_23);
lean_inc(x_5);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_5);
lean_ctor_set(x_26, 3, x_6);
return x_26;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_tryConsume(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_4 = lean_int_dec_le(x_2, x_3);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_int_dec_le(x_2, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_1);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_int_sub(x_6, x_2);
lean_dec(x_6);
lean_ctor_set(x_1, 0, x_12);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_18 = lean_int_dec_le(x_2, x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_int_sub(x_14, x_2);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_1);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_Bucket_tryConsume___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_RateLimiter_Bucket_tryConsume(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Compass_RateLimiter_0__Compass_RateLimiter_consume__nonneg_match__1_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_RateLimiter_AcquireResult_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Compass_RateLimiter_AcquireResult_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Compass_RateLimiter_AcquireResult_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_Allowed_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_RateLimiter_AcquireResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_Allowed_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Compass_RateLimiter_AcquireResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_Denied_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_RateLimiter_AcquireResult_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_Denied_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Compass_RateLimiter_AcquireResult_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compass.RateLimiter.AcquireResult.Allowed", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__1;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compass.RateLimiter.AcquireResult.Denied", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(1);
x_2 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__6;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_34; uint8_t x_35; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_22 = x_1;
} else {
 lean_dec_ref(x_1);
 x_22 = lean_box(0);
}
x_34 = lean_unsigned_to_nat(1024u);
x_35 = lean_nat_dec_le(x_34, x_2);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__3;
x_23 = x_36;
goto block_33;
}
else
{
lean_object* x_37; 
x_37 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4;
x_23 = x_37;
goto block_33;
}
block_33:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__2;
x_25 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_26 = lean_int_dec_lt(x_21, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Int_repr(x_21);
lean_dec(x_21);
if (lean_is_scalar(x_22)) {
 x_28 = lean_alloc_ctor(3, 1, 0);
} else {
 x_28 = x_22;
 lean_ctor_set_tag(x_28, 3);
}
lean_ctor_set(x_28, 0, x_27);
x_12 = x_23;
x_13 = x_24;
x_14 = x_28;
goto block_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_unsigned_to_nat(1024u);
x_30 = l_Int_repr(x_21);
lean_dec(x_21);
if (lean_is_scalar(x_22)) {
 x_31 = lean_alloc_ctor(3, 1, 0);
} else {
 x_31 = x_22;
 lean_ctor_set_tag(x_31, 3);
}
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Repr_addAppParen(x_31, x_29);
x_12 = x_23;
x_13 = x_24;
x_14 = x_32;
goto block_20;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_51; uint8_t x_52; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_39 = x_1;
} else {
 lean_dec_ref(x_1);
 x_39 = lean_box(0);
}
x_51 = lean_unsigned_to_nat(1024u);
x_52 = lean_nat_dec_le(x_51, x_2);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__3;
x_40 = x_53;
goto block_50;
}
else
{
lean_object* x_54; 
x_54 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4;
x_40 = x_54;
goto block_50;
}
block_50:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__7;
x_42 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_43 = lean_int_dec_lt(x_38, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Int_repr(x_38);
lean_dec(x_38);
if (lean_is_scalar(x_39)) {
 x_45 = lean_alloc_ctor(3, 1, 0);
} else {
 x_45 = x_39;
 lean_ctor_set_tag(x_45, 3);
}
lean_ctor_set(x_45, 0, x_44);
x_3 = x_40;
x_4 = x_41;
x_5 = x_45;
goto block_11;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_unsigned_to_nat(1024u);
x_47 = l_Int_repr(x_38);
lean_dec(x_38);
if (lean_is_scalar(x_39)) {
 x_48 = lean_alloc_ctor(3, 1, 0);
} else {
 x_48 = x_39;
 lean_ctor_set_tag(x_48, 3);
}
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Repr_addAppParen(x_48, x_46);
x_3 = x_40;
x_4 = x_41;
x_5 = x_49;
goto block_11;
}
}
}
block_11:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l_Repr_addAppParen(x_9, x_2);
return x_10;
}
block_20:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = 0;
x_18 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = l_Repr_addAppParen(x_18, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprAcquireResult_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_RateLimiter_instReprAcquireResult_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprAcquireResult___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_RateLimiter_instReprAcquireResult_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprAcquireResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_RateLimiter_instReprAcquireResult___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqAcquireResult_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_int_dec_eq(x_8, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqAcquireResult_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Compass_RateLimiter_instDecidableEqAcquireResult_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqAcquireResult(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Compass_RateLimiter_instDecidableEqAcquireResult_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqAcquireResult___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Compass_RateLimiter_instDecidableEqAcquireResult(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Compass_RateLimiter_AcquireResult_isAllowed(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_isAllowed___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Compass_RateLimiter_AcquireResult_isAllowed(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Compass_RateLimiter_AcquireResult_isDenied(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_isDenied___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Compass_RateLimiter_AcquireResult_isDenied(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("allowed:", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("denied:", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_toString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Compass_RateLimiter_AcquireResult_toString___closed__0;
x_4 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_5 = lean_int_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_nat_abs(x_2);
x_7 = l_Nat_reprFast(x_6);
x_8 = lean_string_append(x_3, x_7);
lean_dec_ref(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_nat_abs(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = l_Compass_RateLimiter_AcquireResult_toString___closed__1;
x_13 = lean_nat_add(x_11, x_10);
lean_dec(x_11);
x_14 = l_Nat_reprFast(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec_ref(x_14);
x_16 = lean_string_append(x_3, x_15);
lean_dec_ref(x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = l_Compass_RateLimiter_AcquireResult_toString___closed__2;
x_19 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_20 = lean_int_dec_lt(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_nat_abs(x_17);
x_22 = l_Nat_reprFast(x_21);
x_23 = lean_string_append(x_18, x_22);
lean_dec_ref(x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_nat_abs(x_17);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = l_Compass_RateLimiter_AcquireResult_toString___closed__1;
x_28 = lean_nat_add(x_26, x_25);
lean_dec(x_26);
x_29 = l_Nat_reprFast(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec_ref(x_29);
x_31 = lean_string_append(x_18, x_30);
lean_dec_ref(x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_toString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_RateLimiter_AcquireResult_toString(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tag", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("allowed", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_AcquireResult_toJson___closed__1;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_RateLimiter_AcquireResult_toJson___closed__2;
x_2 = l_Compass_RateLimiter_AcquireResult_toJson___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("denied", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_AcquireResult_toJson___closed__5;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_RateLimiter_AcquireResult_toJson___closed__6;
x_2 = l_Compass_RateLimiter_AcquireResult_toJson___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_toJson(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Compass_RateLimiter_AcquireResult_toJson___closed__3;
x_4 = l_Compass_RateLimiter_AcquireResult_toJson___closed__4;
lean_ctor_set_tag(x_1, 2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Compass_RateLimiter_AcquireResult_toJson___closed__3;
x_12 = l_Compass_RateLimiter_AcquireResult_toJson___closed__4;
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = l_Compass_RateLimiter_AcquireResult_toJson___closed__7;
x_21 = l_Compass_RateLimiter_AcquireResult_toJson___closed__4;
lean_ctor_set_tag(x_1, 2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Compass_RateLimiter_AcquireResult_toJson___closed__7;
x_29 = l_Compass_RateLimiter_AcquireResult_toJson___closed__4;
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_AcquireResult_fromJson(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec_ref(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = l_Compass_RateLimiter_AcquireResult_toJson___closed__0;
x_8 = lean_string_dec_eq(x_5, x_7);
lean_dec(x_5);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_4);
x_9 = lean_box(0);
return x_9;
}
else
{
if (lean_obj_tag(x_6) == 4)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = l_Compass_RateLimiter_AcquireResult_toJson___closed__1;
x_13 = lean_string_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Compass_RateLimiter_AcquireResult_toJson___closed__5;
x_15 = lean_string_dec_eq(x_11, x_14);
lean_dec_ref(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_free_object(x_6);
lean_dec(x_4);
x_16 = lean_box(0);
return x_16;
}
else
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_dec_ref(x_4);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Compass_RateLimiter_AcquireResult_toJson___closed__4;
x_22 = lean_string_dec_eq(x_19, x_21);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_18);
lean_free_object(x_6);
x_23 = lean_box(0);
return x_23;
}
else
{
if (lean_obj_tag(x_20) == 2)
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
lean_ctor_set_tag(x_20, 1);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_20);
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_26);
return x_6;
}
}
else
{
lean_object* x_27; 
lean_dec_ref(x_20);
lean_dec(x_18);
lean_free_object(x_6);
x_27 = lean_box(0);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_20);
lean_dec(x_18);
lean_free_object(x_6);
x_28 = lean_box(0);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_free_object(x_6);
lean_dec(x_4);
x_29 = lean_box(0);
return x_29;
}
}
}
else
{
lean_dec_ref(x_11);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_4, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_dec_ref(x_4);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Compass_RateLimiter_AcquireResult_toJson___closed__4;
x_35 = lean_string_dec_eq(x_32, x_34);
lean_dec(x_32);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_31);
lean_free_object(x_6);
x_36 = lean_box(0);
return x_36;
}
else
{
if (lean_obj_tag(x_33) == 2)
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_ctor_set_tag(x_33, 0);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_33);
return x_6;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_39);
return x_6;
}
}
else
{
lean_object* x_40; 
lean_dec_ref(x_33);
lean_dec(x_31);
lean_free_object(x_6);
x_40 = lean_box(0);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec(x_33);
lean_dec(x_31);
lean_free_object(x_6);
x_41 = lean_box(0);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_free_object(x_6);
lean_dec(x_4);
x_42 = lean_box(0);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_6, 0);
lean_inc(x_43);
lean_dec(x_6);
x_44 = l_Compass_RateLimiter_AcquireResult_toJson___closed__1;
x_45 = lean_string_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l_Compass_RateLimiter_AcquireResult_toJson___closed__5;
x_47 = lean_string_dec_eq(x_43, x_46);
lean_dec_ref(x_43);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_4);
x_48 = lean_box(0);
return x_48;
}
else
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_4, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
lean_dec_ref(x_4);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = l_Compass_RateLimiter_AcquireResult_toJson___closed__4;
x_54 = lean_string_dec_eq(x_51, x_53);
lean_dec(x_51);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_50);
x_55 = lean_box(0);
return x_55;
}
else
{
if (lean_obj_tag(x_52) == 2)
{
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_57 = x_52;
} else {
 lean_dec_ref(x_52);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec_ref(x_52);
lean_dec(x_50);
x_60 = lean_box(0);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_52);
lean_dec(x_50);
x_61 = lean_box(0);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_4);
x_62 = lean_box(0);
return x_62;
}
}
}
else
{
lean_dec_ref(x_43);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_4, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_4, 1);
lean_inc(x_64);
lean_dec_ref(x_4);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_dec(x_63);
x_67 = l_Compass_RateLimiter_AcquireResult_toJson___closed__4;
x_68 = lean_string_dec_eq(x_65, x_67);
lean_dec(x_65);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_66);
lean_dec(x_64);
x_69 = lean_box(0);
return x_69;
}
else
{
if (lean_obj_tag(x_66) == 2)
{
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_71 = x_66;
} else {
 lean_dec_ref(x_66);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(0, 1, 0);
} else {
 x_72 = x_71;
 lean_ctor_set_tag(x_72, 0);
}
lean_ctor_set(x_72, 0, x_70);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec_ref(x_66);
lean_dec(x_64);
x_74 = lean_box(0);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_66);
lean_dec(x_64);
x_75 = lean_box(0);
return x_75;
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_4);
x_76 = lean_box(0);
return x_76;
}
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_6);
lean_dec(x_4);
x_77 = lean_box(0);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_2);
x_78 = lean_box(0);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_1);
x_79 = lean_box(0);
return x_79;
}
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableAcquireResult___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_RateLimiter_AcquireResult_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableAcquireResult___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_RateLimiter_AcquireResult_fromJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableAcquireResult___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_RateLimiter_instExtractableAcquireResult___closed__1;
x_2 = l_Compass_RateLimiter_instExtractableAcquireResult___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableAcquireResult() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_RateLimiter_instExtractableAcquireResult___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_encodeOptInt(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_ctor_set_tag(x_1, 2);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
}
static lean_object* _init_l_Compass_RateLimiter_decodeOptInt___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_decodeOptInt(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Compass_RateLimiter_decodeOptInt___closed__0;
return x_2;
}
case 2:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
lean_ctor_set_tag(x_1, 1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
default: 
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_RateLimiter_RateLimitStats_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("total_requests", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__10;
x_2 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("last_denied_ms", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("denied_requests", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("allowed_requests", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(20u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_60; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__10;
x_7 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__3;
x_8 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__24;
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_84 = lean_int_dec_lt(x_2, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = l_Int_repr(x_2);
lean_dec(x_2);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_60 = x_86;
goto block_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = l_Int_repr(x_2);
lean_dec(x_2);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = l_Repr_addAppParen(x_88, x_82);
x_60 = x_89;
goto block_81;
}
block_35:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_11);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
x_20 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__5;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Option_repr___at___00Lean_Omega_instReprConstraint_repr_spec__0(x_5, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_11);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__3;
x_29 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__4;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__5;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_11);
return x_34;
}
block_59:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_38);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_37);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
lean_inc(x_36);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_36);
x_47 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__7;
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_6);
x_50 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__8;
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_53 = lean_int_dec_lt(x_4, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Int_repr(x_4);
lean_dec(x_4);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_9 = x_36;
x_10 = x_37;
x_11 = x_38;
x_12 = x_49;
x_13 = x_50;
x_14 = x_55;
goto block_35;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l_Int_repr(x_4);
lean_dec(x_4);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Repr_addAppParen(x_57, x_51);
x_9 = x_36;
x_10 = x_37;
x_11 = x_38;
x_12 = x_49;
x_13 = x_50;
x_14 = x_58;
goto block_35;
}
}
block_81:
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_8);
lean_ctor_set(x_61, 1, x_60);
x_62 = 0;
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_7);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__21;
x_66 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_box(1);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__10;
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_6);
x_72 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__11;
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_75 = lean_int_dec_lt(x_3, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Int_repr(x_3);
lean_dec(x_3);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_36 = x_67;
x_37 = x_65;
x_38 = x_62;
x_39 = x_72;
x_40 = x_71;
x_41 = x_77;
goto block_59;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = l_Int_repr(x_3);
lean_dec(x_3);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = l_Repr_addAppParen(x_79, x_73);
x_36 = x_67;
x_37 = x_65;
x_38 = x_62;
x_39 = x_72;
x_40 = x_71;
x_41 = x_80;
goto block_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instReprRateLimitStats_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_RateLimiter_instReprRateLimitStats_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_RateLimiter_instReprRateLimitStats_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instReprRateLimitStats() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_RateLimiter_instReprRateLimitStats___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqRateLimitStats_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_dec_ref(x_2);
x_11 = lean_int_dec_eq(x_3, x_7);
lean_dec(x_7);
lean_dec(x_3);
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_int_dec_eq(x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
if (x_12 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_int_dec_eq(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_6);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
x_15 = l_Option_instDecidableEq_decEq___redArg(x_14, x_6, x_10);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqRateLimitStats_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Compass_RateLimiter_instDecidableEqRateLimitStats_decEq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Compass_RateLimiter_instDecidableEqRateLimitStats(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Compass_RateLimiter_instDecidableEqRateLimitStats_decEq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_instDecidableEqRateLimitStats___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Compass_RateLimiter_instDecidableEqRateLimitStats(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__0;
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__9;
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__6;
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__4;
x_16 = l_Compass_RateLimiter_encodeOptInt(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Compass_Core_Json_fieldN(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l_Compass_Core_Json_asInt(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Compass_Core_Json_fieldN(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_8);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Compass_Core_Json_asInt(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_8);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_unsigned_to_nat(2u);
x_17 = l_Compass_Core_Json_fieldN(x_16, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_8);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l_Compass_Core_Json_asInt(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_15);
lean_dec(x_8);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Compass_Core_Json_fieldN(x_23, x_1);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_8);
x_25 = lean_box(0);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Compass_RateLimiter_decodeOptInt(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_15);
lean_dec(x_8);
x_28 = lean_box(0);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_15);
lean_ctor_set(x_31, 2, x_22);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_15);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_fromJson___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_RateLimiter_RateLimitStats_fromJson(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableRateLimitStats___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_RateLimiter_RateLimitStats_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableRateLimitStats___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_RateLimiter_RateLimitStats_fromJson___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableRateLimitStats___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_RateLimiter_instExtractableRateLimitStats___closed__1;
x_2 = l_Compass_RateLimiter_instExtractableRateLimitStats___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_instExtractableRateLimitStats() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_RateLimiter_instExtractableRateLimitStats___closed__2;
return x_1;
}
}
static lean_object* _init_l_Compass_RateLimiter_RateLimitStats_empty___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_RateLimiter_RateLimitStats_empty() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_RateLimiter_RateLimitStats_empty___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_record(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
lean_dec(x_7);
x_8 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4;
x_9 = lean_int_add(x_5, x_8);
lean_dec(x_5);
x_10 = lean_int_add(x_6, x_8);
lean_dec(x_6);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_1, 3, x_11);
lean_ctor_set(x_1, 2, x_10);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_15 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4;
x_16 = lean_int_add(x_12, x_15);
lean_dec(x_12);
x_17 = lean_int_add(x_14, x_15);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_3);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_17);
lean_ctor_set(x_19, 3, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4;
x_24 = lean_int_add(x_21, x_23);
lean_dec(x_21);
x_25 = lean_int_add(x_22, x_23);
lean_dec(x_22);
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_ctor_get(x_1, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_30 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4;
x_31 = lean_int_add(x_26, x_30);
lean_dec(x_26);
x_32 = lean_int_add(x_27, x_30);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_29);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_RateLimitStats_record___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l_Compass_RateLimiter_RateLimitStats_record(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_calcRetrySeconds(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_int_ediv(x_4, x_3);
x_6 = lean_int_mul(x_5, x_2);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_calcRetrySeconds___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_RateLimiter_calcRetrySeconds(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_acquire(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Compass_RateLimiter_Bucket_refill(x_1, x_2);
x_9 = l_Compass_RateLimiter_Bucket_fresh___closed__0;
x_10 = lean_int_mul(x_3, x_9);
lean_inc_ref(x_4);
x_11 = l_Compass_RateLimiter_Bucket_tryConsume(x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 3);
lean_inc(x_13);
x_14 = lean_int_sub(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_15 = lean_int_mul(x_14, x_9);
lean_dec(x_14);
x_16 = lean_int_ediv(x_15, x_13);
lean_dec(x_13);
lean_dec(x_15);
x_17 = l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4;
x_18 = lean_int_ediv(x_16, x_9);
lean_dec(x_16);
x_19 = lean_int_dec_le(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
x_5 = x_17;
goto block_8;
}
else
{
x_5 = x_18;
goto block_8;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec_ref(x_4);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_21, 0);
x_23 = lean_int_ediv(x_22, x_9);
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_int_ediv(x_26, x_9);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Compass_RateLimiter_acquire___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Compass_RateLimiter_acquire(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_instReprAcquireResult_repr_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Compass_RateLimiter_0__Compass_RateLimiter_instReprAcquireResult_repr_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Compass_RateLimiter_0__Compass_RateLimiter_instReprAcquireResult_repr_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Compass_Core(uint8_t builtin);
lean_object* initialize_Compass_Auth(uint8_t builtin);
lean_object* initialize_Compass_Tools(uint8_t builtin);
lean_object* initialize_Mathlib_Tactic_SplitIfs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Compass_RateLimiter(uint8_t builtin) {
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
res = initialize_Compass_Tools(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_SplitIfs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__0 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__0);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__1 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__1();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__1);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__2 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__2();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__2);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__3 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__3();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__3);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__4 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__4();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__4);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__5 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__5();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__5);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__6 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__6();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__6);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__7 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__7();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__7);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__8 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__8();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__8);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__9 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__9();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__9);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__10 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__10();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__10);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__11 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__11();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__11);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__12 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__12();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__12);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__13 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__13();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__13);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__14);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__15 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__15();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__15);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__16 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__16();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__16);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__17 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__17();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__17);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__18 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__18();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__18);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__19 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__19();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__19);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__20 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__20();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__20);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__21 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__21();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__21);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__22 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__22();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__22);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__23 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__23();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__23);
l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__24 = _init_l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__24();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket_repr___redArg___closed__24);
l_Compass_RateLimiter_instReprBucket___closed__0 = _init_l_Compass_RateLimiter_instReprBucket___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket___closed__0);
l_Compass_RateLimiter_instReprBucket = _init_l_Compass_RateLimiter_instReprBucket();
lean_mark_persistent(l_Compass_RateLimiter_instReprBucket);
l_Compass_RateLimiter_instInhabitedBucket___closed__0 = _init_l_Compass_RateLimiter_instInhabitedBucket___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_instInhabitedBucket___closed__0);
l_Compass_RateLimiter_instInhabitedBucket = _init_l_Compass_RateLimiter_instInhabitedBucket();
lean_mark_persistent(l_Compass_RateLimiter_instInhabitedBucket);
l_Compass_RateLimiter_instExtractableBucket___closed__0 = _init_l_Compass_RateLimiter_instExtractableBucket___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableBucket___closed__0);
l_Compass_RateLimiter_instExtractableBucket___closed__1 = _init_l_Compass_RateLimiter_instExtractableBucket___closed__1();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableBucket___closed__1);
l_Compass_RateLimiter_instExtractableBucket___closed__2 = _init_l_Compass_RateLimiter_instExtractableBucket___closed__2();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableBucket___closed__2);
l_Compass_RateLimiter_instExtractableBucket = _init_l_Compass_RateLimiter_instExtractableBucket();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableBucket);
l_Compass_RateLimiter_Bucket_fresh___closed__0 = _init_l_Compass_RateLimiter_Bucket_fresh___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_Bucket_fresh___closed__0);
l_Compass_RateLimiter_instReprAcquireResult_repr___closed__0 = _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_instReprAcquireResult_repr___closed__0);
l_Compass_RateLimiter_instReprAcquireResult_repr___closed__1 = _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__1();
lean_mark_persistent(l_Compass_RateLimiter_instReprAcquireResult_repr___closed__1);
l_Compass_RateLimiter_instReprAcquireResult_repr___closed__2 = _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__2();
lean_mark_persistent(l_Compass_RateLimiter_instReprAcquireResult_repr___closed__2);
l_Compass_RateLimiter_instReprAcquireResult_repr___closed__3 = _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__3();
lean_mark_persistent(l_Compass_RateLimiter_instReprAcquireResult_repr___closed__3);
l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4 = _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4();
lean_mark_persistent(l_Compass_RateLimiter_instReprAcquireResult_repr___closed__4);
l_Compass_RateLimiter_instReprAcquireResult_repr___closed__5 = _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__5();
lean_mark_persistent(l_Compass_RateLimiter_instReprAcquireResult_repr___closed__5);
l_Compass_RateLimiter_instReprAcquireResult_repr___closed__6 = _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__6();
lean_mark_persistent(l_Compass_RateLimiter_instReprAcquireResult_repr___closed__6);
l_Compass_RateLimiter_instReprAcquireResult_repr___closed__7 = _init_l_Compass_RateLimiter_instReprAcquireResult_repr___closed__7();
lean_mark_persistent(l_Compass_RateLimiter_instReprAcquireResult_repr___closed__7);
l_Compass_RateLimiter_instReprAcquireResult___closed__0 = _init_l_Compass_RateLimiter_instReprAcquireResult___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_instReprAcquireResult___closed__0);
l_Compass_RateLimiter_instReprAcquireResult = _init_l_Compass_RateLimiter_instReprAcquireResult();
lean_mark_persistent(l_Compass_RateLimiter_instReprAcquireResult);
l_Compass_RateLimiter_AcquireResult_toString___closed__0 = _init_l_Compass_RateLimiter_AcquireResult_toString___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toString___closed__0);
l_Compass_RateLimiter_AcquireResult_toString___closed__1 = _init_l_Compass_RateLimiter_AcquireResult_toString___closed__1();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toString___closed__1);
l_Compass_RateLimiter_AcquireResult_toString___closed__2 = _init_l_Compass_RateLimiter_AcquireResult_toString___closed__2();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toString___closed__2);
l_Compass_RateLimiter_AcquireResult_toJson___closed__0 = _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toJson___closed__0);
l_Compass_RateLimiter_AcquireResult_toJson___closed__1 = _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__1();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toJson___closed__1);
l_Compass_RateLimiter_AcquireResult_toJson___closed__2 = _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__2();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toJson___closed__2);
l_Compass_RateLimiter_AcquireResult_toJson___closed__3 = _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__3();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toJson___closed__3);
l_Compass_RateLimiter_AcquireResult_toJson___closed__4 = _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__4();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toJson___closed__4);
l_Compass_RateLimiter_AcquireResult_toJson___closed__5 = _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__5();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toJson___closed__5);
l_Compass_RateLimiter_AcquireResult_toJson___closed__6 = _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__6();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toJson___closed__6);
l_Compass_RateLimiter_AcquireResult_toJson___closed__7 = _init_l_Compass_RateLimiter_AcquireResult_toJson___closed__7();
lean_mark_persistent(l_Compass_RateLimiter_AcquireResult_toJson___closed__7);
l_Compass_RateLimiter_instExtractableAcquireResult___closed__0 = _init_l_Compass_RateLimiter_instExtractableAcquireResult___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableAcquireResult___closed__0);
l_Compass_RateLimiter_instExtractableAcquireResult___closed__1 = _init_l_Compass_RateLimiter_instExtractableAcquireResult___closed__1();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableAcquireResult___closed__1);
l_Compass_RateLimiter_instExtractableAcquireResult___closed__2 = _init_l_Compass_RateLimiter_instExtractableAcquireResult___closed__2();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableAcquireResult___closed__2);
l_Compass_RateLimiter_instExtractableAcquireResult = _init_l_Compass_RateLimiter_instExtractableAcquireResult();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableAcquireResult);
l_Compass_RateLimiter_decodeOptInt___closed__0 = _init_l_Compass_RateLimiter_decodeOptInt___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_decodeOptInt___closed__0);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__0 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__0);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__1 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__1();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__1);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__2 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__2();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__2);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__3 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__3();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__3);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__4 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__4();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__4);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__5 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__5();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__5);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__6 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__6();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__6);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__7 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__7();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__7);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__8 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__8();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__8);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__9 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__9();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__9);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__10 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__10();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__10);
l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__11 = _init_l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__11();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats_repr___redArg___closed__11);
l_Compass_RateLimiter_instReprRateLimitStats___closed__0 = _init_l_Compass_RateLimiter_instReprRateLimitStats___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats___closed__0);
l_Compass_RateLimiter_instReprRateLimitStats = _init_l_Compass_RateLimiter_instReprRateLimitStats();
lean_mark_persistent(l_Compass_RateLimiter_instReprRateLimitStats);
l_Compass_RateLimiter_instExtractableRateLimitStats___closed__0 = _init_l_Compass_RateLimiter_instExtractableRateLimitStats___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableRateLimitStats___closed__0);
l_Compass_RateLimiter_instExtractableRateLimitStats___closed__1 = _init_l_Compass_RateLimiter_instExtractableRateLimitStats___closed__1();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableRateLimitStats___closed__1);
l_Compass_RateLimiter_instExtractableRateLimitStats___closed__2 = _init_l_Compass_RateLimiter_instExtractableRateLimitStats___closed__2();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableRateLimitStats___closed__2);
l_Compass_RateLimiter_instExtractableRateLimitStats = _init_l_Compass_RateLimiter_instExtractableRateLimitStats();
lean_mark_persistent(l_Compass_RateLimiter_instExtractableRateLimitStats);
l_Compass_RateLimiter_RateLimitStats_empty___closed__0 = _init_l_Compass_RateLimiter_RateLimitStats_empty___closed__0();
lean_mark_persistent(l_Compass_RateLimiter_RateLimitStats_empty___closed__0);
l_Compass_RateLimiter_RateLimitStats_empty = _init_l_Compass_RateLimiter_RateLimitStats_empty();
lean_mark_persistent(l_Compass_RateLimiter_RateLimitStats_empty);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
