// Lean compiler output
// Module: Compass.Uuid5
// Imports: public import Init public import Compass.Core
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
lean_object* l_String_quote(lean_object*);
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__5;
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__7;
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__11;
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg(lean_object*);
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__10;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__6;
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instReprUuid5;
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_Uuid5_fromJson(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_Uuid5_ctorIdx(lean_object*);
static lean_object* l_COMPASS_Uuid5_instExtractableUuid5___closed__2;
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instInhabitedUuid5;
LEAN_EXPORT uint8_t l_COMPASS_Uuid5_instDecidableEqUuid5_decEq(lean_object*, lean_object*);
static lean_object* l_COMPASS_Uuid5_instInhabitedUuid5___closed__0;
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__12;
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__3;
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__9;
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__4;
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__1;
lean_object* l_Compass_Core_Json_asString(lean_object*);
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__8;
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__2;
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instExtractableUuid5;
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instReprUuid5_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instDecidableEqUuid5_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_Uuid5_ctorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_COMPASS_Uuid5_instDecidableEqUuid5(lean_object*, lean_object*);
static lean_object* l_COMPASS_Uuid5_instExtractableUuid5___closed__1;
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instDecidableEqUuid5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_Uuid5_toJson(lean_object*);
static lean_object* l_COMPASS_Uuid5_instExtractableUuid5___closed__0;
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___boxed(lean_object*, lean_object*);
static lean_object* l_COMPASS_Uuid5_instReprUuid5___closed__0;
static lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_Uuid5_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_Uuid5_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_COMPASS_Uuid5_Uuid5_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value", 5, 5);
return x_1;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__5;
x_2 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(9u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__9;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_2 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__6;
x_3 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__7;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = 0;
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__10;
x_11 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__11;
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__12;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_7);
return x_16;
}
}
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instReprUuid5_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_COMPASS_Uuid5_instReprUuid5_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instReprUuid5_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_COMPASS_Uuid5_instReprUuid5_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_COMPASS_Uuid5_instReprUuid5_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instReprUuid5() {
_start:
{
lean_object* x_1; 
x_1 = l_COMPASS_Uuid5_instReprUuid5___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_COMPASS_Uuid5_instDecidableEqUuid5_decEq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instDecidableEqUuid5_decEq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_COMPASS_Uuid5_instDecidableEqUuid5_decEq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_COMPASS_Uuid5_instDecidableEqUuid5(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_instDecidableEqUuid5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_COMPASS_Uuid5_instDecidableEqUuid5(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_Uuid5_toJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_COMPASS_Uuid5_Uuid5_fromJson(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_Core_Json_asString(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
}
static lean_object* _init_l_COMPASS_Uuid5_instInhabitedUuid5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("AAAAAAAAAAAAAAAAAAAAAAAAAA", 26, 26);
return x_1;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instInhabitedUuid5() {
_start:
{
lean_object* x_1; 
x_1 = l_COMPASS_Uuid5_instInhabitedUuid5___closed__0;
return x_1;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instExtractableUuid5___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_COMPASS_Uuid5_Uuid5_toJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instExtractableUuid5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_COMPASS_Uuid5_Uuid5_fromJson), 1, 0);
return x_1;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instExtractableUuid5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_COMPASS_Uuid5_instExtractableUuid5___closed__1;
x_2 = l_COMPASS_Uuid5_instExtractableUuid5___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_COMPASS_Uuid5_instExtractableUuid5() {
_start:
{
lean_object* x_1; 
x_1 = l_COMPASS_Uuid5_instExtractableUuid5___closed__2;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Compass_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Compass_Uuid5(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__0 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__0();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__0);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__1 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__1();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__1);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__2 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__2();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__2);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__3 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__3();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__3);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__4 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__4();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__4);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__5 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__5();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__5);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__6 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__6();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__6);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__7 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__7();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__7);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__8 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__8();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__8);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__9 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__9();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__9);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__10 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__10();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__10);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__11 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__11();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__11);
l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__12 = _init_l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__12();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5_repr___redArg___closed__12);
l_COMPASS_Uuid5_instReprUuid5___closed__0 = _init_l_COMPASS_Uuid5_instReprUuid5___closed__0();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5___closed__0);
l_COMPASS_Uuid5_instReprUuid5 = _init_l_COMPASS_Uuid5_instReprUuid5();
lean_mark_persistent(l_COMPASS_Uuid5_instReprUuid5);
l_COMPASS_Uuid5_instInhabitedUuid5___closed__0 = _init_l_COMPASS_Uuid5_instInhabitedUuid5___closed__0();
lean_mark_persistent(l_COMPASS_Uuid5_instInhabitedUuid5___closed__0);
l_COMPASS_Uuid5_instInhabitedUuid5 = _init_l_COMPASS_Uuid5_instInhabitedUuid5();
lean_mark_persistent(l_COMPASS_Uuid5_instInhabitedUuid5);
l_COMPASS_Uuid5_instExtractableUuid5___closed__0 = _init_l_COMPASS_Uuid5_instExtractableUuid5___closed__0();
lean_mark_persistent(l_COMPASS_Uuid5_instExtractableUuid5___closed__0);
l_COMPASS_Uuid5_instExtractableUuid5___closed__1 = _init_l_COMPASS_Uuid5_instExtractableUuid5___closed__1();
lean_mark_persistent(l_COMPASS_Uuid5_instExtractableUuid5___closed__1);
l_COMPASS_Uuid5_instExtractableUuid5___closed__2 = _init_l_COMPASS_Uuid5_instExtractableUuid5___closed__2();
lean_mark_persistent(l_COMPASS_Uuid5_instExtractableUuid5___closed__2);
l_COMPASS_Uuid5_instExtractableUuid5 = _init_l_COMPASS_Uuid5_instExtractableUuid5();
lean_mark_persistent(l_COMPASS_Uuid5_instExtractableUuid5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
