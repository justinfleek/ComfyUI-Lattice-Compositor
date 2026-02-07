// Lean compiler output
// Module: Compass.Budget
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
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__8;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__7;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__0;
LEAN_EXPORT lean_object* l_Compass_Budget_refill___boxed(lean_object*, lean_object*);
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__18;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__11;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__3;
LEAN_EXPORT lean_object* l_Compass_Budget_consume___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Compass_Budget_decodeBudgetState(lean_object*);
LEAN_EXPORT lean_object* l_Compass_Budget_instReprBudgetState_repr(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Compass_Budget_0__Compass_Budget_decodeBudgetState_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Compass_Budget_BudgetState_ctorIdx(lean_object*);
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
LEAN_EXPORT lean_object* l_Compass_Budget_instReprBudgetState_repr___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Compass_Budget_instExtractableBudgetState___closed__0;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__19;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__9;
LEAN_EXPORT lean_object* l_Compass_Budget_instExtractableBudgetState;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__12;
LEAN_EXPORT lean_object* l_Compass_Budget_instReprBudgetState;
LEAN_EXPORT lean_object* l_Compass_Budget_BudgetState_ctorIdx___boxed(lean_object*);
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__6;
LEAN_EXPORT lean_object* l_Compass_Budget_instExtractableBudgetState___lam__0(lean_object*);
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__20;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__16;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__15;
LEAN_EXPORT lean_object* l_Compass_Budget_refill(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__14;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__4;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__21;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__17;
LEAN_EXPORT lean_object* l_Compass_Budget_consume(lean_object*, lean_object*);
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__13;
LEAN_EXPORT lean_object* l___private_Compass_Budget_0__Compass_Budget_decodeBudgetState_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__2;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1;
static lean_object* l_Compass_Budget_instReprBudgetState___closed__0;
static lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg___closed__5;
LEAN_EXPORT lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Compass_Budget_BudgetState_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_Budget_BudgetState_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Compass_Budget_BudgetState_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("current", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__5;
x_2 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__3;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(11u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("max", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(7u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invariant", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__15;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__0;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__18;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__17;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Compass_Budget_instReprBudgetState_repr___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__5;
x_6 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__6;
x_7 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__7;
x_8 = l_Nat_reprFast(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_tag(x_1, 4);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_7);
x_10 = 0;
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__9;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__11;
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__12;
x_21 = l_Nat_reprFast(x_4);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_10);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_13);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
x_28 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__14;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_5);
x_31 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__16;
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__19;
x_34 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__20;
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
x_36 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__21;
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_10);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_1);
x_42 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__5;
x_43 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__6;
x_44 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__7;
x_45 = l_Nat_reprFast(x_40);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = 0;
x_49 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__9;
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_box(1);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__11;
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_42);
x_58 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__12;
x_59 = l_Nat_reprFast(x_41);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_48);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_51);
x_65 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_53);
x_66 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__14;
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_42);
x_69 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__16;
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__19;
x_72 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__20;
x_73 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
x_74 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__21;
x_75 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_48);
return x_77;
}
}
}
LEAN_EXPORT lean_object* l_Compass_Budget_instReprBudgetState_repr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_Budget_instReprBudgetState_repr___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_Budget_instReprBudgetState_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_Budget_instReprBudgetState_repr(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_Budget_instReprBudgetState_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_Budget_instReprBudgetState() {
_start:
{
lean_object* x_1; 
x_1 = l_Compass_Budget_instReprBudgetState___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Compass_Budget_refill(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_add(x_4, x_2);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_6);
lean_inc(x_5);
lean_ctor_set(x_1, 0, x_5);
return x_1;
}
else
{
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_nat_add(x_8, x_2);
lean_dec(x_8);
x_11 = lean_nat_dec_le(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_Budget_refill___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_Budget_refill(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_Budget_consume(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_dec_le(x_2, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_nat_sub(x_4, x_2);
lean_dec(x_4);
lean_ctor_set(x_1, 0, x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_nat_dec_le(x_2, x_10);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_nat_sub(x_10, x_2);
lean_dec(x_10);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Compass_Budget_consume___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Compass_Budget_consume(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Compass_Budget_decodeBudgetState(lean_object* x_1) {
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
x_7 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1;
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
if (lean_obj_tag(x_6) == 2)
{
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec_ref(x_6);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec_ref(x_4);
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
x_16 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
x_17 = lean_string_dec_eq(x_14, x_16);
lean_dec(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_10);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
x_18 = lean_box(0);
return x_18;
}
else
{
if (lean_obj_tag(x_15) == 2)
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = l_Int_toNat(x_11);
lean_dec(x_11);
x_22 = l_Int_toNat(x_20);
lean_dec(x_20);
x_23 = lean_nat_dec_le(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_15);
lean_free_object(x_10);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_ctor_set(x_10, 1, x_22);
lean_ctor_set(x_10, 0, x_21);
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = l_Int_toNat(x_11);
lean_dec(x_11);
x_27 = l_Int_toNat(x_25);
lean_dec(x_25);
x_28 = lean_nat_dec_le(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_10);
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; 
lean_ctor_set(x_10, 1, x_27);
lean_ctor_set(x_10, 0, x_26);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_10);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_free_object(x_10);
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec(x_11);
x_31 = lean_box(0);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_free_object(x_10);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
x_32 = lean_box(0);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
x_36 = lean_string_dec_eq(x_33, x_35);
lean_dec(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_12);
lean_dec(x_11);
x_37 = lean_box(0);
return x_37;
}
else
{
if (lean_obj_tag(x_34) == 2)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 x_39 = x_34;
} else {
 lean_dec_ref(x_34);
 x_39 = lean_box(0);
}
x_40 = l_Int_toNat(x_11);
lean_dec(x_11);
x_41 = l_Int_toNat(x_38);
lean_dec(x_38);
x_42 = lean_nat_dec_le(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_43 = lean_box(0);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_41);
if (lean_is_scalar(x_39)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_39;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec_ref(x_34);
lean_dec(x_12);
lean_dec(x_11);
x_46 = lean_box(0);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_34);
lean_dec(x_12);
lean_dec(x_11);
x_47 = lean_box(0);
return x_47;
}
}
}
}
else
{
lean_object* x_48; 
lean_dec_ref(x_6);
lean_dec(x_4);
x_48 = lean_box(0);
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_6);
lean_dec(x_4);
x_49 = lean_box(0);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_2);
x_50 = lean_box(0);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_1);
x_51 = lean_box(0);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l___private_Compass_Budget_0__Compass_Budget_decodeBudgetState_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1;
x_12 = lean_string_dec_eq(x_9, x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_6);
lean_dec(x_10);
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_2);
x_13 = lean_apply_2(x_3, x_1, lean_box(0));
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 0);
lean_dec(x_15);
if (lean_obj_tag(x_10) == 2)
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
x_22 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
x_23 = lean_string_dec_eq(x_20, x_22);
lean_dec(x_20);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_21);
lean_free_object(x_6);
lean_dec(x_2);
lean_inc_ref(x_10);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 0, x_11);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_10, 0);
lean_dec(x_25);
lean_ctor_set(x_4, 0, x_16);
lean_ctor_set_tag(x_10, 6);
lean_ctor_set(x_10, 0, x_4);
x_26 = lean_apply_2(x_3, x_10, lean_box(0));
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
lean_ctor_set(x_4, 0, x_16);
x_27 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_27, 0, x_4);
x_28 = lean_apply_2(x_3, x_27, lean_box(0));
return x_28;
}
}
else
{
uint8_t x_29; 
lean_inc(x_19);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_8, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_8, 0);
lean_dec(x_31);
if (lean_obj_tag(x_21) == 2)
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_free_object(x_8);
lean_free_object(x_16);
lean_inc(x_18);
lean_free_object(x_6);
lean_dec_ref(x_10);
lean_free_object(x_4);
lean_dec(x_3);
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec_ref(x_21);
x_33 = lean_apply_2(x_2, x_18, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_inc_ref(x_10);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 0, x_11);
x_34 = !lean_is_exclusive(x_10);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_10, 0);
lean_dec(x_35);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_4, 0, x_16);
lean_ctor_set_tag(x_10, 6);
lean_ctor_set(x_10, 0, x_4);
x_36 = lean_apply_2(x_3, x_10, lean_box(0));
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_4, 0, x_16);
x_37 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_37, 0, x_4);
x_38 = lean_apply_2(x_3, x_37, lean_box(0));
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_2);
lean_inc_ref(x_10);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 0, x_11);
x_39 = !lean_is_exclusive(x_10);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_10, 0);
lean_dec(x_40);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_4, 0, x_16);
lean_ctor_set_tag(x_10, 6);
lean_ctor_set(x_10, 0, x_4);
x_41 = lean_apply_2(x_3, x_10, lean_box(0));
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_4, 0, x_16);
x_42 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_42, 0, x_4);
x_43 = lean_apply_2(x_3, x_42, lean_box(0));
return x_43;
}
}
}
else
{
lean_dec(x_8);
if (lean_obj_tag(x_21) == 2)
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_free_object(x_16);
lean_inc(x_18);
lean_free_object(x_6);
lean_dec_ref(x_10);
lean_free_object(x_4);
lean_dec(x_3);
x_44 = lean_ctor_get(x_21, 0);
lean_inc(x_44);
lean_dec_ref(x_21);
x_45 = lean_apply_2(x_2, x_18, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
lean_inc_ref(x_10);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 0, x_11);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_46 = x_10;
} else {
 lean_dec_ref(x_10);
 x_46 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_22);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_19);
lean_ctor_set(x_4, 1, x_47);
lean_ctor_set(x_4, 0, x_16);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(6, 1, 0);
} else {
 x_48 = x_46;
 lean_ctor_set_tag(x_48, 6);
}
lean_ctor_set(x_48, 0, x_4);
x_49 = lean_apply_2(x_3, x_48, lean_box(0));
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_2);
lean_inc_ref(x_10);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 0, x_11);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_50 = x_10;
} else {
 lean_dec_ref(x_10);
 x_50 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_22);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_6);
lean_ctor_set(x_51, 1, x_19);
lean_ctor_set(x_4, 1, x_51);
lean_ctor_set(x_4, 0, x_16);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(6, 1, 0);
} else {
 x_52 = x_50;
 lean_ctor_set_tag(x_52, 6);
}
lean_ctor_set(x_52, 0, x_4);
x_53 = lean_apply_2(x_3, x_52, lean_box(0));
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_10, 0);
x_55 = lean_ctor_get(x_8, 1);
x_56 = lean_ctor_get(x_16, 0);
x_57 = lean_ctor_get(x_16, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_16);
x_58 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
x_59 = lean_string_dec_eq(x_56, x_58);
lean_dec(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_57);
lean_free_object(x_6);
lean_dec(x_2);
lean_inc_ref(x_10);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_11);
lean_ctor_set(x_60, 1, x_10);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_61 = x_10;
} else {
 lean_dec_ref(x_10);
 x_61 = lean_box(0);
}
lean_ctor_set(x_4, 0, x_60);
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(6, 1, 0);
} else {
 x_62 = x_61;
 lean_ctor_set_tag(x_62, 6);
}
lean_ctor_set(x_62, 0, x_4);
x_63 = lean_apply_2(x_3, x_62, lean_box(0));
return x_63;
}
else
{
lean_object* x_64; 
lean_inc(x_55);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_64 = x_8;
} else {
 lean_dec_ref(x_8);
 x_64 = lean_box(0);
}
if (lean_obj_tag(x_57) == 2)
{
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_64);
lean_inc(x_54);
lean_free_object(x_6);
lean_dec_ref(x_10);
lean_free_object(x_4);
lean_dec(x_3);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
lean_dec_ref(x_57);
x_66 = lean_apply_2(x_2, x_54, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_2);
lean_inc_ref(x_10);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_11);
lean_ctor_set(x_67, 1, x_10);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_68 = x_10;
} else {
 lean_dec_ref(x_10);
 x_68 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_57);
lean_ctor_set(x_6, 0, x_58);
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_6);
lean_ctor_set(x_69, 1, x_55);
lean_ctor_set(x_4, 1, x_69);
lean_ctor_set(x_4, 0, x_67);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(6, 1, 0);
} else {
 x_70 = x_68;
 lean_ctor_set_tag(x_70, 6);
}
lean_ctor_set(x_70, 0, x_4);
x_71 = lean_apply_2(x_3, x_70, lean_box(0));
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_2);
lean_inc_ref(x_10);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_11);
lean_ctor_set(x_72, 1, x_10);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_73 = x_10;
} else {
 lean_dec_ref(x_10);
 x_73 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_57);
lean_ctor_set(x_6, 0, x_58);
if (lean_is_scalar(x_64)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_64;
}
lean_ctor_set(x_74, 0, x_6);
lean_ctor_set(x_74, 1, x_55);
lean_ctor_set(x_4, 1, x_74);
lean_ctor_set(x_4, 0, x_72);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(6, 1, 0);
} else {
 x_75 = x_73;
 lean_ctor_set_tag(x_75, 6);
}
lean_ctor_set(x_75, 0, x_4);
x_76 = lean_apply_2(x_3, x_75, lean_box(0));
return x_76;
}
}
}
}
else
{
lean_object* x_77; 
lean_dec(x_2);
lean_ctor_set(x_6, 0, x_11);
x_77 = lean_apply_2(x_3, x_1, lean_box(0));
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec(x_2);
lean_ctor_set(x_6, 0, x_11);
x_78 = lean_apply_2(x_3, x_1, lean_box(0));
return x_78;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_10) == 2)
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_79 = lean_ctor_get(x_8, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_10, 0);
x_81 = lean_ctor_get(x_8, 1);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_84 = x_79;
} else {
 lean_dec_ref(x_79);
 x_84 = lean_box(0);
}
x_85 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
x_86 = lean_string_dec_eq(x_82, x_85);
lean_dec(x_82);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_83);
lean_free_object(x_6);
lean_dec(x_2);
lean_inc_ref(x_10);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_11);
lean_ctor_set(x_87, 1, x_10);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_88 = x_10;
} else {
 lean_dec_ref(x_10);
 x_88 = lean_box(0);
}
lean_ctor_set(x_4, 0, x_87);
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(6, 1, 0);
} else {
 x_89 = x_88;
 lean_ctor_set_tag(x_89, 6);
}
lean_ctor_set(x_89, 0, x_4);
x_90 = lean_apply_2(x_3, x_89, lean_box(0));
return x_90;
}
else
{
lean_object* x_91; 
lean_inc(x_81);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_91 = x_8;
} else {
 lean_dec_ref(x_8);
 x_91 = lean_box(0);
}
if (lean_obj_tag(x_83) == 2)
{
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_91);
lean_dec(x_84);
lean_inc(x_80);
lean_free_object(x_6);
lean_dec_ref(x_10);
lean_free_object(x_4);
lean_dec(x_3);
x_92 = lean_ctor_get(x_83, 0);
lean_inc(x_92);
lean_dec_ref(x_83);
x_93 = lean_apply_2(x_2, x_80, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_2);
lean_inc_ref(x_10);
if (lean_is_scalar(x_84)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_84;
}
lean_ctor_set(x_94, 0, x_11);
lean_ctor_set(x_94, 1, x_10);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_95 = x_10;
} else {
 lean_dec_ref(x_10);
 x_95 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_83);
lean_ctor_set(x_6, 0, x_85);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_6);
lean_ctor_set(x_96, 1, x_81);
lean_ctor_set(x_4, 1, x_96);
lean_ctor_set(x_4, 0, x_94);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(6, 1, 0);
} else {
 x_97 = x_95;
 lean_ctor_set_tag(x_97, 6);
}
lean_ctor_set(x_97, 0, x_4);
x_98 = lean_apply_2(x_3, x_97, lean_box(0));
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_2);
lean_inc_ref(x_10);
if (lean_is_scalar(x_84)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_84;
}
lean_ctor_set(x_99, 0, x_11);
lean_ctor_set(x_99, 1, x_10);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_100 = x_10;
} else {
 lean_dec_ref(x_10);
 x_100 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_83);
lean_ctor_set(x_6, 0, x_85);
if (lean_is_scalar(x_91)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_91;
}
lean_ctor_set(x_101, 0, x_6);
lean_ctor_set(x_101, 1, x_81);
lean_ctor_set(x_4, 1, x_101);
lean_ctor_set(x_4, 0, x_99);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(6, 1, 0);
} else {
 x_102 = x_100;
 lean_ctor_set_tag(x_102, 6);
}
lean_ctor_set(x_102, 0, x_4);
x_103 = lean_apply_2(x_3, x_102, lean_box(0));
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_2);
lean_ctor_set(x_6, 0, x_11);
x_104 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_104, 0, x_4);
x_105 = lean_apply_2(x_3, x_104, lean_box(0));
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_2);
lean_ctor_set(x_6, 0, x_11);
x_106 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_106, 0, x_4);
x_107 = lean_apply_2(x_3, x_106, lean_box(0));
return x_107;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_108 = lean_ctor_get(x_4, 1);
x_109 = lean_ctor_get(x_6, 0);
x_110 = lean_ctor_get(x_6, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_6);
x_111 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1;
x_112 = lean_string_dec_eq(x_109, x_111);
lean_dec(x_109);
if (x_112 == 0)
{
lean_object* x_113; 
lean_dec(x_110);
lean_free_object(x_4);
lean_dec(x_108);
lean_dec(x_2);
x_113 = lean_apply_2(x_3, x_1, lean_box(0));
return x_113;
}
else
{
lean_object* x_114; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_114 = x_1;
} else {
 lean_dec_ref(x_1);
 x_114 = lean_box(0);
}
if (lean_obj_tag(x_110) == 2)
{
if (lean_obj_tag(x_108) == 1)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_114);
x_115 = lean_ctor_get(x_108, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 0);
x_117 = lean_ctor_get(x_108, 1);
x_118 = lean_ctor_get(x_115, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_120 = x_115;
} else {
 lean_dec_ref(x_115);
 x_120 = lean_box(0);
}
x_121 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
x_122 = lean_string_dec_eq(x_118, x_121);
lean_dec(x_118);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_119);
lean_dec(x_2);
lean_inc_ref(x_110);
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_120;
}
lean_ctor_set(x_123, 0, x_111);
lean_ctor_set(x_123, 1, x_110);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_124 = x_110;
} else {
 lean_dec_ref(x_110);
 x_124 = lean_box(0);
}
lean_ctor_set(x_4, 0, x_123);
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(6, 1, 0);
} else {
 x_125 = x_124;
 lean_ctor_set_tag(x_125, 6);
}
lean_ctor_set(x_125, 0, x_4);
x_126 = lean_apply_2(x_3, x_125, lean_box(0));
return x_126;
}
else
{
lean_object* x_127; 
lean_inc(x_117);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_127 = x_108;
} else {
 lean_dec_ref(x_108);
 x_127 = lean_box(0);
}
if (lean_obj_tag(x_119) == 2)
{
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_127);
lean_dec(x_120);
lean_inc(x_116);
lean_dec_ref(x_110);
lean_free_object(x_4);
lean_dec(x_3);
x_128 = lean_ctor_get(x_119, 0);
lean_inc(x_128);
lean_dec_ref(x_119);
x_129 = lean_apply_2(x_2, x_116, x_128);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_2);
lean_inc_ref(x_110);
if (lean_is_scalar(x_120)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_120;
}
lean_ctor_set(x_130, 0, x_111);
lean_ctor_set(x_130, 1, x_110);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_131 = x_110;
} else {
 lean_dec_ref(x_110);
 x_131 = lean_box(0);
}
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_121);
lean_ctor_set(x_132, 1, x_119);
if (lean_is_scalar(x_127)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_127;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_117);
lean_ctor_set(x_4, 1, x_133);
lean_ctor_set(x_4, 0, x_130);
if (lean_is_scalar(x_131)) {
 x_134 = lean_alloc_ctor(6, 1, 0);
} else {
 x_134 = x_131;
 lean_ctor_set_tag(x_134, 6);
}
lean_ctor_set(x_134, 0, x_4);
x_135 = lean_apply_2(x_3, x_134, lean_box(0));
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
lean_inc_ref(x_110);
if (lean_is_scalar(x_120)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_120;
}
lean_ctor_set(x_136, 0, x_111);
lean_ctor_set(x_136, 1, x_110);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_137 = x_110;
} else {
 lean_dec_ref(x_110);
 x_137 = lean_box(0);
}
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_121);
lean_ctor_set(x_138, 1, x_119);
if (lean_is_scalar(x_127)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_127;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_117);
lean_ctor_set(x_4, 1, x_139);
lean_ctor_set(x_4, 0, x_136);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(6, 1, 0);
} else {
 x_140 = x_137;
 lean_ctor_set_tag(x_140, 6);
}
lean_ctor_set(x_140, 0, x_4);
x_141 = lean_apply_2(x_3, x_140, lean_box(0));
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_2);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_111);
lean_ctor_set(x_142, 1, x_110);
lean_ctor_set(x_4, 0, x_142);
if (lean_is_scalar(x_114)) {
 x_143 = lean_alloc_ctor(6, 1, 0);
} else {
 x_143 = x_114;
}
lean_ctor_set(x_143, 0, x_4);
x_144 = lean_apply_2(x_3, x_143, lean_box(0));
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_2);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_111);
lean_ctor_set(x_145, 1, x_110);
lean_ctor_set(x_4, 0, x_145);
if (lean_is_scalar(x_114)) {
 x_146 = lean_alloc_ctor(6, 1, 0);
} else {
 x_146 = x_114;
}
lean_ctor_set(x_146, 0, x_4);
x_147 = lean_apply_2(x_3, x_146, lean_box(0));
return x_147;
}
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_148 = lean_ctor_get(x_4, 0);
x_149 = lean_ctor_get(x_4, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_4);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_152 = x_148;
} else {
 lean_dec_ref(x_148);
 x_152 = lean_box(0);
}
x_153 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1;
x_154 = lean_string_dec_eq(x_150, x_153);
lean_dec(x_150);
if (x_154 == 0)
{
lean_object* x_155; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_149);
lean_dec(x_2);
x_155 = lean_apply_2(x_3, x_1, lean_box(0));
return x_155;
}
else
{
lean_object* x_156; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_156 = x_1;
} else {
 lean_dec_ref(x_1);
 x_156 = lean_box(0);
}
if (lean_obj_tag(x_151) == 2)
{
if (lean_obj_tag(x_149) == 1)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
lean_dec(x_156);
x_157 = lean_ctor_get(x_149, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_151, 0);
x_159 = lean_ctor_get(x_149, 1);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_162 = x_157;
} else {
 lean_dec_ref(x_157);
 x_162 = lean_box(0);
}
x_163 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
x_164 = lean_string_dec_eq(x_160, x_163);
lean_dec(x_160);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_161);
lean_dec(x_152);
lean_dec(x_2);
lean_inc_ref(x_151);
if (lean_is_scalar(x_162)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_162;
}
lean_ctor_set(x_165, 0, x_153);
lean_ctor_set(x_165, 1, x_151);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_166 = x_151;
} else {
 lean_dec_ref(x_151);
 x_166 = lean_box(0);
}
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_149);
if (lean_is_scalar(x_166)) {
 x_168 = lean_alloc_ctor(6, 1, 0);
} else {
 x_168 = x_166;
 lean_ctor_set_tag(x_168, 6);
}
lean_ctor_set(x_168, 0, x_167);
x_169 = lean_apply_2(x_3, x_168, lean_box(0));
return x_169;
}
else
{
lean_object* x_170; 
lean_inc(x_159);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_170 = x_149;
} else {
 lean_dec_ref(x_149);
 x_170 = lean_box(0);
}
if (lean_obj_tag(x_161) == 2)
{
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_170);
lean_dec(x_162);
lean_inc(x_158);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_3);
x_171 = lean_ctor_get(x_161, 0);
lean_inc(x_171);
lean_dec_ref(x_161);
x_172 = lean_apply_2(x_2, x_158, x_171);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_2);
lean_inc_ref(x_151);
if (lean_is_scalar(x_162)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_162;
}
lean_ctor_set(x_173, 0, x_153);
lean_ctor_set(x_173, 1, x_151);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_174 = x_151;
} else {
 lean_dec_ref(x_151);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_152;
}
lean_ctor_set(x_175, 0, x_163);
lean_ctor_set(x_175, 1, x_161);
if (lean_is_scalar(x_170)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_170;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_159);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_176);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(6, 1, 0);
} else {
 x_178 = x_174;
 lean_ctor_set_tag(x_178, 6);
}
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_apply_2(x_3, x_178, lean_box(0));
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_2);
lean_inc_ref(x_151);
if (lean_is_scalar(x_162)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_162;
}
lean_ctor_set(x_180, 0, x_153);
lean_ctor_set(x_180, 1, x_151);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_181 = x_151;
} else {
 lean_dec_ref(x_151);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_152;
}
lean_ctor_set(x_182, 0, x_163);
lean_ctor_set(x_182, 1, x_161);
if (lean_is_scalar(x_170)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_170;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_159);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_180);
lean_ctor_set(x_184, 1, x_183);
if (lean_is_scalar(x_181)) {
 x_185 = lean_alloc_ctor(6, 1, 0);
} else {
 x_185 = x_181;
 lean_ctor_set_tag(x_185, 6);
}
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_apply_2(x_3, x_185, lean_box(0));
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_2);
if (lean_is_scalar(x_152)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_152;
}
lean_ctor_set(x_187, 0, x_153);
lean_ctor_set(x_187, 1, x_151);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_149);
if (lean_is_scalar(x_156)) {
 x_189 = lean_alloc_ctor(6, 1, 0);
} else {
 x_189 = x_156;
}
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_apply_2(x_3, x_189, lean_box(0));
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_2);
if (lean_is_scalar(x_152)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_152;
}
lean_ctor_set(x_191, 0, x_153);
lean_ctor_set(x_191, 1, x_151);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_149);
if (lean_is_scalar(x_156)) {
 x_193 = lean_alloc_ctor(6, 1, 0);
} else {
 x_193 = x_156;
}
lean_ctor_set(x_193, 0, x_192);
x_194 = lean_apply_2(x_3, x_193, lean_box(0));
return x_194;
}
}
}
}
else
{
lean_object* x_195; 
lean_dec(x_4);
lean_dec(x_2);
x_195 = lean_apply_2(x_3, x_1, lean_box(0));
return x_195;
}
}
else
{
lean_object* x_196; 
lean_dec(x_2);
x_196 = lean_apply_2(x_3, x_1, lean_box(0));
return x_196;
}
}
}
LEAN_EXPORT lean_object* l___private_Compass_Budget_0__Compass_Budget_decodeBudgetState_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Compass_Budget_0__Compass_Budget_decodeBudgetState_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Compass_Budget_instExtractableBudgetState___lam__0(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1;
x_6 = lean_nat_to_int(x_3);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_5);
x_8 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
x_9 = lean_nat_to_int(x_4);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1;
x_19 = lean_nat_to_int(x_16);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10;
x_23 = lean_nat_to_int(x_17);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
static lean_object* _init_l_Compass_Budget_instExtractableBudgetState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Compass_Budget_decodeBudgetState), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Compass_Budget_instExtractableBudgetState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Compass_Budget_instExtractableBudgetState___lam__0), 1, 0);
x_2 = l_Compass_Budget_instExtractableBudgetState___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Compass_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Compass_Budget(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__0 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__0();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__0);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__1);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__2 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__2();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__2);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__3 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__3();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__3);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__4 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__4();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__4);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__5 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__5();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__5);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__6 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__6();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__6);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__7 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__7();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__7);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__8 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__8();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__8);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__9 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__9();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__9);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__10);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__11 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__11();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__11);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__12 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__12();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__12);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__13 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__13();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__13);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__14 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__14();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__14);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__15 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__15();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__15);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__16 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__16();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__16);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__17 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__17();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__17);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__18 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__18();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__18);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__19 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__19();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__19);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__20 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__20();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__20);
l_Compass_Budget_instReprBudgetState_repr___redArg___closed__21 = _init_l_Compass_Budget_instReprBudgetState_repr___redArg___closed__21();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState_repr___redArg___closed__21);
l_Compass_Budget_instReprBudgetState___closed__0 = _init_l_Compass_Budget_instReprBudgetState___closed__0();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState___closed__0);
l_Compass_Budget_instReprBudgetState = _init_l_Compass_Budget_instReprBudgetState();
lean_mark_persistent(l_Compass_Budget_instReprBudgetState);
l_Compass_Budget_instExtractableBudgetState___closed__0 = _init_l_Compass_Budget_instExtractableBudgetState___closed__0();
lean_mark_persistent(l_Compass_Budget_instExtractableBudgetState___closed__0);
l_Compass_Budget_instExtractableBudgetState = _init_l_Compass_Budget_instExtractableBudgetState();
lean_mark_persistent(l_Compass_Budget_instExtractableBudgetState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
