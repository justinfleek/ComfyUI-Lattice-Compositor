// Lean compiler output
// Module: CompassExtractMain
// Imports: public import Init public import Compass public import Compass.Emit
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
LEAN_EXPORT lean_object* _lean_main(lean_object*);
static lean_object* l_main___closed__10;
static lean_object* l_main___closed__19;
static lean_object* l_main___closed__21;
static lean_object* l_main___closed__3;
LEAN_EXPORT lean_object* l_writeFile(lean_object*, lean_object*);
static lean_object* l_writeFile___closed__0;
static lean_object* l_main___closed__12;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
static lean_object* l_main___closed__20;
lean_object* l_IO_FS_createDirAll(lean_object*);
static lean_object* l_main___closed__16;
static lean_object* l_main___closed__11;
static lean_object* l_main___closed__0;
static lean_object* l_main___closed__13;
static lean_object* l_main___closed__14;
static lean_object* l_main___closed__1;
static lean_object* l_main___closed__25;
extern lean_object* l_Compass_Emit_pureScriptModule;
static lean_object* l_main___closed__5;
static lean_object* l_main___closed__4;
static lean_object* l_main___closed__15;
static lean_object* l_main___closed__17;
lean_object* l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(lean_object*);
static lean_object* l_main___closed__9;
static lean_object* l_main___closed__6;
extern lean_object* l_Compass_Emit_elmModule;
static lean_object* l_main___closed__8;
static lean_object* l_main___closed__23;
extern lean_object* l_Compass_Emit_pythonModule;
static lean_object* l_main___closed__7;
static lean_object* l_main___closed__24;
static lean_object* l_main___closed__22;
LEAN_EXPORT lean_object* l_writeFile___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
static lean_object* l_main___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_main___closed__18;
static lean_object* _init_l_writeFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Wrote ", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_writeFile(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_FS_writeFile(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_4);
x_5 = l_writeFile___closed__0;
x_6 = lean_string_append(x_5, x_1);
x_7 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_6);
return x_7;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_writeFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_writeFile(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
static lean_object* _init_l_main___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Usage: lake exe compass-extract <target>", 40, 40);
return x_1;
}
}
static lean_object* _init_l_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Targets:", 8, 8);
return x_1;
}
}
static lean_object* _init_l_main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  purescript  Extract verified PureScript types + codecs (PRIMARY)", 66, 66);
return x_1;
}
}
static lean_object* _init_l_main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  python      Extract verified Python dataclasses", 49, 49);
return x_1;
}
}
static lean_object* _init_l_main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  elm         Extract verified Elm types + codecs (legacy)", 58, 58);
return x_1;
}
}
static lean_object* _init_l_main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  all         Extract everything", 32, 32);
return x_1;
}
}
static lean_object* _init_l_main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Every extracted type has a proven roundtrip theorem in Lean.", 60, 60);
return x_1;
}
}
static lean_object* _init_l_main___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The proofs guarantee the extraction is correct.", 47, 47);
return x_1;
}
}
static lean_object* _init_l_main___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Types extracted:", 16, 16);
return x_1;
}
}
static lean_object* _init_l_main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  - Permission (21 variants)", 28, 28);
return x_1;
}
}
static lean_object* _init_l_main___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  - Role (4 variants)", 21, 21);
return x_1;
}
}
static lean_object* _init_l_main___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  - User", 8, 8);
return x_1;
}
}
static lean_object* _init_l_main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  - Session", 11, 11);
return x_1;
}
}
static lean_object* _init_l_main___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  - JobStatus (7 variants)", 26, 26);
return x_1;
}
}
static lean_object* _init_l_main___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("purescript", 10, 10);
return x_1;
}
}
static lean_object* _init_l_main___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("python", 6, 6);
return x_1;
}
}
static lean_object* _init_l_main___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("elm", 3, 3);
return x_1;
}
}
static lean_object* _init_l_main___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all", 3, 3);
return x_1;
}
}
static lean_object* _init_l_main___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extracted/purescript/Compass", 28, 28);
return x_1;
}
}
static lean_object* _init_l_main___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extracted/python", 16, 16);
return x_1;
}
}
static lean_object* _init_l_main___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extracted/elm/Compass", 21, 21);
return x_1;
}
}
static lean_object* _init_l_main___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extracted/purescript/Compass/Types.purs", 39, 39);
return x_1;
}
}
static lean_object* _init_l_main___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extracted/python/compass_types.py", 33, 33);
return x_1;
}
}
static lean_object* _init_l_main___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extracted/elm/Compass/Types.elm", 31, 31);
return x_1;
}
}
static lean_object* _init_l_main___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Done. All COMPASS types extracted from proofs.", 46, 46);
return x_1;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* x_1) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_dec_ref(x_1);
x_39 = l_main___closed__15;
x_40 = lean_string_dec_eq(x_37, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = l_main___closed__16;
x_42 = lean_string_dec_eq(x_37, x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = l_main___closed__17;
x_44 = lean_string_dec_eq(x_37, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = l_main___closed__18;
x_46 = lean_string_dec_eq(x_37, x_45);
lean_dec(x_37);
if (x_46 == 0)
{
lean_dec(x_38);
x_3 = lean_box(0);
goto block_36;
}
else
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_main___closed__19;
x_48 = l_IO_FS_createDirAll(x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec_ref(x_48);
x_49 = l_main___closed__20;
x_50 = l_IO_FS_createDirAll(x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_50);
x_51 = l_main___closed__21;
x_52 = l_IO_FS_createDirAll(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_52);
x_53 = l_main___closed__22;
x_54 = l_Compass_Emit_pureScriptModule;
x_55 = l_writeFile(x_53, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_55);
x_56 = l_main___closed__23;
x_57 = l_Compass_Emit_pythonModule;
x_58 = l_writeFile(x_56, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_58);
x_59 = l_main___closed__24;
x_60 = l_Compass_Emit_elmModule;
x_61 = l_writeFile(x_59, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_61);
x_62 = l_main___closed__25;
x_63 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_62);
return x_63;
}
else
{
return x_61;
}
}
else
{
return x_58;
}
}
else
{
return x_55;
}
}
else
{
return x_52;
}
}
else
{
return x_50;
}
}
else
{
return x_48;
}
}
else
{
lean_dec(x_38);
x_3 = lean_box(0);
goto block_36;
}
}
}
else
{
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_main___closed__21;
x_65 = l_IO_FS_createDirAll(x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_65);
x_66 = l_main___closed__24;
x_67 = l_Compass_Emit_elmModule;
x_68 = l_writeFile(x_66, x_67);
return x_68;
}
else
{
return x_65;
}
}
else
{
lean_dec(x_38);
x_3 = lean_box(0);
goto block_36;
}
}
}
else
{
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_main___closed__20;
x_70 = l_IO_FS_createDirAll(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_70);
x_71 = l_main___closed__23;
x_72 = l_Compass_Emit_pythonModule;
x_73 = l_writeFile(x_71, x_72);
return x_73;
}
else
{
return x_70;
}
}
else
{
lean_dec(x_38);
x_3 = lean_box(0);
goto block_36;
}
}
}
else
{
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_main___closed__19;
x_75 = l_IO_FS_createDirAll(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_75);
x_76 = l_main___closed__22;
x_77 = l_Compass_Emit_pureScriptModule;
x_78 = l_writeFile(x_76, x_77);
return x_78;
}
else
{
return x_75;
}
}
else
{
lean_dec(x_38);
x_3 = lean_box(0);
goto block_36;
}
}
}
else
{
lean_dec(x_1);
x_3 = lean_box(0);
goto block_36;
}
block_36:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_main___closed__0;
x_5 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_5);
x_6 = l_main___closed__1;
x_7 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_7);
x_8 = l_main___closed__2;
x_9 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_9);
x_10 = l_main___closed__3;
x_11 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_11);
x_12 = l_main___closed__4;
x_13 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_13);
x_14 = l_main___closed__5;
x_15 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_15);
x_16 = l_main___closed__6;
x_17 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec_ref(x_17);
x_18 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_18);
x_19 = l_main___closed__7;
x_20 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_20);
x_21 = l_main___closed__8;
x_22 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec_ref(x_22);
x_23 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_6);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_23);
x_24 = l_main___closed__9;
x_25 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_25);
x_26 = l_main___closed__10;
x_27 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_27);
x_28 = l_main___closed__11;
x_29 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_29);
x_30 = l_main___closed__12;
x_31 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_31);
x_32 = l_main___closed__13;
x_33 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_33);
x_34 = l_main___closed__14;
x_35 = l_IO_println___at___00Lean_Environment_transitivelyRequiredModules_x27_spec__10(x_34);
return x_35;
}
else
{
return x_33;
}
}
else
{
return x_31;
}
}
else
{
return x_29;
}
}
else
{
return x_27;
}
}
else
{
return x_25;
}
}
else
{
return x_23;
}
}
else
{
return x_22;
}
}
else
{
return x_20;
}
}
else
{
return x_18;
}
}
else
{
return x_17;
}
}
else
{
return x_15;
}
}
else
{
return x_13;
}
}
else
{
return x_11;
}
}
else
{
return x_9;
}
}
else
{
return x_7;
}
}
else
{
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = _lean_main(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Compass(uint8_t builtin);
lean_object* initialize_Compass_Emit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_CompassExtractMain(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Emit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_writeFile___closed__0 = _init_l_writeFile___closed__0();
lean_mark_persistent(l_writeFile___closed__0);
l_main___closed__0 = _init_l_main___closed__0();
lean_mark_persistent(l_main___closed__0);
l_main___closed__1 = _init_l_main___closed__1();
lean_mark_persistent(l_main___closed__1);
l_main___closed__2 = _init_l_main___closed__2();
lean_mark_persistent(l_main___closed__2);
l_main___closed__3 = _init_l_main___closed__3();
lean_mark_persistent(l_main___closed__3);
l_main___closed__4 = _init_l_main___closed__4();
lean_mark_persistent(l_main___closed__4);
l_main___closed__5 = _init_l_main___closed__5();
lean_mark_persistent(l_main___closed__5);
l_main___closed__6 = _init_l_main___closed__6();
lean_mark_persistent(l_main___closed__6);
l_main___closed__7 = _init_l_main___closed__7();
lean_mark_persistent(l_main___closed__7);
l_main___closed__8 = _init_l_main___closed__8();
lean_mark_persistent(l_main___closed__8);
l_main___closed__9 = _init_l_main___closed__9();
lean_mark_persistent(l_main___closed__9);
l_main___closed__10 = _init_l_main___closed__10();
lean_mark_persistent(l_main___closed__10);
l_main___closed__11 = _init_l_main___closed__11();
lean_mark_persistent(l_main___closed__11);
l_main___closed__12 = _init_l_main___closed__12();
lean_mark_persistent(l_main___closed__12);
l_main___closed__13 = _init_l_main___closed__13();
lean_mark_persistent(l_main___closed__13);
l_main___closed__14 = _init_l_main___closed__14();
lean_mark_persistent(l_main___closed__14);
l_main___closed__15 = _init_l_main___closed__15();
lean_mark_persistent(l_main___closed__15);
l_main___closed__16 = _init_l_main___closed__16();
lean_mark_persistent(l_main___closed__16);
l_main___closed__17 = _init_l_main___closed__17();
lean_mark_persistent(l_main___closed__17);
l_main___closed__18 = _init_l_main___closed__18();
lean_mark_persistent(l_main___closed__18);
l_main___closed__19 = _init_l_main___closed__19();
lean_mark_persistent(l_main___closed__19);
l_main___closed__20 = _init_l_main___closed__20();
lean_mark_persistent(l_main___closed__20);
l_main___closed__21 = _init_l_main___closed__21();
lean_mark_persistent(l_main___closed__21);
l_main___closed__22 = _init_l_main___closed__22();
lean_mark_persistent(l_main___closed__22);
l_main___closed__23 = _init_l_main___closed__23();
lean_mark_persistent(l_main___closed__23);
l_main___closed__24 = _init_l_main___closed__24();
lean_mark_persistent(l_main___closed__24);
l_main___closed__25 = _init_l_main___closed__25();
lean_mark_persistent(l_main___closed__25);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize();

  #if defined(WIN32) || defined(_WIN32)
  #include <windows.h>
  #endif

  int main(int argc, char ** argv) {
  #if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
  #endif
  lean_object* in; lean_object* res;
argv = lean_setup_args(argc, argv);
lean_initialize();
lean_set_panic_messages(false);
res = initialize_CompassExtractMain(1 /* builtin */);
lean_set_panic_messages(true);
lean_io_mark_end_initialization();
if (lean_io_result_is_ok(res)) {
lean_dec_ref(res);
lean_init_task_manager();
in = lean_box(0);
int i = argc;
while (i > 1) {
 lean_object* n;
 i--;
 n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
 in = n;
}
res = _lean_main(in);
}
lean_finalize_task_manager();
if (lean_io_result_is_ok(res)) {
  int ret = 0;
  lean_dec_ref(res);
  return ret;
} else {
  lean_io_result_show_error(res);
  lean_dec_ref(res);
  return 1;
}
}
#ifdef __cplusplus
}
#endif
