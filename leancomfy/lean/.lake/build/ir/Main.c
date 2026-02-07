// Lean compiler output
// Module: Main
// Imports: public import Init public import TensorCore.Basic public import TensorCore.Tensor public import TensorCore.Ops public import TensorCore.Graph public import TensorCore.FFI
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
LEAN_EXPORT lean_object* _lean_main();
static lean_object* lp_tensor_x2dcore_main___closed__3;
LEAN_EXPORT lean_object* lp_tensor_x2dcore_main___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
LEAN_EXPORT lean_object* lp_tensor_x2dcore_IO_println___at___00main_spec__0(lean_object*);
static lean_object* lp_tensor_x2dcore_main___closed__0;
LEAN_EXPORT lean_object* lp_tensor_x2dcore_IO_print___at___00IO_println___at___00main_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_IO_println___at___00main_spec__0___boxed(lean_object*, lean_object*);
static lean_object* lp_tensor_x2dcore_main___closed__1;
static lean_object* lp_tensor_x2dcore_main___closed__5;
static lean_object* lp_tensor_x2dcore_main___closed__4;
static lean_object* lp_tensor_x2dcore_main___closed__6;
static lean_object* lp_tensor_x2dcore_main___closed__7;
static lean_object* lp_tensor_x2dcore_main___closed__2;
LEAN_EXPORT lean_object* lp_tensor_x2dcore_IO_print___at___00IO_println___at___00main_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stdout();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_IO_println___at___00main_spec__0(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = lp_tensor_x2dcore_IO_print___at___00IO_println___at___00main_spec__0_spec__0(x_4);
return x_5;
}
}
static lean_object* _init_lp_tensor_x2dcore_main___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("TensorCore - Type-safe tensors for the discerning droid", 55, 55);
return x_1;
}
}
static lean_object* _init_lp_tensor_x2dcore_main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_lp_tensor_x2dcore_main___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("This library provides:", 22, 22);
return x_1;
}
}
static lean_object* _init_lp_tensor_x2dcore_main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  • Dependent types for tensor shapes", 39, 37);
return x_1;
}
}
static lean_object* _init_lp_tensor_x2dcore_main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  • Compile-time shape checking", 33, 31);
return x_1;
}
}
static lean_object* _init_lp_tensor_x2dcore_main___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  • Type-safe computation graphs", 34, 32);
return x_1;
}
}
static lean_object* _init_lp_tensor_x2dcore_main___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  • FFI boundary with runtime validation", 42, 40);
return x_1;
}
}
static lean_object* _init_lp_tensor_x2dcore_main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("The droids can't cheat here.", 28, 28);
return x_1;
}
}
LEAN_EXPORT lean_object* _lean_main() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lp_tensor_x2dcore_main___closed__0;
x_3 = lp_tensor_x2dcore_IO_println___at___00main_spec__0(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_3);
x_4 = lp_tensor_x2dcore_main___closed__1;
x_5 = lp_tensor_x2dcore_IO_println___at___00main_spec__0(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec_ref(x_5);
x_6 = lp_tensor_x2dcore_main___closed__2;
x_7 = lp_tensor_x2dcore_IO_println___at___00main_spec__0(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_7);
x_8 = lp_tensor_x2dcore_main___closed__3;
x_9 = lp_tensor_x2dcore_IO_println___at___00main_spec__0(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_9);
x_10 = lp_tensor_x2dcore_main___closed__4;
x_11 = lp_tensor_x2dcore_IO_println___at___00main_spec__0(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec_ref(x_11);
x_12 = lp_tensor_x2dcore_main___closed__5;
x_13 = lp_tensor_x2dcore_IO_println___at___00main_spec__0(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_13);
x_14 = lp_tensor_x2dcore_main___closed__6;
x_15 = lp_tensor_x2dcore_IO_println___at___00main_spec__0(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec_ref(x_15);
x_16 = lp_tensor_x2dcore_IO_println___at___00main_spec__0(x_4);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_16);
x_17 = lp_tensor_x2dcore_main___closed__7;
x_18 = lp_tensor_x2dcore_IO_println___at___00main_spec__0(x_17);
return x_18;
}
else
{
return x_16;
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
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_IO_println___at___00main_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_tensor_x2dcore_IO_println___at___00main_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_IO_print___at___00IO_println___at___00main_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_tensor_x2dcore_IO_print___at___00IO_println___at___00main_spec__0_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = _lean_main();
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tensor_x2dcore_TensorCore_Basic(uint8_t builtin);
lean_object* initialize_tensor_x2dcore_TensorCore_Tensor(uint8_t builtin);
lean_object* initialize_tensor_x2dcore_TensorCore_Ops(uint8_t builtin);
lean_object* initialize_tensor_x2dcore_TensorCore_Graph(uint8_t builtin);
lean_object* initialize_tensor_x2dcore_TensorCore_FFI(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tensor_x2dcore_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tensor_x2dcore_TensorCore_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tensor_x2dcore_TensorCore_Tensor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tensor_x2dcore_TensorCore_Ops(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tensor_x2dcore_TensorCore_Graph(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tensor_x2dcore_TensorCore_FFI(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_tensor_x2dcore_main___closed__0 = _init_lp_tensor_x2dcore_main___closed__0();
lean_mark_persistent(lp_tensor_x2dcore_main___closed__0);
lp_tensor_x2dcore_main___closed__1 = _init_lp_tensor_x2dcore_main___closed__1();
lean_mark_persistent(lp_tensor_x2dcore_main___closed__1);
lp_tensor_x2dcore_main___closed__2 = _init_lp_tensor_x2dcore_main___closed__2();
lean_mark_persistent(lp_tensor_x2dcore_main___closed__2);
lp_tensor_x2dcore_main___closed__3 = _init_lp_tensor_x2dcore_main___closed__3();
lean_mark_persistent(lp_tensor_x2dcore_main___closed__3);
lp_tensor_x2dcore_main___closed__4 = _init_lp_tensor_x2dcore_main___closed__4();
lean_mark_persistent(lp_tensor_x2dcore_main___closed__4);
lp_tensor_x2dcore_main___closed__5 = _init_lp_tensor_x2dcore_main___closed__5();
lean_mark_persistent(lp_tensor_x2dcore_main___closed__5);
lp_tensor_x2dcore_main___closed__6 = _init_lp_tensor_x2dcore_main___closed__6();
lean_mark_persistent(lp_tensor_x2dcore_main___closed__6);
lp_tensor_x2dcore_main___closed__7 = _init_lp_tensor_x2dcore_main___closed__7();
lean_mark_persistent(lp_tensor_x2dcore_main___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize_runtime_module();

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
lean_initialize_runtime_module();
lean_set_panic_messages(false);
res = initialize_tensor_x2dcore_Main(1 /* builtin */);
lean_set_panic_messages(true);
lean_io_mark_end_initialization();
if (lean_io_result_is_ok(res)) {
lean_dec_ref(res);
lean_init_task_manager();
res = _lean_main();
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
