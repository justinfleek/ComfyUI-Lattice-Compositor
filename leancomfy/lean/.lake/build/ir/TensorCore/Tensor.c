// Lean compiler output
// Module: TensorCore.Tensor
// Imports: public import Init public import TensorCore.Basic
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
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_shape___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_mk(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_dtype___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_numel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_mk_x3f(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_numel___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore___private_TensorCore_Tensor_0__ByteArray_size_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tensor_x2dcore_TensorCore_Tensor_dtype___redArg(uint8_t);
uint8_t lp_tensor_x2dcore_TensorCore_instDecidableAllPos(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_shape(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore___private_TensorCore_Tensor_0__ByteArray_size_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_numel(lean_object*, uint8_t, lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_dtype___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_zeros(lean_object*, uint8_t, lean_object*);
lean_object* lean_byte_array_data(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg___boxed(lean_object*, lean_object*);
lean_object* lp_tensor_x2dcore_TensorCore_Shape_numel(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_zeros___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lp_tensor_x2dcore_TensorCore_DType_sizeof(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_tensor_x2dcore_TensorCore_Tensor_dtype(lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_numel___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_shape___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_mk_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_shape___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_mk_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_byte_array_size(x_3);
x_5 = lp_tensor_x2dcore_TensorCore_Shape_numel(x_1);
x_6 = lp_tensor_x2dcore_TensorCore_DType_sizeof(x_2);
x_7 = lean_nat_mul(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_nat_dec_eq(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_3);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lp_tensor_x2dcore_TensorCore_instDecidableAllPos(x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_3);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_mk_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lp_tensor_x2dcore_TensorCore_Tensor_mk_x3f(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore___private_TensorCore_Tensor_0__ByteArray_size_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_byte_array_data(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore___private_TensorCore_Tensor_0__ByteArray_size_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_tensor_x2dcore___private_TensorCore_Tensor_0__ByteArray_size_match__1_splitter___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(lean_object* x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lp_tensor_x2dcore_TensorCore_Shape_numel(x_1);
x_4 = lp_tensor_x2dcore_TensorCore_DType_sizeof(x_2);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = l_List_replicateTR___redArg(x_5, x_7);
x_9 = lean_array_mk(x_8);
x_10 = lean_byte_array_mk(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_zeros(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_zeros___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lp_tensor_x2dcore_TensorCore_Tensor_zeros(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
x_4 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_1, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_shape(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_shape___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_shape___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lp_tensor_x2dcore_TensorCore_Tensor_shape(x_1, x_4, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_shape___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_tensor_x2dcore_TensorCore_Tensor_shape___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t lp_tensor_x2dcore_TensorCore_Tensor_dtype(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
return x_2;
}
}
LEAN_EXPORT uint8_t lp_tensor_x2dcore_TensorCore_Tensor_dtype___redArg(uint8_t x_1) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_dtype___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
x_5 = lp_tensor_x2dcore_TensorCore_Tensor_dtype(x_1, x_4, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_dtype___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
x_3 = lp_tensor_x2dcore_TensorCore_Tensor_dtype___redArg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_numel(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_tensor_x2dcore_TensorCore_Shape_numel(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_numel___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_tensor_x2dcore_TensorCore_Shape_numel(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_numel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = lp_tensor_x2dcore_TensorCore_Tensor_numel(x_1, x_4, x_3);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_Tensor_numel___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_tensor_x2dcore_TensorCore_Tensor_numel___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tensor_x2dcore_TensorCore_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tensor_x2dcore_TensorCore_Tensor(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tensor_x2dcore_TensorCore_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
