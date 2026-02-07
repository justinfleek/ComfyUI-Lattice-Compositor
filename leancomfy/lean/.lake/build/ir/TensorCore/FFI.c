// Lean compiler output
// Module: TensorCore.FFI
// Imports: public import Init public import TensorCore.Graph public import TensorCore.Basic
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
LEAN_EXPORT lean_object* lp_tensor_x2dcore___private_TensorCore_FFI_0__TensorCore_Shape_numel_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_FFI_graphAddInput___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* graph_add_input(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* tensor_matmul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_FFI_tensorCreate___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lp_tensor_x2dcore_TensorCore_instDecidableEqDType(uint8_t, uint8_t);
uint8_t lp_tensor_x2dcore_TensorCore_instDecidableAllPos(lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(lean_object*, uint8_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_tensor_x2dcore___private_TensorCore_FFI_0__TensorCore_Shape_numel_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_tensor_x2dcore_TensorCore_Graph_addInput(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* graph_new;
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_FFI_tensorDtype___boxed(lean_object*);
lean_object* lp_tensor_x2dcore_TensorCore_Shape_numel(lean_object*);
extern lean_object* lp_tensor_x2dcore_TensorCore_Graph_empty;
LEAN_EXPORT lean_object* tensor_shape(lean_object*);
lean_object* lp_tensor_x2dcore_TensorCore_DType_sizeof(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT uint8_t tensor_dtype(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* tensor_create(lean_object*, uint8_t, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* tensor_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* tensor_conv2d(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_tensor_x2dcore___private_TensorCore_FFI_0__TensorCore_Shape_numel_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore___private_TensorCore_FFI_0__TensorCore_Shape_numel_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_tensor_x2dcore___private_TensorCore_FFI_0__TensorCore_Shape_numel_match__1_splitter___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* tensor_create(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_17; uint8_t x_18; 
x_4 = lean_array_to_list(x_1);
x_5 = lp_tensor_x2dcore_TensorCore_instDecidableAllPos(x_4);
x_17 = 0;
x_18 = lean_uint8_dec_eq(x_2, x_17);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; 
x_19 = 1;
x_20 = lean_uint8_dec_eq(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; 
x_21 = 2;
x_22 = lean_uint8_dec_eq(x_2, x_21);
if (x_22 == 0)
{
uint8_t x_23; uint8_t x_24; 
x_23 = 3;
x_24 = lean_uint8_dec_eq(x_2, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_25 = lean_box(0);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = 3;
x_6 = x_26;
goto block_16;
}
}
else
{
uint8_t x_27; 
x_27 = 2;
x_6 = x_27;
goto block_16;
}
}
else
{
uint8_t x_28; 
x_28 = 1;
x_6 = x_28;
goto block_16;
}
}
else
{
uint8_t x_29; 
x_29 = 0;
x_6 = x_29;
goto block_16;
}
block_16:
{
if (x_5 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_byte_array_size(x_3);
x_9 = lp_tensor_x2dcore_TensorCore_Shape_numel(x_4);
x_10 = lp_tensor_x2dcore_TensorCore_DType_sizeof(x_6);
x_11 = lean_nat_mul(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_nat_dec_eq(x_8, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_6);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_FFI_tensorCreate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = tensor_create(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* tensor_shape(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_array_mk(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t tensor_dtype(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
switch (x_2) {
case 0:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 1:
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
case 2:
{
uint8_t x_5; 
x_5 = 2;
return x_5;
}
default: 
{
uint8_t x_6; 
x_6 = 3;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_FFI_tensorDtype___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = tensor_dtype(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* tensor_matmul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec_ref(x_3);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec_ref(x_4);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_14 = lean_ctor_get(x_2, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_2, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
lean_dec(x_18);
x_19 = lean_nat_dec_eq(x_11, x_17);
lean_dec(x_17);
lean_dec(x_11);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_6);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_7);
x_20 = lean_box(0);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_9, x_13);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_6);
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_7);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_ctor_set(x_6, 0, x_10);
x_23 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_6, x_9);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_9);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_2);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_nat_dec_eq(x_11, x_25);
lean_dec(x_25);
lean_dec(x_11);
if (x_26 == 0)
{
lean_object* x_27; 
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_7);
x_27 = lean_box(0);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_9, x_13);
if (x_28 == 0)
{
lean_object* x_29; 
lean_free_object(x_2);
lean_dec(x_10);
lean_dec_ref(x_7);
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_7);
x_31 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_30, x_9);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_30);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_9);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_2);
return x_32;
}
}
}
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_35 = x_6;
} else {
 lean_dec_ref(x_6);
 x_35 = lean_box(0);
}
x_36 = lean_nat_dec_eq(x_11, x_34);
lean_dec(x_34);
lean_dec(x_11);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec_ref(x_7);
x_37 = lean_box(0);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_9, x_33);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_10);
lean_dec_ref(x_7);
x_39 = lean_box(0);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
if (lean_is_scalar(x_35)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_35;
}
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_7);
x_41 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_40, x_9);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_9);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
else
{
lean_object* x_44; 
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_44 = lean_box(0);
return x_44;
}
}
else
{
lean_object* x_45; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_45 = lean_box(0);
return x_45;
}
}
else
{
lean_object* x_46; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_46 = lean_box(0);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_47 = lean_box(0);
return x_47;
}
}
else
{
lean_object* x_48; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_48 = lean_box(0);
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = lean_box(0);
return x_49;
}
}
}
LEAN_EXPORT lean_object* tensor_conv2d(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 1)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec_ref(x_6);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec_ref(x_7);
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
lean_dec_ref(x_8);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_2, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_dec(x_35);
x_36 = lean_nat_dec_eq(x_17, x_28);
lean_dec(x_28);
lean_dec(x_17);
if (x_36 == 0)
{
lean_object* x_37; 
lean_free_object(x_13);
lean_dec(x_34);
lean_free_object(x_12);
lean_dec(x_31);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_37 = lean_box(0);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_mul(x_38, x_4);
lean_dec(x_4);
x_40 = lean_nat_add(x_18, x_39);
lean_dec(x_18);
x_41 = lean_nat_dec_le(x_31, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_13);
lean_dec(x_34);
lean_free_object(x_12);
lean_dec(x_31);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_3);
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_nat_add(x_19, x_39);
lean_dec(x_39);
lean_dec(x_19);
x_44 = lean_nat_dec_le(x_34, x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_43);
lean_dec(x_40);
lean_free_object(x_13);
lean_dec(x_34);
lean_free_object(x_12);
lean_dec(x_31);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_3);
x_45 = lean_box(0);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_15, x_21);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_43);
lean_dec(x_40);
lean_free_object(x_13);
lean_dec(x_34);
lean_free_object(x_12);
lean_dec(x_31);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_3);
x_47 = lean_box(0);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_nat_sub(x_40, x_31);
lean_dec(x_31);
lean_dec(x_40);
x_49 = lean_nat_div(x_48, x_3);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_add(x_49, x_50);
lean_dec(x_49);
x_52 = lean_nat_sub(x_43, x_34);
lean_dec(x_34);
lean_dec(x_43);
x_53 = lean_nat_div(x_52, x_3);
lean_dec(x_3);
lean_dec(x_52);
x_54 = lean_nat_add(x_53, x_50);
lean_dec(x_53);
lean_ctor_set(x_13, 0, x_54);
lean_ctor_set(x_12, 0, x_51);
lean_ctor_set(x_11, 0, x_25);
lean_ctor_set(x_10, 0, x_16);
x_55 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_10, x_15);
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_15);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_2);
return x_56;
}
}
}
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_13, 0);
lean_inc(x_57);
lean_dec(x_13);
x_58 = lean_nat_dec_eq(x_17, x_28);
lean_dec(x_28);
lean_dec(x_17);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_57);
lean_free_object(x_12);
lean_dec(x_31);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_59 = lean_box(0);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_nat_mul(x_60, x_4);
lean_dec(x_4);
x_62 = lean_nat_add(x_18, x_61);
lean_dec(x_18);
x_63 = lean_nat_dec_le(x_31, x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_57);
lean_free_object(x_12);
lean_dec(x_31);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_3);
x_64 = lean_box(0);
return x_64;
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_nat_add(x_19, x_61);
lean_dec(x_61);
lean_dec(x_19);
x_66 = lean_nat_dec_le(x_57, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_57);
lean_free_object(x_12);
lean_dec(x_31);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_3);
x_67 = lean_box(0);
return x_67;
}
else
{
uint8_t x_68; 
x_68 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_15, x_21);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_57);
lean_free_object(x_12);
lean_dec(x_31);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_3);
x_69 = lean_box(0);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_nat_sub(x_62, x_31);
lean_dec(x_31);
lean_dec(x_62);
x_71 = lean_nat_div(x_70, x_3);
lean_dec(x_70);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_71, x_72);
lean_dec(x_71);
x_74 = lean_nat_sub(x_65, x_57);
lean_dec(x_57);
lean_dec(x_65);
x_75 = lean_nat_div(x_74, x_3);
lean_dec(x_3);
lean_dec(x_74);
x_76 = lean_nat_add(x_75, x_72);
lean_dec(x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_14);
lean_ctor_set(x_12, 1, x_77);
lean_ctor_set(x_12, 0, x_73);
lean_ctor_set(x_11, 0, x_25);
lean_ctor_set(x_10, 0, x_16);
x_78 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_10, x_15);
lean_ctor_set(x_2, 1, x_78);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_15);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_2);
return x_79;
}
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_12, 0);
lean_inc(x_80);
lean_dec(x_12);
x_81 = lean_ctor_get(x_13, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_82 = x_13;
} else {
 lean_dec_ref(x_13);
 x_82 = lean_box(0);
}
x_83 = lean_nat_dec_eq(x_17, x_28);
lean_dec(x_28);
lean_dec(x_17);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_84 = lean_box(0);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_85 = lean_unsigned_to_nat(2u);
x_86 = lean_nat_mul(x_85, x_4);
lean_dec(x_4);
x_87 = lean_nat_add(x_18, x_86);
lean_dec(x_18);
x_88 = lean_nat_dec_le(x_80, x_87);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_3);
x_89 = lean_box(0);
return x_89;
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_nat_add(x_19, x_86);
lean_dec(x_86);
lean_dec(x_19);
x_91 = lean_nat_dec_le(x_81, x_90);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_3);
x_92 = lean_box(0);
return x_92;
}
else
{
uint8_t x_93; 
x_93 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_15, x_21);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_free_object(x_11);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_3);
x_94 = lean_box(0);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_95 = lean_nat_sub(x_87, x_80);
lean_dec(x_80);
lean_dec(x_87);
x_96 = lean_nat_div(x_95, x_3);
lean_dec(x_95);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_add(x_96, x_97);
lean_dec(x_96);
x_99 = lean_nat_sub(x_90, x_81);
lean_dec(x_81);
lean_dec(x_90);
x_100 = lean_nat_div(x_99, x_3);
lean_dec(x_3);
lean_dec(x_99);
x_101 = lean_nat_add(x_100, x_97);
lean_dec(x_100);
if (lean_is_scalar(x_82)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_82;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_14);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_98);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_11, 1, x_103);
lean_ctor_set(x_11, 0, x_25);
lean_ctor_set(x_10, 0, x_16);
x_104 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_10, x_15);
lean_ctor_set(x_2, 1, x_104);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_15);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_2);
return x_105;
}
}
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_106 = lean_ctor_get(x_11, 0);
lean_inc(x_106);
lean_dec(x_11);
x_107 = lean_ctor_get(x_12, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_108 = x_12;
} else {
 lean_dec_ref(x_12);
 x_108 = lean_box(0);
}
x_109 = lean_ctor_get(x_13, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_110 = x_13;
} else {
 lean_dec_ref(x_13);
 x_110 = lean_box(0);
}
x_111 = lean_nat_dec_eq(x_17, x_106);
lean_dec(x_106);
lean_dec(x_17);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_box(0);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_unsigned_to_nat(2u);
x_114 = lean_nat_mul(x_113, x_4);
lean_dec(x_4);
x_115 = lean_nat_add(x_18, x_114);
lean_dec(x_18);
x_116 = lean_nat_dec_le(x_107, x_115);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_3);
x_117 = lean_box(0);
return x_117;
}
else
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_nat_add(x_19, x_114);
lean_dec(x_114);
lean_dec(x_19);
x_119 = lean_nat_dec_le(x_109, x_118);
if (x_119 == 0)
{
lean_object* x_120; 
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_3);
x_120 = lean_box(0);
return x_120;
}
else
{
uint8_t x_121; 
x_121 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_15, x_21);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_118);
lean_dec(x_115);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_free_object(x_10);
lean_dec(x_25);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_3);
x_122 = lean_box(0);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_123 = lean_nat_sub(x_115, x_107);
lean_dec(x_107);
lean_dec(x_115);
x_124 = lean_nat_div(x_123, x_3);
lean_dec(x_123);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_124, x_125);
lean_dec(x_124);
x_127 = lean_nat_sub(x_118, x_109);
lean_dec(x_109);
lean_dec(x_118);
x_128 = lean_nat_div(x_127, x_3);
lean_dec(x_3);
lean_dec(x_127);
x_129 = lean_nat_add(x_128, x_125);
lean_dec(x_128);
if (lean_is_scalar(x_110)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_110;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_14);
if (lean_is_scalar(x_108)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_108;
}
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_25);
lean_ctor_set(x_132, 1, x_131);
lean_ctor_set(x_10, 1, x_132);
lean_ctor_set(x_10, 0, x_16);
x_133 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_10, x_15);
lean_ctor_set(x_2, 1, x_133);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_15);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_2);
return x_134;
}
}
}
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_135 = lean_ctor_get(x_10, 0);
lean_inc(x_135);
lean_dec(x_10);
x_136 = lean_ctor_get(x_11, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_137 = x_11;
} else {
 lean_dec_ref(x_11);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get(x_12, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_139 = x_12;
} else {
 lean_dec_ref(x_12);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_13, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_141 = x_13;
} else {
 lean_dec_ref(x_13);
 x_141 = lean_box(0);
}
x_142 = lean_nat_dec_eq(x_17, x_136);
lean_dec(x_136);
lean_dec(x_17);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_143 = lean_box(0);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_unsigned_to_nat(2u);
x_145 = lean_nat_mul(x_144, x_4);
lean_dec(x_4);
x_146 = lean_nat_add(x_18, x_145);
lean_dec(x_18);
x_147 = lean_nat_dec_le(x_138, x_146);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_free_object(x_2);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_3);
x_148 = lean_box(0);
return x_148;
}
else
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_nat_add(x_19, x_145);
lean_dec(x_145);
lean_dec(x_19);
x_150 = lean_nat_dec_le(x_140, x_149);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec(x_149);
lean_dec(x_146);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_3);
x_151 = lean_box(0);
return x_151;
}
else
{
uint8_t x_152; 
x_152 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_15, x_21);
if (x_152 == 0)
{
lean_object* x_153; 
lean_dec(x_149);
lean_dec(x_146);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_3);
x_153 = lean_box(0);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_154 = lean_nat_sub(x_146, x_138);
lean_dec(x_138);
lean_dec(x_146);
x_155 = lean_nat_div(x_154, x_3);
lean_dec(x_154);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_nat_add(x_155, x_156);
lean_dec(x_155);
x_158 = lean_nat_sub(x_149, x_140);
lean_dec(x_140);
lean_dec(x_149);
x_159 = lean_nat_div(x_158, x_3);
lean_dec(x_3);
lean_dec(x_158);
x_160 = lean_nat_add(x_159, x_156);
lean_dec(x_159);
if (lean_is_scalar(x_141)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_141;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_14);
if (lean_is_scalar(x_139)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_139;
}
lean_ctor_set(x_162, 0, x_157);
lean_ctor_set(x_162, 1, x_161);
if (lean_is_scalar(x_137)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_137;
}
lean_ctor_set(x_163, 0, x_135);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_16);
lean_ctor_set(x_164, 1, x_163);
x_165 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_164, x_15);
lean_ctor_set(x_2, 1, x_165);
lean_ctor_set(x_2, 0, x_164);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_15);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_2);
return x_166;
}
}
}
}
}
}
else
{
uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_167 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_dec(x_2);
x_168 = lean_ctor_get(x_10, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_169 = x_10;
} else {
 lean_dec_ref(x_10);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_11, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_171 = x_11;
} else {
 lean_dec_ref(x_11);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_12, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_173 = x_12;
} else {
 lean_dec_ref(x_12);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_13, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_175 = x_13;
} else {
 lean_dec_ref(x_13);
 x_175 = lean_box(0);
}
x_176 = lean_nat_dec_eq(x_17, x_170);
lean_dec(x_170);
lean_dec(x_17);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
x_177 = lean_box(0);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_178 = lean_unsigned_to_nat(2u);
x_179 = lean_nat_mul(x_178, x_4);
lean_dec(x_4);
x_180 = lean_nat_add(x_18, x_179);
lean_dec(x_18);
x_181 = lean_nat_dec_le(x_172, x_180);
if (x_181 == 0)
{
lean_object* x_182; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_3);
x_182 = lean_box(0);
return x_182;
}
else
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_nat_add(x_19, x_179);
lean_dec(x_179);
lean_dec(x_19);
x_184 = lean_nat_dec_le(x_174, x_183);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_183);
lean_dec(x_180);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_16);
lean_dec(x_3);
x_185 = lean_box(0);
return x_185;
}
else
{
uint8_t x_186; 
x_186 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_15, x_167);
if (x_186 == 0)
{
lean_object* x_187; 
lean_dec(x_183);
lean_dec(x_180);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_16);
lean_dec(x_3);
x_187 = lean_box(0);
return x_187;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_188 = lean_nat_sub(x_180, x_172);
lean_dec(x_172);
lean_dec(x_180);
x_189 = lean_nat_div(x_188, x_3);
lean_dec(x_188);
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_nat_add(x_189, x_190);
lean_dec(x_189);
x_192 = lean_nat_sub(x_183, x_174);
lean_dec(x_174);
lean_dec(x_183);
x_193 = lean_nat_div(x_192, x_3);
lean_dec(x_3);
lean_dec(x_192);
x_194 = lean_nat_add(x_193, x_190);
lean_dec(x_193);
if (lean_is_scalar(x_175)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_175;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_14);
if (lean_is_scalar(x_173)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_173;
}
lean_ctor_set(x_196, 0, x_191);
lean_ctor_set(x_196, 1, x_195);
if (lean_is_scalar(x_171)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_171;
}
lean_ctor_set(x_197, 0, x_168);
lean_ctor_set(x_197, 1, x_196);
if (lean_is_scalar(x_169)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_169;
}
lean_ctor_set(x_198, 0, x_16);
lean_ctor_set(x_198, 1, x_197);
x_199 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_198, x_15);
x_200 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set_uint8(x_200, sizeof(void*)*2, x_15);
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
}
}
}
else
{
lean_object* x_202; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_202 = lean_box(0);
return x_202;
}
}
else
{
lean_object* x_203; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_203 = lean_box(0);
return x_203;
}
}
else
{
lean_object* x_204; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_204 = lean_box(0);
return x_204;
}
}
else
{
lean_object* x_205; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_205 = lean_box(0);
return x_205;
}
}
else
{
lean_object* x_206; 
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_206 = lean_box(0);
return x_206;
}
}
else
{
lean_object* x_207; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_207 = lean_box(0);
return x_207;
}
}
else
{
lean_object* x_208; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_208 = lean_box(0);
return x_208;
}
}
else
{
lean_object* x_209; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_209 = lean_box(0);
return x_209;
}
}
else
{
lean_object* x_210; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_210 = lean_box(0);
return x_210;
}
}
else
{
lean_object* x_211; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_211 = lean_box(0);
return x_211;
}
}
}
LEAN_EXPORT lean_object* tensor_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_dec_ref(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_8 = lean_ctor_get(x_2, 1);
lean_dec(x_8);
x_9 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc(x_3);
x_10 = l_instDecidableEqList___redArg(x_9, x_3, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_3);
x_11 = lean_box(0);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_4, x_7);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_3);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_3, x_4);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_2);
return x_15;
}
}
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
lean_inc(x_16);
lean_dec(x_2);
x_18 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc(x_3);
x_19 = l_instDecidableEqList___redArg(x_18, x_3, x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_3);
x_20 = lean_box(0);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lp_tensor_x2dcore_TensorCore_instDecidableEqDType(x_4, x_17);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lp_tensor_x2dcore_TensorCore_Tensor_zeros___redArg(x_3, x_4);
x_24 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_4);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
}
}
static lean_object* _init_graph_new() {
_start:
{
lean_object* x_1; 
x_1 = lp_tensor_x2dcore_TensorCore_Graph_empty;
return x_1;
}
}
LEAN_EXPORT lean_object* graph_add_input(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
uint8_t x_4; uint8_t x_17; uint8_t x_18; 
x_17 = 0;
x_18 = lean_uint8_dec_eq(x_3, x_17);
if (x_18 == 0)
{
uint8_t x_19; uint8_t x_20; 
x_19 = 1;
x_20 = lean_uint8_dec_eq(x_3, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; 
x_21 = 2;
x_22 = lean_uint8_dec_eq(x_3, x_21);
if (x_22 == 0)
{
uint8_t x_23; uint8_t x_24; 
x_23 = 3;
x_24 = lean_uint8_dec_eq(x_3, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_25 = lean_box(0);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = 3;
x_4 = x_26;
goto block_16;
}
}
else
{
uint8_t x_27; 
x_27 = 2;
x_4 = x_27;
goto block_16;
}
}
else
{
uint8_t x_28; 
x_28 = 1;
x_4 = x_28;
goto block_16;
}
}
else
{
uint8_t x_29; 
x_29 = 0;
x_4 = x_29;
goto block_16;
}
block_16:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_to_list(x_2);
x_6 = lp_tensor_x2dcore_TensorCore_Graph_addInput(x_1, x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
lean_ctor_set(x_6, 1, x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* lp_tensor_x2dcore_TensorCore_FFI_graphAddInput___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = graph_add_input(x_1, x_2, x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_tensor_x2dcore_TensorCore_Graph(uint8_t builtin);
lean_object* initialize_tensor_x2dcore_TensorCore_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_tensor_x2dcore_TensorCore_FFI(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tensor_x2dcore_TensorCore_Graph(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_tensor_x2dcore_TensorCore_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
graph_new = _init_graph_new();
lean_mark_persistent(graph_new);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
