/*
 * tensor_core.h - C interface to Lean TensorCore
 * 
 * This is auto-generated from the @[export] functions in Lean.
 * Python talks to this, not to Lean directly.
 */

#ifndef TENSOR_CORE_H
#define TENSOR_CORE_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque handles - Python can't look inside */
typedef struct TensorHandle* tensor_handle_t;
typedef struct GraphHandle* graph_handle_t;

/* DType tags */
typedef enum {
    DTYPE_F32 = 0,
    DTYPE_F16 = 1,
    DTYPE_BF16 = 2,
    DTYPE_NVFP4 = 3
} dtype_t;

/* Result type for operations that can fail */
typedef struct {
    int success;
    tensor_handle_t handle;
    const char* error;
} tensor_result_t;

/* 
 * Create a tensor from raw data.
 * Returns NULL if validation fails (shape/dtype/size mismatch).
 */
tensor_result_t tensor_create(
    const size_t* shape,
    size_t ndim,
    dtype_t dtype,
    const void* data,
    size_t data_size
);

/* Free a tensor handle */
void tensor_free(tensor_handle_t t);

/* Get tensor properties */
size_t tensor_ndim(tensor_handle_t t);
size_t tensor_shape(tensor_handle_t t, size_t dim);
dtype_t tensor_dtype(tensor_handle_t t);
const void* tensor_data(tensor_handle_t t);
size_t tensor_nbytes(tensor_handle_t t);

/* 
 * Operations - all return NULL on shape mismatch.
 * This is the runtime enforcement of type-level contracts.
 */
tensor_result_t tensor_matmul(tensor_handle_t a, tensor_handle_t b);
tensor_result_t tensor_conv2d(
    tensor_handle_t input,
    tensor_handle_t kernel,
    size_t stride,
    size_t padding
);
tensor_result_t tensor_add(tensor_handle_t a, tensor_handle_t b);
tensor_result_t tensor_relu(tensor_handle_t t);

/* Graph operations */
graph_handle_t graph_new(void);
void graph_free(graph_handle_t g);
int graph_add_input(graph_handle_t g, const size_t* shape, size_t ndim, dtype_t dtype);
int graph_connect(graph_handle_t g, int src_node, int src_port, int dst_node, int dst_port);

#ifdef __cplusplus
}
#endif

#endif /* TENSOR_CORE_H */
