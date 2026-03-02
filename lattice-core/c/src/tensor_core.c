/*
 * tensor_core.c - C shim for Lean FFI
 * 
 * In a full implementation, this would link against the Lean runtime
 * and call the @[export] functions. For this demo, we implement
 * the validation logic in C to show the pattern.
 */

#include "tensor_core.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* Internal tensor representation */
struct TensorHandle {
    size_t* shape;
    size_t ndim;
    dtype_t dtype;
    void* data;
    size_t nbytes;
};

/* Internal graph representation */
struct GraphHandle {
    int next_id;
    /* In real impl: nodes, edges, etc */
};

static size_t dtype_sizeof(dtype_t dt) {
    switch (dt) {
        case DTYPE_F32: return 4;
        case DTYPE_F16: return 2;
        case DTYPE_BF16: return 2;
        case DTYPE_NVFP4: return 1;  /* simplified */
        default: return 0;
    }
}

static size_t compute_numel(const size_t* shape, size_t ndim) {
    size_t numel = 1;
    for (size_t i = 0; i < ndim; i++) {
        numel *= shape[i];
    }
    return numel;
}

tensor_result_t tensor_create(
    const size_t* shape,
    size_t ndim,
    dtype_t dtype,
    const void* data,
    size_t data_size
) {
    tensor_result_t result = {0, NULL, NULL};
    
    /* Validate: all dims positive */
    for (size_t i = 0; i < ndim; i++) {
        if (shape[i] == 0) {
            result.error = "All dimensions must be positive";
            return result;
        }
    }
    
    /* Validate: data size matches shape * dtype */
    size_t expected = compute_numel(shape, ndim) * dtype_sizeof(dtype);
    if (data_size != expected) {
        result.error = "Data size does not match shape * dtype size";
        return result;
    }
    
    /* All checks pass - create handle */
    struct TensorHandle* t = malloc(sizeof(struct TensorHandle));
    if (!t) {
        result.error = "Allocation failed";
        return result;
    }
    
    t->shape = malloc(ndim * sizeof(size_t));
    t->data = malloc(data_size);
    if (!t->shape || !t->data) {
        free(t->shape);
        free(t->data);
        free(t);
        result.error = "Allocation failed";
        return result;
    }
    
    memcpy(t->shape, shape, ndim * sizeof(size_t));
    memcpy(t->data, data, data_size);
    t->ndim = ndim;
    t->dtype = dtype;
    t->nbytes = data_size;
    
    result.success = 1;
    result.handle = t;
    return result;
}

void tensor_free(tensor_handle_t t) {
    if (t) {
        free(t->shape);
        free(t->data);
        free(t);
    }
}

size_t tensor_ndim(tensor_handle_t t) { return t->ndim; }
size_t tensor_shape(tensor_handle_t t, size_t dim) { 
    return dim < t->ndim ? t->shape[dim] : 0; 
}
dtype_t tensor_dtype(tensor_handle_t t) { return t->dtype; }
const void* tensor_data(tensor_handle_t t) { return t->data; }
size_t tensor_nbytes(tensor_handle_t t) { return t->nbytes; }

tensor_result_t tensor_matmul(tensor_handle_t a, tensor_handle_t b) {
    tensor_result_t result = {0, NULL, NULL};
    
    /* Shape check: [m, k] @ [k, n] -> [m, n] */
    if (a->ndim != 2 || b->ndim != 2) {
        result.error = "Matmul requires 2D tensors";
        return result;
    }
    
    if (a->shape[1] != b->shape[0]) {
        result.error = "Inner dimensions must match for matmul";
        return result;
    }
    
    if (a->dtype != b->dtype) {
        result.error = "Dtype mismatch";
        return result;
    }
    
    /* Create output tensor */
    size_t out_shape[2] = {a->shape[0], b->shape[1]};
    size_t out_size = out_shape[0] * out_shape[1] * dtype_sizeof(a->dtype);
    void* out_data = calloc(1, out_size);  /* zeros for demo */
    
    if (!out_data) {
        result.error = "Allocation failed";
        return result;
    }
    
    /* In real impl: call cuBLAS here */
    
    return tensor_create(out_shape, 2, a->dtype, out_data, out_size);
}

tensor_result_t tensor_conv2d(
    tensor_handle_t input,
    tensor_handle_t kernel,
    size_t stride,
    size_t padding
) {
    tensor_result_t result = {0, NULL, NULL};
    
    /* Shape check: input [b, c_in, h, w], kernel [c_out, c_in, kh, kw] */
    if (input->ndim != 4 || kernel->ndim != 4) {
        result.error = "Conv2D requires 4D tensors";
        return result;
    }
    
    if (input->shape[1] != kernel->shape[1]) {
        result.error = "Input channels must match kernel input channels";
        return result;
    }
    
    size_t h = input->shape[2], w = input->shape[3];
    size_t kh = kernel->shape[2], kw = kernel->shape[3];
    
    if (h + 2 * padding < kh || w + 2 * padding < kw) {
        result.error = "Input too small for kernel size";
        return result;
    }
    
    if (input->dtype != kernel->dtype) {
        result.error = "Dtype mismatch";
        return result;
    }
    
    /* Compute output shape */
    size_t out_shape[4] = {
        input->shape[0],
        kernel->shape[0],
        (h + 2 * padding - kh) / stride + 1,
        (w + 2 * padding - kw) / stride + 1
    };
    
    size_t out_size = compute_numel(out_shape, 4) * dtype_sizeof(input->dtype);
    void* out_data = calloc(1, out_size);
    
    if (!out_data) {
        result.error = "Allocation failed";
        return result;
    }
    
    /* In real impl: call cuDNN here */
    
    return tensor_create(out_shape, 4, input->dtype, out_data, out_size);
}

tensor_result_t tensor_add(tensor_handle_t a, tensor_handle_t b) {
    tensor_result_t result = {0, NULL, NULL};
    
    /* Shapes must match exactly */
    if (a->ndim != b->ndim) {
        result.error = "Dimension count mismatch";
        return result;
    }
    
    for (size_t i = 0; i < a->ndim; i++) {
        if (a->shape[i] != b->shape[i]) {
            result.error = "Shape mismatch";
            return result;
        }
    }
    
    if (a->dtype != b->dtype) {
        result.error = "Dtype mismatch";
        return result;
    }
    
    void* out_data = calloc(1, a->nbytes);
    if (!out_data) {
        result.error = "Allocation failed";
        return result;
    }
    
    return tensor_create(a->shape, a->ndim, a->dtype, out_data, a->nbytes);
}

tensor_result_t tensor_relu(tensor_handle_t t) {
    void* out_data = calloc(1, t->nbytes);
    if (!out_data) {
        tensor_result_t result = {0, NULL, "Allocation failed"};
        return result;
    }
    return tensor_create(t->shape, t->ndim, t->dtype, out_data, t->nbytes);
}

graph_handle_t graph_new(void) {
    struct GraphHandle* g = malloc(sizeof(struct GraphHandle));
    if (g) {
        g->next_id = 0;
    }
    return g;
}

void graph_free(graph_handle_t g) {
    free(g);
}

int graph_add_input(graph_handle_t g, const size_t* shape, size_t ndim, dtype_t dtype) {
    (void)shape; (void)ndim; (void)dtype;
    return g->next_id++;
}

int graph_connect(graph_handle_t g, int src_node, int src_port, int dst_node, int dst_port) {
    (void)g; (void)src_node; (void)src_port; (void)dst_node; (void)dst_port;
    /* In real impl: validate shapes match, add edge */
    return 0;
}
