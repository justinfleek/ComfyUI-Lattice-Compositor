/*
 * AUTO-EXTRACTED FROM LEAN PROOFS
 *
 * Every type here has a corresponding Extractable instance in Lean
 * with a proven roundtrip theorem. Validation functions mirror
 * the Lean type constraints.
 *
 * DO NOT EDIT - regenerate with `lake exe extract c`
 */

#ifndef TENSOR_CORE_TYPES_H
#define TENSOR_CORE_TYPES_H

#include <stdbool.h>

#ifdef __cplusplus
extern "C" {
#endif


typedef struct {
    float x;
    float y;
    float z;
} Point3;

typedef struct {
    float x;
    float y;
    float z;
} Vec3;

typedef struct {
    float r;  /* must be in [0,1] */
    float g;  /* must be in [0,1] */
    float b;  /* must be in [0,1] */
} ColorRGB;

static inline bool ColorRGB_valid(ColorRGB c) {
    return c.r >= 0 && c.r <= 1 
        && c.g >= 0 && c.g <= 1 
        && c.b >= 0 && c.b <= 1;
}

typedef struct {
    Point3 position;
    Vec3 normal;
} Vertex;

typedef struct {
    float matrix[16];
} Transform;

#ifdef __cplusplus
}
#endif

#endif /* TENSOR_CORE_TYPES_H */
