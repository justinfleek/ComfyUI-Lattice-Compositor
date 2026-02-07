#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr calculate_max_depth(HsPtr a1, HsInt32 a2);
extern HsPtr validate_expressions(HsPtr a1, HsPtr a2);
extern HsPtr validate_single_expression(HsPtr a1, HsPtr a2);
extern HsPtr validate_numeric_bounds(HsPtr a1, HsPtr a2);
extern HsPtr validate_paths(HsPtr a1, HsPtr a2);
extern HsPtr count_layers(HsPtr a1);
extern HsPtr validate_string_lengths(HsPtr a1, HsPtr a2);
extern HsPtr validate_array_lengths(HsPtr a1, HsPtr a2);
extern HsInt32 validate_project_id(HsPtr a1);
#if defined(__cplusplus)
}
#endif

