#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr compute_hash(HsPtr a1, HsInt32 a2);
extern HsInt32 verify_hash(HsPtr a1, HsPtr a2);
extern HsPtr validate_decomposition_params(HsPtr a1);
#if defined(__cplusplus)
}
#endif

