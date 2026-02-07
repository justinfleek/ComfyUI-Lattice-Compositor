#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr get_default_limits(void);
extern HsPtr validate_limit(HsPtr a1, HsPtr a2);
extern HsPtr clamp_limit(HsPtr a1, HsPtr a2);
#if defined(__cplusplus)
}
#endif

