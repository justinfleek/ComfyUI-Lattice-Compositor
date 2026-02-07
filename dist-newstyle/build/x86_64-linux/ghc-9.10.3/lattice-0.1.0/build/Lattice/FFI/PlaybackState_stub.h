#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr playing(HsPtr a1);
extern HsPtr has_work_area(HsPtr a1);
extern HsPtr effective_start_frame(HsPtr a1);
extern HsPtr effective_end_frame(HsPtr a1, HsPtr a2);
extern HsPtr clamp_frame(HsPtr a1, HsPtr a2);
extern HsPtr step_forward_frame(HsPtr a1, HsPtr a2);
extern HsPtr step_backward_frame(HsPtr a1);
#if defined(__cplusplus)
}
#endif

