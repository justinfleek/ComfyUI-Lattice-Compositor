#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr frames_equal(HsPtr a1, HsPtr a2);
extern HsPtr get_markers(HsPtr a1);
extern HsPtr get_marker(HsPtr a1, HsPtr a2);
extern HsPtr get_marker_at_frame(HsPtr a1, HsPtr a2);
extern HsPtr get_markers_in_range(HsPtr a1, HsPtr a2, HsPtr a3);
extern HsPtr get_next_marker(HsPtr a1, HsPtr a2);
extern HsPtr get_previous_marker(HsPtr a1, HsPtr a2);
#if defined(__cplusplus)
}
#endif

