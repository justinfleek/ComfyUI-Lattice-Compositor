#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr calculate_time_stretch_ffi(HsDouble a1, HsDouble a2);
extern HsPtr calculate_video_frame_count_ffi(HsDouble a1, HsDouble a2);
extern HsPtr calculate_stretched_duration_ffi(HsDouble a1, HsDouble a2, HsDouble a3);
extern HsPtr check_fps_mismatch_ffi(HsDouble a1, HsDouble a2, HsDouble a3);
extern HsPtr calculate_video_out_point_ffi(HsInt32 a1, HsInt32 a2);
#if defined(__cplusplus)
}
#endif

