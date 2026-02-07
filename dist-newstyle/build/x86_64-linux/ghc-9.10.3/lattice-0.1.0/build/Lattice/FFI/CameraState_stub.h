#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr frames_equal_ffi(HsDouble a1, HsDouble a2);
extern HsPtr safe_frame_ffi(HsPtr a1, HsDouble a2);
extern HsPtr all_cameras_ffi(HsPtr a1);
extern HsPtr get_camera_ffi(HsPtr a1);
extern HsPtr get_camera_keyframes_ffi(HsPtr a1);
extern HsPtr active_camera_ffi(HsPtr a1);
#if defined(__cplusplus)
}
#endif

