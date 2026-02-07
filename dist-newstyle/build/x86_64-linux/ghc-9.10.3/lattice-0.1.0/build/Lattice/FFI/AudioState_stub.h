#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr is_loaded(HsPtr a1);
extern HsPtr is_loading(HsPtr a1);
extern HsPtr has_error(HsPtr a1);
extern HsPtr duration(HsPtr a1);
extern HsPtr bpm(HsPtr a1);
extern HsPtr frame_count(HsPtr a1);
extern HsPtr has_audio_buffer(HsPtr a1);
extern HsPtr get_bpm(HsPtr a1);
extern HsPtr available_stems(HsPtr a1);
extern HsPtr has_stems(HsPtr a1);
extern HsPtr get_active_stem_name(HsPtr a1);
extern HsPtr active_analysis(HsPtr a1);
extern HsPtr active_buffer(HsPtr a1);
#if defined(__cplusplus)
}
#endif

