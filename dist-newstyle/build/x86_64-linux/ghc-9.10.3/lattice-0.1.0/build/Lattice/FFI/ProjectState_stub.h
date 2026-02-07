#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr get_open_compositions(HsPtr a1, HsPtr a2);
extern HsPtr get_breadcrumb_path(HsPtr a1, HsPtr a2);
extern HsPtr get_active_composition(HsPtr a1, HsPtr a2);
extern HsPtr get_active_composition_layers(HsPtr a1, HsPtr a2);
extern HsPtr get_width(HsPtr a1, HsPtr a2);
extern HsPtr get_height(HsPtr a1, HsPtr a2);
extern HsPtr get_frame_count(HsPtr a1, HsPtr a2);
extern HsPtr get_fps(HsPtr a1, HsPtr a2);
extern HsPtr get_duration(HsPtr a1, HsPtr a2);
extern HsPtr get_background_color(HsPtr a1, HsPtr a2);
extern HsPtr get_current_time(HsPtr a1, HsPtr a2);
extern HsPtr has_project(HsPtr a1);
extern HsPtr find_used_asset_ids(HsPtr a1);
extern HsPtr get_extension_for_asset(HsPtr a1);
extern HsPtr create_default_project(HsPtr a1);
#if defined(__cplusplus)
}
#endif

