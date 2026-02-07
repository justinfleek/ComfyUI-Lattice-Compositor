#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr has_selection(HsPtr a1);
extern HsPtr has_multiple_selected(HsPtr a1);
extern HsPtr has_keyframe_selection(HsPtr a1);
extern HsPtr has_control_point_selection(HsPtr a1);
extern HsPtr single_selected_layer_id(HsPtr a1);
extern HsPtr selected_control_point_count(HsPtr a1);
extern HsPtr is_layer_selected(HsPtr a1, HsPtr a2);
extern HsPtr is_keyframe_selected(HsPtr a1, HsPtr a2);
extern HsPtr is_control_point_selected(HsPtr a1, HsPtr a2, HsInt32 a3);
extern HsPtr get_selected_control_points_for_layer(HsPtr a1, HsPtr a2);
extern HsPtr compute_range_selection(HsPtr a1, HsPtr a2, HsPtr a3);
extern HsPtr compute_layer_above_selection(HsPtr a1, HsPtr a2);
extern HsPtr compute_layer_below_selection(HsPtr a1, HsPtr a2);
#if defined(__cplusplus)
}
#endif

