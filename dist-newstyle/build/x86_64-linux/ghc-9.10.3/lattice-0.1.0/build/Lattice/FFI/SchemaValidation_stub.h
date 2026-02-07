#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr validate_non_empty_string(HsPtr a1, HsInt32 a2);
extern HsPtr validate_iso8601_datetime(HsPtr a1);
extern HsPtr validate_base64_or_data_url(HsPtr a1);
extern HsPtr validate_mime_type(HsPtr a1);
extern HsPtr validate_hex_color(HsPtr a1);
extern HsPtr validate_entity_id(HsPtr a1);
extern HsPtr validate_property_path(HsPtr a1);
extern HsPtr validate_filename(HsPtr a1);
extern HsPtr validate_url(HsPtr a1);
extern HsPtr validate_shader_code(HsPtr a1);
extern HsPtr validate_bounded_array(HsPtr a1, HsInt32 a2);
extern HsPtr validate_non_empty_array(HsPtr a1);
extern HsPtr validate_json_serializable(HsPtr a1);
extern HsInt32 update_validation_limits(HsPtr a1);
extern HsInt32 get_max_dimension(void);
extern HsInt32 get_max_frame_count(void);
extern HsInt32 get_max_array_length(void);
#if defined(__cplusplus)
}
#endif

