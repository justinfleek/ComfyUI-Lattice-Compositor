#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr active_backend_ffi(HsPtr a1);
extern HsPtr gpu_compute_active_ffi(HsPtr a1);
extern HsPtr backend_description_ffi(HsPtr a1);
extern HsPtr supports_high_particle_counts_ffi(HsPtr a1);
extern HsPtr sanitize_max_particles_per_layer_ffi(HsPtr a1);
extern HsPtr sanitize_cache_checkpoint_interval_ffi(HsPtr a1);
extern HsPtr sanitize_max_cache_memory_mb_ffi(HsPtr a1);
extern HsPtr sanitize_target_fps_ffi(HsPtr a1);
#if defined(__cplusplus)
}
#endif

