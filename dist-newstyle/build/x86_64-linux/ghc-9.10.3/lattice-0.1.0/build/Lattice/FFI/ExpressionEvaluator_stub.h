#include <HsFFI.h>
#if defined(__cplusplus)
extern "C" {
#endif
extern HsPtr time_ramp(HsPtr a1);
extern HsPtr periodic(HsPtr a1);
extern HsPtr sawtooth(HsPtr a1);
extern HsPtr triangle(HsPtr a1);
extern HsPtr square(HsPtr a1);
extern HsPtr sine(HsPtr a1);
extern HsPtr pulse(HsPtr a1);
extern HsPtr lerp(HsPtr a1);
extern HsPtr clamp(HsPtr a1);
extern HsPtr map_range(HsPtr a1);
extern HsPtr normalize(HsPtr a1);
extern HsPtr smoothstep(HsPtr a1);
extern HsPtr smootherstep(HsPtr a1);
extern HsPtr mod_safe(HsPtr a1);
extern HsPtr distance(HsPtr a1);
extern HsPtr angle_between(HsPtr a1);
extern HsPtr degrees_to_radians(HsPtr a1);
extern HsPtr radians_to_degrees(HsPtr a1);
extern HsPtr seed_random(HsPtr a1);
extern HsPtr gauss_random(HsPtr a1);
extern HsPtr expression_ease(HsPtr a1);
extern HsPtr expression_ease_in(HsPtr a1);
extern HsPtr expression_ease_out(HsPtr a1);
#if defined(__cplusplus)
}
#endif

