// Lean compiler output
// Module: Compass
// Imports: public import Init public import Compass.Core public import Compass.Permissions public import Compass.Auth public import Compass.Tools public import Compass.Audit public import Compass.Jobs public import Compass.Router public import Compass.Budget public import Compass.BudgetState public import Compass.Flags public import Compass.RateLimiter public import Compass.Campaign public import Compass.Emit
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Compass_Core(uint8_t builtin);
lean_object* initialize_Compass_Permissions(uint8_t builtin);
lean_object* initialize_Compass_Auth(uint8_t builtin);
lean_object* initialize_Compass_Tools(uint8_t builtin);
lean_object* initialize_Compass_Audit(uint8_t builtin);
lean_object* initialize_Compass_Jobs(uint8_t builtin);
lean_object* initialize_Compass_Router(uint8_t builtin);
lean_object* initialize_Compass_Budget(uint8_t builtin);
lean_object* initialize_Compass_BudgetState(uint8_t builtin);
lean_object* initialize_Compass_Flags(uint8_t builtin);
lean_object* initialize_Compass_RateLimiter(uint8_t builtin);
lean_object* initialize_Compass_Campaign(uint8_t builtin);
lean_object* initialize_Compass_Emit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Compass(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Permissions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Auth(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Tools(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Audit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Jobs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Router(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Budget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_BudgetState(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Flags(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_RateLimiter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Campaign(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Compass_Emit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
