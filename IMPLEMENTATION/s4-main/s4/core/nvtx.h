// s4 // core/nvtx.h
#pragma once

// NVTX is optional. If unavailable, these helpers compile to no-ops.
//
// Enable by defining S4_ENABLE_NVTX and ensuring nvtx headers/libs are present.

#if defined(S4_ENABLE_NVTX)
    #include <nvtx3/nvToolsExt.h>
#endif

namespace s4::core {

class nvtx_range final {
public:
    explicit nvtx_range(const char* message) noexcept {
#if defined(S4_ENABLE_NVTX)
        nvtxRangePushA(message);
#else
        (void)message;
#endif
    }

    ~nvtx_range() {
#if defined(S4_ENABLE_NVTX)
        nvtxRangePop();
#endif
    }

    nvtx_range(const nvtx_range&) = delete;
    nvtx_range(nvtx_range&&) = delete;
    auto operator=(const nvtx_range&) -> nvtx_range& = delete;
    auto operator=(nvtx_range&&) -> nvtx_range& = delete;
};

}  // namespace s4::core
