option(SSE "SSE 4.1 support" FALSE)

if (SSE)
	message("-- fpng SSE enabled")
else()
	message("-- fpng SSE disabled")
endif()


add_library(fpng STATIC fpng.cpp)
if (SSE)
    target_compile_definitions(fpng PRIVATE "FPNG_NO_SSE=0")
    target_compile_options(fpng PUBLIC "-msse4.1 -mpclmul")
else()
    target_compile_definitions(fpng PRIVATE "FPNG_NO_SSE")
endif()
target_include_directories(fpng INTERFACE ${CMAKE_CURRENT_SOURCE_DIR})


