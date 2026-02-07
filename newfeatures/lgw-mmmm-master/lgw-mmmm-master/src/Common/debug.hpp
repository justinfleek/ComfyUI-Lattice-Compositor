#ifndef DEBUG_HPP
#define DEBUG_HPP

#include <iostream>
#include <filesystem>



// Define here for global use
#define USE_DEBUG_OUTSTREAM

#ifdef USE_DEBUG_OUTSTREAM
#define DEBUG_OUTPUT_DISACTIVATED false
#else 
#define DEBUG_OUTPUT_DISACTIVATED true
#endif

#define DEBUG_OUT \
    if constexpr(DEBUG_OUTPUT_DISACTIVATED) {} \
    else std::cerr << "[DB] "

#define DEBUG_TEST_EXIT(cmd, failcmd) \
    if constexpr(DEBUG_OUTPUT_DISACTIVATED) cmd; \
    else if (cmd) { failcmd; exit(EXIT_FAILURE); }

#endif // DEBUG_HPP
