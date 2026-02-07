// Define for global use
//#define USE_TIMER

#ifndef TIMER_HPP
#define TIMER_HPP 

#include <chrono>
#include <iostream>
#include <string>

/// @brief Typedef for the chrono
using time_point_t = std::chrono::time_point<std::chrono::system_clock>;

#ifdef USE_TIMER 

#define TIMER_START(name, prefix, depth)                                \
    const std::string timer_prefix_##name(prefix);                  \
    constexpr size_t timer_depth_##name = depth;                        \
    time_point_t timer_start_##name = std::chrono::high_resolution_clock::now(); \
    time_point_t timer_checkpoint_##name = std::chrono::high_resolution_clock::now(); \
    time_point_t timer_new_checkpoint_##name = std::chrono::high_resolution_clock::now(); \
    {

// From last checkpoint
#define TIMER_PRINT_CP(str, name, precision)                     \
    timer_new_checkpoint_##name = std::chrono::high_resolution_clock::now(); \
    for (size_t i = 0; i < timer_depth_##name; ++i) std::cout << "--";               \
    std::cout << ">> " << timer_prefix_##name << str << ": "             \
    << (std::chrono::duration_cast< std::chrono::precision >((timer_new_checkpoint_##name - timer_checkpoint_##name ) ).count()) << std::endl; \
    timer_checkpoint_##name = timer_new_checkpoint_##name

// From last checkpoint + barrier
#define TIMER_PRINT_CP_BARRIER(str, name, precision)             \
    _Pragma("omp barrier")                                              \
    _Pragma("omp single")                                               \
    {                                                                   \
    timer_new_checkpoint_##name = std::chrono::high_resolution_clock::now(); \
    for (size_t i = 0; i < timer_depth_##name; ++i) std::cout << "--";               \
    std::cout << ">> " << timer_prefix_##name << str << ": "                                   \
    << (std::chrono::duration_cast< std::chrono::precision >((timer_new_checkpoint_##name - timer_checkpoint_##name ) ).count()) << std::endl; \
    timer_checkpoint_##name = timer_new_checkpoint_##name;                   \
    }                                                                   \
    _Pragma("omp barrier")                                              \
    
// From the start
#define TIMER_PRINT_TOTAL(str, name, precision)                  \
    for (size_t i = 0; i < timer_depth_##name; ++i) std::cout << "--";               \
    std::cout << ">> " << timer_prefix_##name << str << ": "                                   \
    << (std::chrono::duration_cast< std::chrono::precision >(( std::chrono::high_resolution_clock::now() - timer_start_##name ) ).count()) << std::endl

// Closing timer context
#define TIMER_END(str, name, precision)                          \
    }                                                                   \
    timer_new_checkpoint_##name = std::chrono::high_resolution_clock::now(); \
    for (size_t i = 0; i < timer_depth_##name; ++i) std::cout << "--";               \
    std::cout << ">> " << timer_prefix_##name << str << "(C/T): "                    \
    << (std::chrono::duration_cast< std::chrono::precision >((timer_new_checkpoint_##name - timer_checkpoint_##name ) ).count()) << "/" \
    << (std::chrono::duration_cast< std::chrono::precision >((timer_new_checkpoint_##name - timer_start_##name ) ).count()) << std::endl

typedef std::chrono::microseconds microseconds;
typedef std::chrono::milliseconds milliseconds;
typedef std::chrono::seconds seconds;

#undef USE_TIMER 

#else //


#define TIMER_START(name, prefix, depth)        \
    do { } while(0)
#define TIMER_PRINT_CP(str, name, precision)    \
    do { } while(0)
#define TIMER_PRINT_CP_BARRIER(str, name, precision)    \
    do { } while(0)
#define TIMER_PRINT_TOTAL(str, name, precision) \
    do { } while(0)
#define TIMER_END(str, name, precision)         \
    do { } while(0)

#endif //



// Convenient timer
#define TIMER_MS_START(prefix, depth)   TIMER_START(default_timer_ms, prefix, depth)
#define TIMER_MS_PRINT_CP(str)          TIMER_PRINT_CP(str, default_timer_ms, milliseconds)
#define TIMER_MS_PRINT_CP_BARRIER(str)  TIMER_PRINT_CP_BARRIER(str, default_timer_ms, milliseconds)
//#define TIMER_MS_PRINT(str)             TIMER_PRINT(str, default_timer_ms, milliseconds)
#define TIMER_MS_END                    TIMER_END("", default_timer_ms, milliseconds)   


#endif // TIMER_HPP
