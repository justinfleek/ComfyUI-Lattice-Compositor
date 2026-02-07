#==========================================
#Project options.
#==========================================

cmake_minimum_required(VERSION 3.10)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON CACHE INTERNAL "")
if(CMAKE_EXPORT_COMPILE_COMMANDS)
  set(CMAKE_CXX_STANDARD_INCLUDE_DIRECTORIES
      ${CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES})
endif()
set(CMAKE_BUILD_RPATH_USE_ORIGIN on)


#==========================================
#Project name.
#==========================================
project(MyMPM)

#==========================================
#Building options.
#==========================================

set(CMAKE_CXX_STANDARD 20)
if(UNIX)
    #set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++0x -Wall -fopenmp -Wno-deprecated")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -fopenmp ")
    # Silence bullet warnings
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-double-promotion -Wno-unused-parameter")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-sign-compare -Wno-old-style-cast ")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wno-unknown-pragmas -Wno-narrowing ")
    set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -DDEBUG -g")
endif()

#==========================================
#Building mode handling.
#==========================================
if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Debug)
    set(CMAKE_CONFIGURATION_TYPES Debug)
else()
    set(CMAKE_CONFIGURATION_TYPES Release)
endif()
message("Building mode: " ${CMAKE_BUILD_TYPE})

#==========================================
#Libraries.
#==========================================

set(CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/modules/" ${CMAKE_MODULE_PATH})
set(CLI_APPLICATION_ONLY off)

add_subdirectory(extern)


#==============================================
#Project sources.
#==============================================

include_directories("${PROJECT_SOURCE_DIR}/src")
add_subdirectory(src)
