#==========================================
# Project.
#==========================================

project(supertopofixer)


#==========================================
# CMake options.
#==========================================

cmake_minimum_required(VERSION 3.15)
#set(CMAKE_CXX_STANDARD 11)
#set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_POSITION_INDEPENDENT_CODE TRUE) 

set (CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})
set (CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR})


#==========================================
#Building mode handling.
#==========================================
if (NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE DEBUG)
    set(CMAKE_CONFIGURATION_TYPES Debug)
else()
    set(CMAKE_CONFIGURATION_TYPES Release)
endif()
message("Building mode: " ${CMAKE_BUILD_TYPE})



#==========================================
# Project options.
#==========================================

option(ENABLE_VIEWER         "TopoFixer with GUI"        ON)
option(ENABLE_LEGACY_VIEWER  "TopoFixer with Legacy GUI" OFF)
option(USE_LEGACY_EXEC_NAMES "Old naming for backward compatibility with scripts" OFF)
option(ENABLE_TESTS "Build tests" ON)


#==========================================
# Dependencies.
#==========================================

if (ENABLE_TESTS) 
	include(CTest)
	enable_testing()
endif ()

find_package(OpenMP)
find_package(ZLIB REQUIRED)

add_subdirectory(abseil-cpp)
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/utilities/triangle)
add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/src/utilities/fpng)
add_subdirectory(src)

if (ENABLE_LEGACY_VIEWER)
	find_package(OpenGL REQUIRED)
	find_package(GLUT REQUIRED)
	find_package(GLEW REQUIRED)
	include_directories( ${OPENGL_INCLUDE_DIRS}  ${GLUT_INCLUDE_DIRS}  ${GLEW_INCLUDE_DIRS})
endif ()



#==========================================
# Execs.
#==========================================

if (USE_LEGACY_EXEC_NAMES)
        set(EXEC_TOPO_FIXER mesh_reconstruction_no_visual)
        set(EXEC_TOPO_VIEWER_LEG mesh_reconstruction)
else()
        set(EXEC_TOPO_FIXER TopoFixer)
        set(EXEC_TOPO_VIEWER_LEG TopoFixerViewerLegacy)
endif()
set(EXEC_TOPO_VIEWER TopoFixerViewer)


## Topo fixer - command line
add_executable(${EXEC_TOPO_FIXER}_exec
	src/binaries/fixer_only.cpp
)
target_include_directories(${EXEC_TOPO_FIXER}_exec PUBLIC ${CMAKE_CURRENT_SOURCE_DIR} )
target_link_libraries(${EXEC_TOPO_FIXER}_exec TopoFixer)

set_property(TARGET ${EXEC_TOPO_FIXER}_exec PROPERTY VS_DEBUGGER_WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}")
set_property(TARGET ${EXEC_TOPO_FIXER}_exec PROPERTY WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}")
# Avoid conflict name if name == TopoFixer
if (UNIX)
        set_property(TARGET ${EXEC_TOPO_FIXER}_exec PROPERTY OUTPUT_NAME ${EXEC_TOPO_FIXER})
elseif(MSVC)
        set_property(TARGET ${EXEC_TOPO_FIXER}_exec PROPERTY RUNTIME_OUTPUT_NAME ${EXEC_TOPO_FIXER})
endif()
  

## Topo fixer - legacy viewer
if (ENABLE_LEGACY_VIEWER)
	add_executable(${EXEC_TOPO_VIEWER_LEG}
		src/binaries/fixer_with_render.cpp
	)
	target_include_directories(${EXEC_TOPO_VIEWER_LEG} PUBLIC ${CMAKE_CURRENT_SOURCE_DIR} )
	target_link_libraries(${EXEC_TOPO_VIEWER_LEG} TopoFixerRender)

	set_property(TARGET ${EXEC_TOPO_VIEWER_LEG} PROPERTY VS_DEBUGGER_WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}")
	set_property(TARGET ${EXEC_TOPO_VIEWER_LEG} PROPERTY WORKING_DIRECTORY "${CMAKE_SOURCE_DIR}")
endif ()
# target_compile_options(${EXEC_TOPO_VIEWER_LEG} PRIVATE $<$<CONFIG:Debug>:-fsanitize=address>)
# target_link_options(${EXEC_TOPO_VIEWER_LEG} PRIVATE $<$<CONFIG:Debug>:-fsanitize=address>)

## Topo fixer - new viewer
if (ENABLE_VIEWER)
	set(GLFW_BUILD_DOCS OFF CACHE BOOL "" FORCE)
	set(GLFW_BUILD_TESTS OFF CACHE BOOL "" FORCE)
	set(GLFW_BUILD_EXAMPLES OFF CACHE BOOL "" FORCE)
	add_subdirectory(src/utilities/glfw-3.4)
	add_subdirectory(src/viewer)
endif ()
