cmake_minimum_required(VERSION 3.5.0)

set(CMAKE_CXX_STANDARD 17)

project(${EXEC_TOPO_VIEWER} CXX)

file(GLOB_RECURSE sources
	${CMAKE_CURRENT_SOURCE_DIR}/*.c
	${CMAKE_CURRENT_SOURCE_DIR}/*.cpp
	${CMAKE_CURRENT_SOURCE_DIR}/*.h
)

file(GLOB imgui_sources
	${CMAKE_CURRENT_SOURCE_DIR}/../utilities/imgui/*.cpp
	${CMAKE_CURRENT_SOURCE_DIR}/../utilities/imgui/*.h
	${CMAKE_CURRENT_SOURCE_DIR}/../utilities/imgui/backends/imgui_impl_glfw*
	${CMAKE_CURRENT_SOURCE_DIR}/../utilities/imgui/backends/imgui_impl_opengl3*
	${CMAKE_CURRENT_SOURCE_DIR}/../utilities/imgui/misc/cpp/*.cpp
	${CMAKE_CURRENT_SOURCE_DIR}/../utilities/imgui/misc/cpp/*.h
)

file(GLOB shader_sources
	${CMAKE_CURRENT_SOURCE_DIR}/../../res/shaders/*
)


add_executable(${EXEC_TOPO_VIEWER}
	${sources} ${imgui_sources} ${shader_sources}
)

set_source_files_properties(${shader_sources} PROPERTIES HEADER_FILE_ONLY TRUE)


target_include_directories(${EXEC_TOPO_VIEWER} PUBLIC
	${CMAKE_CURRENT_SOURCE_DIR}
	${CMAKE_CURRENT_SOURCE_DIR}/glad
	${CMAKE_CURRENT_SOURCE_DIR}/../utilities/imgui
	${CMAKE_CURRENT_SOURCE_DIR}/../utilities
)

target_link_libraries(${EXEC_TOPO_VIEWER} glfw TopoFixer fpng)

source_group(TREE ${CMAKE_CURRENT_SOURCE_DIR} FILES ${sources})
source_group(TREE ${CMAKE_CURRENT_SOURCE_DIR}/../utilities FILES ${imgui_sources})
source_group(TREE ${CMAKE_CURRENT_SOURCE_DIR}/../../res FILES ${shader_sources})
