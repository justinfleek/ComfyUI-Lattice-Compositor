## Rapidjson
if (NOT RAPIDJSON_INCLUDEDIR)
  set(RAPIDJSON_INCLUDEDIR "${CMAKE_CURRENT_SOURCE_DIR}/rapidjson/include")
endif()
find_package(rapidjson REQUIRED)
include_directories("${RAPIDJSON_INCLUDE_DIRS}")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${RAPIDJSON_CXX_FLAGS}")

## Eigen3
find_package(Eigen3)
# add_subdirectory(eigen-3.4.0)

## ImGUI
set(WITH_IMGUI ON CACHE BOOL "" FORCE)
set(ImGui_INCLUDE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/imgui")
set(imgui_DIR "${CMAKE_CURRENT_SOURCE_DIR}/imgui" CACHE PATH "" FORCE)
set(ImGui_imgui_SOURCE "${ImGui_INCLUDE_DIR}/imgui.cpp" CACHE FILEPATH "" FORCE)
set(ImGui_imgui_widgets_SOURCE "${ImGui_INCLUDE_DIR}/imgui_widgets.cpp" CACHE FILEPATH "" FORCE)
set(ImGui_imgui_draw_SOURCE "${ImGui_INCLUDE_DIR}/imgui_draw.cpp" CACHE FILEPATH "" FORCE)
set(ImGui_imgui_demo_SOURCE "${ImGui_INCLUDE_DIR}/imgui_demo.cpp" CACHE FILEPATH "" FORCE)
set(ImGui_imgui_tables_SOURCE "${ImGui_INCLUDE_DIR}/imgui_tables.cpp" CACHE FILEPATH "" FORCE)

## Corrade
set(CORRADE_BUILD_STATIC ON CACHE BOOL "" FORCE)
add_subdirectory(corrade EXCLUDE_FROM_ALL)

## Magnum
set(MAGNUM_WITH_EIGEN ON CACHE BOOL "" FORCE)
if(NOT CLI_APPLICATION_ONLY)
	set(MAGNUM_WITH_GLFWAPPLICATION ON CACHE BOOL "" FORCE)
endif()
set(MAGNUM_WITH_WINDOWLESSEGLAPPLICATION ON CACHE BOOL "" FORCE)
set(MAGNUM_WITH_IMGUI ON CACHE BOOL "" FORCE)
set(MAGNUM_BUILD_STATIC ON CACHE BOOL "" FORCE)
set(MAGNUM_BUILD_PLUGINS_STATIC ON CACHE BOOL "" FORCE)
set(MAGNUM_WITH_PNGIMAGECONVERTER ON CACHE BOOL "" FORCE)
set(MAGNUM_WITH_PNGIMPORTER ON CACHE BOOL "" FORCE)
set(MAGNUM_WITH_OBJIMPORTER ON CACHE BOOL "" FORCE)
add_subdirectory(magnum EXCLUDE_FROM_ALL)
add_subdirectory(magnum-integration EXCLUDE_FROM_ALL)
add_subdirectory(magnum-plugins EXCLUDE_FROM_ALL)


## libigl
add_subdirectory(libigl)
set(LIBIGL_INCLUDE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/libigl/include" CACHE BOOL "" FORCE)

# add_subdirectory(cnpy)
# set_property(TARGET cnpy APPEND PROPERTY INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})

add_subdirectory(frictionfrenzy)
set(FRICTION_FRENZY_INCLUDE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/frictionfrenzy" CACHE FILEPATH "" FORCE)
include_directories(${CMAKE_CURRENT_SOURCE}/frictionfrenzy)
set_property(TARGET __ff_FrictionFrenzy APPEND PROPERTY 
	INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR}/frictionfrenzy)
