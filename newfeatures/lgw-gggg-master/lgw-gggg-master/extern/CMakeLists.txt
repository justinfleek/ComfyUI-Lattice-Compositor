
#Eigen: always use version 3.4
message(STATUS "Third-party: creating target 'Eigen3::Eigen'")
message(${EIGEN_BUILD_PATH})
find_package (Eigen3 3.4 REQUIRED)

set(MAGNUM_WITH_IMGUI ON CACHE BOOL "" FORCE)
set(MAGNUM_WITH_EIGEN ON CACHE BOOL "" FORCE)
if(APPLICATION_USE_GUI)
	set(MAGNUM_WITH_GLFWAPPLICATION ON CACHE BOOL "" FORCE)
else()
    set(MAGNUM_WITH_GLFWAPPLICATION OFF CACHE BOOL "" FORCE)
endif()
# If you want to load just basic OBJs
set(MAGNUM_WITH_ANYIMAGEIMPORTER ON CACHE BOOL "" FORCE)
set(MAGNUM_WITH_ANYSCENEIMPORTER ON CACHE BOOL "" FORCE)
set(MAGNUM_WITH_OBJIMPORTER ON CACHE BOOL "" FORCE)
# If you want to load (textured) glTF as well
set(MAGNUM_WITH_STBIMAGEIMPORTER ON CACHE BOOL "" FORCE)
set(MAGNUM_WITH_TINYGLTFIMPORTER ON CACHE BOOL "" FORCE)
set(MAGNUM_WITH_ANYSCENECONVERTER ON CACHE BOOL "" FORCE)
set(MAGNUM_WITH_GLTFSCENECONVERTER ON CACHE BOOL "" FORCE)

add_subdirectory(corrade EXCLUDE_FROM_ALL)
add_subdirectory(magnum EXCLUDE_FROM_ALL)
if(APPLICATION_USE_GUI)
	find_package(Magnum REQUIRED GL MeshTools Shaders SceneGraph Trade GlfwApplication)
else()
    find_package(Magnum REQUIRED GL MeshTools Shaders SceneGraph Trade)
endif()
add_subdirectory(magnum-plugins EXCLUDE_FROM_ALL)
set(CORRADE_WITH_RC OFF CACHE BOOL "" FORCE)

set(ImGui_INCLUDE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/imgui" CACHE PATH "" FORCE)
set(imgui_DIR "${CMAKE_CURRENT_SOURCE_DIR}/imgui" CACHE PATH "" FORCE)
set(ImGui_imgui_SOURCE "${ImGui_INCLUDE_DIR}/imgui.cpp" CACHE FILEPATH "" FORCE)
set(ImGui_imgui_widgets_SOURCE "${ImGui_INCLUDE_DIR}/imgui_widgets.cpp" CACHE FILEPATH "" FORCE)
set(ImGui_imgui_draw_SOURCE "${ImGui_INCLUDE_DIR}/imgui_draw.cpp" CACHE FILEPATH "" FORCE)
set(ImGui_imgui_demo_SOURCE "${ImGui_INCLUDE_DIR}/imgui_demo.cpp" CACHE FILEPATH "" FORCE)
set(ImGui_imgui_tables_SOURCE "${ImGui_INCLUDE_DIR}/imgui_tables.cpp" CACHE FILEPATH "" FORCE)
find_package(ImGui REQUIRED)

set(MAGNUM_WITH_EIGEN ON CACHE BOOL "" FORCE)
add_subdirectory(magnum-integration EXCLUDE_FROM_ALL)
find_package(MagnumIntegration REQUIRED ImGui Eigen)
set_property(TARGET MagnumImGuiIntegration APPEND PROPERTY
	INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})

add_library(ImGuiFileDialog
 ${CMAKE_CURRENT_SOURCE_DIR}/ImGuiFileDialog/ImGuiFileDialog.h
 ${ImGui_INCLUDE_DIR}/imgui.h
 ${CMAKE_CURRENT_SOURCE_DIR}/ImGuiFileDialog/ImGuiFileDialog.cpp
 ${CMAKE_CURRENT_SOURCE_DIR}/ImGuiFileDialog/ImGuiFileDialogConfig.h
 )
target_include_directories(ImGuiFileDialog PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/imgui)

add_library(ImGuizmo
 ${CMAKE_CURRENT_SOURCE_DIR}/ImGuizmo/ImGuizmo.h
 ${ImGui_INCLUDE_DIR}/imgui.h
 ${CMAKE_CURRENT_SOURCE_DIR}/ImGuizmo/ImGuizmo.cpp
 )
target_include_directories(ImGuizmo PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/imgui)

find_package(OpenMP)

add_subdirectory(cnpy)
set_property(TARGET cnpy APPEND PROPERTY INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})

add_subdirectory(frictionfrenzy)
set_property(TARGET __ff_FrictionFrenzy APPEND PROPERTY
	INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR}/frictionfrenzy/src)

add_subdirectory(yaml-cpp)
set(YAML_CPP_BUILD_TESTS OFF CACHE BOOL "" FORCE)
set(YAML_CPP_BUILD_TOOLS OFF CACHE BOOL "" FORCE)
set_property(TARGET yaml-cpp APPEND PROPERTY INTERFACE_INCLUDE_DIRECTORIES
	"${PROJECT_SOURCE_DIR}/extern/yaml-cpp/include")

