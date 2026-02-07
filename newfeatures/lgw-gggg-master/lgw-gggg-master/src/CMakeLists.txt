set_directory_properties(PROPERTIES CORRADE_USE_PEDANTIC_FLAGS ON)

find_package(OpenMP)
find_package(Eigen3 3.4 REQUIRED)
find_package(ImGui REQUIRED)

add_subdirectory(Cameras)
add_subdirectory(Common)
add_subdirectory(Drawables)
add_subdirectory(Experiments)
add_subdirectory(Applications)
add_subdirectory(UnitTests)
add_subdirectory(IO)
add_subdirectory(UI)
# # Make the executable a default target to build & run in Visual Studio
# set_property(DIRECTORY ${PROJECT_SOURCE_DIR} PROPERTY VS_STARTUP_PROJECT MyApplication)
