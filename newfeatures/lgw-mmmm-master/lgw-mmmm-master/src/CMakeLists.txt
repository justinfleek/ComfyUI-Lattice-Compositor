find_package(Eigen3 3.4 REQUIRED)
include_directories(${Eigen3_SOURCE_DIR})
# message(${Eigen3_SOURCE_DIR})


# find_package(LIBIGL QUIET)
include_directories(${LIBIGL_INCLUDE_DIR})

find_package(OpenMP REQUIRED)

find_package(Corrade REQUIRED Containers)
set_directory_properties(PROPERTIES CORRADE_USE_PEDANTIC_FLAGS OFF)

if(CLI_APPLICATION_ONLY)
	find_package(Magnum REQUIRED GL WindowlessEglApplication ObjImporter)
	find_package(MagnumIntegration REQUIRED Eigen)
else()
	find_package(Magnum REQUIRED GL GlfwApplication WindowlessEglApplication ObjImporter)
	find_package(MagnumIntegration REQUIRED ImGui Eigen)
endif()
find_package(MagnumPlugins REQUIRED PngImageConverter)

# find_package(Scotch REQUIRED)
# find_package(MMGS REQUIRED)
# include_directories(${MMGS_INCLUDE_DIRS})

add_subdirectory(Cameras)
add_subdirectory(Common)
add_subdirectory(Geometry)
add_subdirectory(Shaders)
add_subdirectory(Drawables)
add_subdirectory(Grids)
add_subdirectory(Sampling)
add_subdirectory(Particles)
add_subdirectory(Physics)
add_subdirectory(IO)
add_subdirectory(Applications)
add_subdirectory(UnitTest)
