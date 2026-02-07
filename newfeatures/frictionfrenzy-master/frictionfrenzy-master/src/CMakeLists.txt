# include_directories("${PROJECT_SOURCE_DIR}/src")
set(FRICTION_COMMON_DIR "${PROJECT_SOURCE_DIR}/src")
include_directories(${FRICTION_COMMON_DIR})
find_package(OpenMP)
find_package(Eigen3 3.4 REQUIRED)

add_subdirectory(CollisionObject)
add_subdirectory(Contact)
add_subdirectory(Common)
add_subdirectory(Solver)
add_subdirectory(Dynamics)
add_subdirectory(UnitTests)

# # Make the executable a default target to build & run in Visual Studio
# set_property(DIRECTORY ${PROJECT_SOURCE_DIR} PROPERTY VS_STARTUP_PROJECT MyApplication)
