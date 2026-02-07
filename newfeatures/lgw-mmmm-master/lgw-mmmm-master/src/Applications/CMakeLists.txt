set_directory_properties(PROPERTIES CORRADE_USE_PEDANTIC_FLAGS OFF)
if(NOT CLI_APPLICATION_ONLY)
add_executable(mpm3DApp mpm3DApp.cpp mpm3DApp.hpp)
target_include_directories(mpm3DApp PRIVATE ${RAPIDJSON_INCLUDE_DIRS})
target_link_libraries(mpm3DApp PRIVATE
  Corrade::Main    
  Magnum::Application
  Magnum::GL
  Magnum::Magnum
  Magnum::Shaders
  Magnum::SceneGraph
  Magnum::Primitives
  Magnum::MeshTools
  Magnum::Trade
  MagnumIntegration::ImGui
  MagnumIntegration::Eigen
  MagnumPlugins::PngImageConverter
  MagnumPlugins::PngImporter
  # cnpy
  Cameras
  Drawables
  Grids
  Sampling
  Particles
  Physics
  Common
  IO
  )
endif()

add_executable(CLImpm3DApp CLImpm3DApp.cpp CLImpm3DApp.hpp)
target_include_directories(CLImpm3DApp PRIVATE ${RAPIDJSON_INCLUDE_DIRS})
target_link_libraries(CLImpm3DApp PRIVATE
# cnpy
Grids
Sampling
Particles
Physics
Common
IO
)

# Make the executable a default target to build & run in Visual Studio
# set_property(DIRECTORY ${PROJECT_SOURCE_DIR} PROPERTY VS_STARTUP_PROJECT MyApplication)
