file(
    GLOB_RECURSE
    HEADER_FILES
    *.h
    *.hpp
    )
file(
    GLOB_RECURSE
    SOURCE_FILES
    *.cpp
    )

add_library(IO STATIC
  ${HEADER_FILES}
  ${SOURCE_FILES}
  )

target_include_directories(IO PRIVATE ${RAPIDJSON_INCLUDE_DIRS})

add_dependencies(IO Magnum::ObjImporter)

target_link_libraries(IO
  ${Eigen_LIBRARIES}
  Magnum::ObjImporter
  MagnumIntegration::Eigen
  FrictionFrenzy::FrictionFrenzy
  Common
  Sampling
  Geometry
  Physics)
