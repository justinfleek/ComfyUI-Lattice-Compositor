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

add_library(Drawables STATIC
  ${HEADER_FILES}
  ${SOURCE_FILES}
  )

target_link_libraries(Drawables
  FrictionFrenzy::FrictionFrenzy
  Shaders
  Magnum::Magnum
  MagnumIntegration::Eigen
  Corrade::Containers)
