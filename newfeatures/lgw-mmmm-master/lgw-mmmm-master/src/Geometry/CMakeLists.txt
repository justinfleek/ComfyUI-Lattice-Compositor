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

add_library(Geometry STATIC
  ${HEADER_FILES}
  ${SOURCE_FILES}
  )

target_link_libraries(Geometry
  Magnum::Magnum
  Magnum::GL
  Common
  Physics # bad dependency
  igl::core
  )
