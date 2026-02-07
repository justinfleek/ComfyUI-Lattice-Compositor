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

add_library(Common STATIC
  ${HEADER_FILES}
  ${SOURCE_FILES}
  )

target_link_libraries(Common
	Eigen3::Eigen
  Magnum::Magnum)
