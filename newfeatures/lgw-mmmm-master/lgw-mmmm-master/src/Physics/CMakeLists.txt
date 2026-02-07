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

add_library(Physics STATIC
  ${HEADER_FILES}
  ${SOURCE_FILES}
  )

target_include_directories(Physics PUBLIC
	${FRICTION_FRENZY_INCLUDE_DIR}
)

target_link_libraries(Physics PUBLIC
  ${Eigen_LIBRARIES}
  FrictionFrenzy::FrictionFrenzy
  Common
  Geometry)
