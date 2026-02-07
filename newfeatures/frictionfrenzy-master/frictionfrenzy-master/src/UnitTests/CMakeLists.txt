set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/${CMAKE_BUILD_TYPE}/bin/tests)
add_executable(ConstraintTest ConstraintTest.cpp)
target_link_libraries(ConstraintTest PRIVATE
    OpenMP::OpenMP_CXX
	FrictionFrenzy::Dynamics
)
