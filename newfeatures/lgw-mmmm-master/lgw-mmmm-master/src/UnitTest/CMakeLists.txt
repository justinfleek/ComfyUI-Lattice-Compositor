set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/${CMAKE_BUILD_TYPE}/bin/tests)

add_executable(FixedCorotatedYield FixedCorotatedYield.cpp)
target_link_libraries(FixedCorotatedYield PRIVATE
	Physics
)
add_executable(FixedCorotatedYield_Cutting FixedCorotatedYield_Cutting.cpp)
target_link_libraries(FixedCorotatedYield_Cutting PRIVATE
	Physics
	Eigen3::Eigen
)
add_executable(FixedCorotatedYield_Measured FixedCorotatedYield_Measured.cpp)
target_link_libraries(FixedCorotatedYield_Measured PRIVATE
	Physics
	Eigen3::Eigen
)
add_executable(MeasuredElasticity MeasuredElasticity.cpp)
target_link_libraries(MeasuredElasticity PRIVATE
	Physics
	Eigen3::Eigen
)
add_executable(MohrCoulomb MohrCoulomb.cpp)
target_link_libraries(MohrCoulomb PRIVATE Physics)

add_executable(GridTest GridTest.cpp)
target_link_libraries(GridTest PRIVATE Grids)

add_executable(BlockGridTest BlockGridTest.cpp)
target_link_libraries(BlockGridTest PRIVATE Grids)
