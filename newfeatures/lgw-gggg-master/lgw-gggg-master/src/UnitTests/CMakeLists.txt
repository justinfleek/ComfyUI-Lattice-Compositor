set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/${CMAKE_BUILD_TYPE}/bin/tests)

add_executable(CNPYTest CNPYTest.cpp)
add_dependencies(CNPYTest
    cnpy
)
target_include_directories(CNPYTest PRIVATE ${CNPY_INCLUDE_PATH})
target_link_libraries(CNPYTest PRIVATE
    OpenMP::OpenMP_CXX
    cnpy
)
