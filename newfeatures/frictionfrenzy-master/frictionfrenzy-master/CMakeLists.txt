cmake_minimum_required(VERSION 3.18)
set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED On)
set(CMAKE_CXX_EXTENSIONS Off)
#set(CMAKE_CXX_FLAGS "-ftime-trace -Wall")
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()
set(CMAKE_CXX_FLAGS_RELEASE "-DNDEBUG -Wall -O3")
set(CMAKE_C_FLAGS_RELEASE "-DNDEBUG -Wall -O3")
set(CMAKE_CXX_FLAGS "-Wall")
set(CMAKE_EXPORT_COMPILE_COMMANDS ON CACHE INTERNAL "")
if(CMAKE_EXPORT_COMPILE_COMMANDS)
  set(CMAKE_CXX_STANDARD_INCLUDE_DIRECTORIES
      ${CMAKE_CXX_IMPLICIT_INCLUDE_DIRECTORIES})
endif()
set(CMAKE_BUILD_RPATH_USE_ORIGIN on)
set(APPLICATION_USE_GUI on)

project(FrictionFrenzy)

set(CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/modules/" ${CMAKE_MODULE_PATH})
set(EIGEN_BUILD_PATH "${CMAKE_BINARY_DIR}/${CMAKE_BUILD_TYPE}/lib/eigen")
list(PREPEND CMAKE_MODULE_PATH ${CMAKE_CURRENT_SOURCE_DIR}/cmake)

# set(HPP_FCL_BUILD_PATH "${CMAKE_BINARY_DIR}/${CMAKE_BUILD_TYPE}/lib/hpp-fcl")

find_package (Cholmod REQUIRED)

add_subdirectory(extern)
add_subdirectory(src)

add_library(__ff_FrictionFrenzy STATIC FrictionFrenzy.cpp FrictionFrenzy.h)
target_link_libraries(__ff_FrictionFrenzy
	FrictionFrenzy::CollisionObject
	FrictionFrenzy::Contact
	FrictionFrenzy::Dynamics
	FrictionFrenzy::Solver
)

set_property(TARGET __ff_FrictionFrenzy APPEND PROPERTY
	INTERFACE_INCLUDE_DIRECTORIES ${CMAKE_CURRENT_SOURCE_DIR})

add_library(FrictionFrenzy::FrictionFrenzy ALIAS __ff_FrictionFrenzy)



