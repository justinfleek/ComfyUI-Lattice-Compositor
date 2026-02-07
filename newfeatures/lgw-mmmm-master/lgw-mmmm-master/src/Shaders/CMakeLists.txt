corrade_add_resource(MPM_Shaders
	${CMAKE_CURRENT_SOURCE_DIR}/resources.conf)

add_library(Shaders
	ParticleShaderProgram.h
	ParticleShaderProgram.cpp
	${MPM_Shaders}
)

target_link_libraries(Shaders
	Corrade::Main
	Magnum::GL
	Magnum::Magnum
	Magnum::Shaders
)
