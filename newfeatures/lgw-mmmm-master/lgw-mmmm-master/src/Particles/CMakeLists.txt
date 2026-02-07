add_library(Particles STATIC
    ParticleBase.h
    ParticleBase.cpp
)
target_link_libraries(Particles
	Eigen3::Eigen
	MagnumIntegration::Eigen
	FrictionFrenzy::FrictionFrenzy
    Magnum::GL
    Magnum::Magnum
    Magnum::Shaders
    Magnum::SceneGraph
    Magnum::Primitives
    Magnum::Trade
    Magnum::Magnum)
