add_library(__ff_Dynamics STATIC
    DynamicSystem.h
    DynamicSystem.cpp
	RigidBodyWorld.h
	EuclideanWorld.h
	PeriodicWorld.h
	PeriodicWorld.cpp
)
add_dependencies(__ff_Dynamics
    fcl
)
target_link_libraries(__ff_Dynamics
	FrictionFrenzy::CollisionObject
	FrictionFrenzy::Contact
	FrictionFrenzy::Solver
    OpenMP::OpenMP_CXX
    ${FCL_LIBRARY}
    ${CCD_LIBRARY}
)
target_include_directories(__ff_Dynamics PUBLIC
	${FRICTION_COMMON_DIR}
	${CCD_INCLUDE_PATH}
	${FCL_INCLUDE_PATH}
	${DISCREGRID_INCLUDE_PATH}
	${LIBIGL_INCLUDE_PATH}
)
add_library(FrictionFrenzy::Dynamics ALIAS __ff_Dynamics)
