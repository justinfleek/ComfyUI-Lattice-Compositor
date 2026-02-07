add_library(__ff_PrimalDualSolver STATIC

    PrimalDualForceSolver.cpp
    PrimalDualForceSolver.h
	SmoothForces/SmoothForces.h
	SmoothForces/SmoothForceBase.h
	# SmoothForces/DynamicFriction.h
	# SmoothForces/DynamicFriction.cpp

	NonSmoothForces/OnlyNormalForce.h
	NonSmoothForces/SecondOrderConeForce.h
	NonSmoothForces/NonSmoothContactForce.h
	NonSmoothForces/NormalizedContactForce.h
	NonSmoothForces/NonSmoothForces.h
	NonSmoothForces/NonSmoothForceBase.h
	NonSmoothForces/SecondOrderConeForce.cpp
	NonSmoothForces/NonSmoothContactForce.cpp
	NonSmoothForces/NormalizedContactForce.cpp
	NonSmoothForces/OnlyNormalForce.cpp
	NonSmoothForces/ForceConstraint/ForceConstraint.h
	NonSmoothForces/ForceConstraint/ForceConstraintBase.h
	NonSmoothForces/ForceConstraint/LorenzCircleConstraint.h
	NonSmoothForces/ForceConstraint/LorenzCircleConstraint.cpp
	NonSmoothForces/ForceConstraint/PerturbedSecondOrderCone.h
	NonSmoothForces/ForceConstraint/PerturbedSecondOrderCone.cpp
	NonSmoothForces/ForceConstraint/RatioCircleConstraint.h
	NonSmoothForces/ForceConstraint/RatioCircleConstraint.cpp
	NonSmoothForces/ForceConstraint/CylinderConstraint.h
	NonSmoothForces/ForceConstraint/CylinderConstraint.cpp
)
target_include_directories(__ff_PrimalDualSolver PRIVATE
	${CHOLMOD_INCLUDES}
	${AMGCL_INCLUDE_PATH}
)
target_link_libraries(__ff_PrimalDualSolver
    OpenMP::OpenMP_CXX
	${CHOLMOD_LIBRARIES}
	FrictionFrenzy::CollisionObject
	FrictionFrenzy::Contact
)
