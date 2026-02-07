add_subdirectory(PrimalDual)
add_library(__ff_Solver STATIC Solver.h ForceSolverBase.h)
target_link_libraries(__ff_Solver __ff_PrimalDualSolver)
target_include_directories(__ff_Solver PUBLIC
	${CCD_INCLUDE_PATH}
	${FCL_INCLUDE_PATH}
	${DISCREGRID_INCLUDE_PATH}
	${LIBIGL_INCLUDE_PATH}
	${FRICTION_COMMON_DIR}
)

add_library(FrictionFrenzy::Solver ALIAS __ff_Solver)

