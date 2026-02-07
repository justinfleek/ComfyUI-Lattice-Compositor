add_library(__hg_Experiments STATIC
	ExperimentBase.h
	ExperimentBase.cpp
	Brownian.h
	Brownian.cpp
	BoundaryScaleSearch.h
	BoundaryScaleSearch.cpp
	StaticPress.h
	StaticPress.cpp
	StaticPressShear.h
	StaticPressShear.cpp
)
target_link_libraries(__hg_Experiments
	FrictionFrenzy::FrictionFrenzy
)
