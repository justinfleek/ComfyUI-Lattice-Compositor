add_library(Drawables STATIC
    ColoredDrawable.h
    ColoredDrawable.cpp
)
target_include_directories(Drawables PUBLIC ${YAML_INCLUDE_PATH} ${FF_INCLUDE_PATH})
target_link_libraries(Drawables
	yaml-cpp::yaml-cpp
	Magnum::Magnum
	MagnumIntegration::ImGui
	MagnumIntegration::Eigen
	FrictionFrenzy::CollisionObject
)
