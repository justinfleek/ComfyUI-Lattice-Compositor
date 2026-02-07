set_directory_properties(PROPERTIES CORRADE_USE_PEDANTIC_FLAGS ON)

if(APPLICATION_USE_GUI)
	add_executable(Homogenization Homogenization.cpp)
	target_link_libraries(Homogenization
        Corrade::Main    
        Magnum::Application
        Magnum::GL
        Magnum::Magnum
        Magnum::SceneGraph
        MagnumIntegration::ImGui
        MagnumIntegration::Eigen
        ImGuizmo
        ImGuiFileDialog
        Cameras
        Drawables
		FrictionFrenzy::FrictionFrenzy
		__hg_IO
		__hg_Experiments
		__hg_GUI
	)
endif()
add_executable(CLIHomogenization CLIHomogenization.cpp)
target_link_libraries(CLIHomogenization PRIVATE
    FrictionFrenzy::FrictionFrenzy
	__hg_GUI
	__hg_IO
)

# Make the executable a default target to build & run in Visual Studio
# set_property(DIRECTORY ${PROJECT_SOURCE_DIR} PROPERTY VS_STARTUP_PROJECT MyApplication)
