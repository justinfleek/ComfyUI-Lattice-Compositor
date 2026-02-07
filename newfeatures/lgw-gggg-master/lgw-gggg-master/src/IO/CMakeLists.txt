add_library(__hg_IO STATIC
    FileLoader.h
    FileLoader.cpp
	InputParse.h
	ParamLoad.h
	ParamLoad.cpp
    # FileSaver.h
    # FileSaver.cpp
)
add_dependencies(__hg_IO
    cnpy
    Magnum::AnyImageImporter
    Magnum::AnySceneImporter
    Magnum::AnySceneConverter
    Magnum::ObjImporter
    MagnumPlugins::StbImageImporter
    MagnumPlugins::TinyGltfImporter
    MagnumPlugins::GltfSceneConverter
)
target_link_libraries(__hg_IO
    cnpy
	FrictionFrenzy::FrictionFrenzy
	Drawables
	__hg_GUI
	__hg_Experiments
    yaml-cpp::yaml-cpp
    OpenMP::OpenMP_CXX
    Corrade::Main
    Magnum::Magnum
    Magnum::Trade
    Magnum::MeshTools
    Magnum::Primitives
    Magnum::SceneGraph
    Magnum::GL
    MagnumIntegration::Eigen
    ${FCL_LIBRARY}
    ${CCD_LIBRARY}
)
