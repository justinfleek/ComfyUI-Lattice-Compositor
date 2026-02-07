set(CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS ON)

set(TopoFixerSourceFiles
	schemes/SDTopoFixer.h
    schemes/SDTopoFixer.cpp
	schemes/TopoFixerSettings.h
	schemes/TopoFixerSettingsParser.h
	schemes/TopoFixerSettingsParser.cpp

    scenes/CurlNoise.h
    scenes/CurlNoise.cpp
    scenes/ConstantVelocity.h
    scenes/ConstantVelocity.cpp
    scenes/GridAdvect.h
    scenes/GridAdvect.cpp
    scenes/MeshMultiplier.h
    scenes/MeshMultiplier.cpp
    scenes/NormalFlow.h
    scenes/NormalFlow.cpp
    scenes/Roll.h
    scenes/Roll.cpp
    scenes/Scene.h
    scenes/SmoothInverter.h
    scenes/SmoothInverter.cpp
    scenes/Zalesak.h
    scenes/Zalesak.cpp

    datastructures/GridMeshIntersection.h
    datastructures/GridMeshIntersection.cpp
    datastructures/Mesh3DVertex.h
    datastructures/Mesh3DTriangle.h
    datastructures/Mesh3DTriangle.cpp
    datastructures/Mesh3DInterface.h
    datastructures/Mesh3DInterface.cpp
    datastructures/Mesh3DHalfCorner.h
    datastructures/Mesh3DHalfCorner.cpp
    datastructures/Mesh3DCornerTable.h
    datastructures/Mesh3DCornerTable.cpp
	datastructures/Mesh3DCornerTableInformation.cpp
	datastructures/Mesh3DCornerTableIO.cpp
	datastructures/Mesh3DCornerTableMaintenance.cpp
	datastructures/Mesh3DCornerTableManipulation.cpp
	datastructures/Mesh3DCornerTableEdgeCollapse.cpp
	datastructures/Grid3DInterface.h
	datastructures/Grid3DInterface.cpp
	datastructures/Grid3DCubical.h
	datastructures/Grid3DCubical.cpp
	datastructures/Grid3DSparseCubical.h
	datastructures/Grid3DSparseCubical.cpp
	datastructures/TriangleSubdivision.cpp
    datastructures/VertexProperties.h
    datastructures/VertexProperties.cpp
    datastructures/mesh_io/ObjFileHandler.h
    datastructures/mesh_io/ObjFileHandler.cpp

	modules/LabelResolver.h
	modules/LabelResolver.cpp
	modules/MultiLabelMarchingCuber.h
	modules/MultiLabelMarchingCuber.cpp
    modules/ModuleInterface.h
    modules/ModuleInterface.cpp
	modules/MeshUpkeeper.h
	modules/MeshUpkeeper.cpp
    modules/GridLabeler.h
    modules/GridLabeler.cpp
    modules/ComplexCellDetector.h
    modules/ComplexCellDetector.cpp
	modules/CellSeparator.h
	modules/CellSeparator.cpp
	modules/StateSaver.h
	modules/StateSaver.cpp

    submodules/GridMeshIntersector.h
	submodules/GridMeshIntersector.cpp
	submodules/Smoother.h
	submodules/Smoother.cpp
	submodules/T1Resolver.h
	submodules/T1Resolver.cpp
	submodules/ValueTransferrer.h
	submodules/ValueTransferrer.cpp

	utilities/vec.h
	utilities/util.h
	utilities/string_util.h
	utilities/UnionFind.h
    utilities/doctest/doctest.h
    utilities/cnpy/cnpy.h
    utilities/cnpy/cnpy.cpp
	utilities/intersection/ExactnessPredicates.h
	utilities/intersection/ExactnessPredicates.cpp
	utilities/tunicate/expansion.h
	utilities/tunicate/expansion.cpp
	utilities/tunicate/neg.h
	utilities/tunicate/neg.cpp
	utilities/tunicate/orientation.cpp
	utilities/tunicate/sos_intersection.cpp
	utilities/tunicate/sos_orientation.cpp
	utilities/tunicate/tunicate.h)

add_library(TopoFixer SHARED 
    ${TopoFixerSourceFiles}
)
target_include_directories(TopoFixer INTERFACE ${CMAKE_CURRENT_SOURCE_DIR})
target_include_directories(TopoFixer PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}/utilities)
target_link_libraries(TopoFixer PUBLIC absl::flat_hash_set absl::flat_hash_map Triangle ZLIB::ZLIB)

if (OpenMP_CXX_VERSION_MAJOR GREATER_EQUAL 3)
	target_link_libraries(TopoFixer PUBLIC OpenMP::OpenMP_CXX)
else ()
	message("Disabled OpenMP because version < 3.0.")
endif ()

source_group(TREE ${CMAKE_CURRENT_SOURCE_DIR} FILES ${TopoFixerSourceFiles})

if (ENABLE_LEGACY_VIEWER)
    add_library(TopoFixerRender SHARED
        rendering/OpenGLRenderer.h
        rendering/OpenGLRenderer.cpp
        rendering/RenderingPrimitives.h
        rendering/RenderingPrimitives.cpp
        rendering/OldComplexCellVisualizer.h
        rendering/OldComplexCellVisualizer.cpp
        rendering/GridLabelerVisualizer.h
        rendering/GridLabelerVisualizer.cpp
        rendering/SmoothingVisualizer.h
        rendering/SmoothingVisualizer.cpp
        rendering/ComplexCellVisualizer.h
        rendering/ComplexCellVisualizer.cpp
        rendering/IntersectionElementsVisualizer.h
        rendering/IntersectionElementsVisualizer.cpp
        rendering/NonmanifoldEdgeVisualizer.h
        rendering/NonmanifoldEdgeVisualizer.cpp
        rendering/ValueTransferrerVisualizer.h
        rendering/ValueTransferrerVisualizer.cpp
        rendering/Visualizer.h
        rendering/Colorizer.h
        rendering/MeshColorizers.h
        rendering/MeshColorizers.cpp

        rendering/ImGUIWindows.h
        rendering/ImGUIWindows.cpp
        utilities/imgui/backends/imgui_impl_glut.h
        utilities/imgui/backends/imgui_impl_opengl2.h
        utilities/imgui/imgui.h
        utilities/imgui/imgui.cpp
        utilities/imgui/backends/imgui_impl_glut.cpp
        utilities/imgui/backends/imgui_impl_opengl2.cpp
        utilities/imgui/imgui_draw.cpp
        utilities/imgui/imgui_widgets.cpp
        utilities/imgui/imgui_tables.cpp
    )
    target_include_directories(TopoFixerRender PUBLIC 
        ${CMAKE_CURRENT_SOURCE_DIR}/utilities/imgui)
    target_link_libraries(TopoFixerRender PUBLIC ${OPENGL_LIBRARIES} ${GLUT_LIBRARIES} ${GLEW_LIBRARIES} TopoFixer)
ENDIF ()



IF (ENABLE_TESTS)
    add_executable(ObjFileHandlerTest datastructures/mesh_io/ObjFileHandlerTest.cpp)
    target_link_libraries(ObjFileHandlerTest TopoFixer)
    add_test(NAME ObjFileHandlerPasses COMMAND ObjFileHandlerTest)


    add_executable(StringUtilTest utilities/string_util_test.cpp)
    add_test(NAME StringUtilPasses COMMAND StringUtilTest)

    add_executable(T1ResolverTest submodules/T1ResolverTest.cpp)
    target_link_libraries(T1ResolverTest TopoFixer)
    add_test(NAME T1ResolverPasses COMMAND T1ResolverTest WORKING_DIRECTORY ${PROJECT_SOURCE_DIR})
ENDIF ()
