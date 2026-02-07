/* SDTopoFixer.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru 2021
 *
 * This is the header for the scheme that manages the SuperDuperTopoFixer code execution.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <chrono>
#include <memory>
#include <random>

#include "../datastructures/Grid3DSparseCubical.h"
#include "../datastructures/Mesh3DCornerTable.h"
#include "../datastructures/Mesh3DInterface.h"
#include "../modules/CellSeparator.h"
#include "../modules/ComplexCellDetector.h"
#include "../modules/GridLabeler.h"
#include "../modules/LabelResolver.h"
#include "../modules/MeshUpkeeper.h"
#include "../modules/MultiLabelMarchingCuber.h"
#include "../modules/StateSaver.h"
#include "../scenes/Scene.h"
#include "../submodules/GridMeshIntersector.h"
#include "../submodules/ValueTransferrer.h"
#include "TopoFixerSettings.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class manages the flow of the SuperDuperTopoFixer code
class SDTopoFixer {
 public:
	// constructors
	SDTopoFixer(const TopoFixerSettings& settings);
	~SDTopoFixer() = default;

	// basic functions
	int init();
	// Initializes mesh from the given geometric values.
	int init(const std::vector<Vec3i>& triangle_vertices, const std::vector<Vec3d>& vertex_positions,
	         const std::vector<VertexProperties>& vertex_properties,
	         const std::vector<Vec2i>& material_labels);
	// Runs only mesh tracking part of the code on the current state of the mesh.
	int runFixer(bool should_perturb_grid);
	// Runs simulation defined by the scene.
	int runScene();
	// Runs n steps of the simulation defined by the scene.
	int runSteps(size_t steps);
	// Is the simulation finished?
	bool isSimulationFinished();
	// Runs Mesh Upkeeper Preprocessing step that includes a small subset of operations.
	int runMeshPreprocess();

	size_t getCurrentStep() const { return runner_current_step_; }

	// Saves mesh at path and in the format specified by the input parameters.
	void saveMesh(int current_step);

	void clearNonMeshState();

	// return grid cell size; this value is made accessible here, so that simulators can use it to
	// tune their parameters
	double getGridCellSize() const { return grid.get_cell_dx(); }

	// data structre access for rendering
	Mesh3DInterface* getMesh3DInterface() { return &mesh; };
	Grid3DSparseCubical* getGrid3DCubical() { return &grid; };
	GridLabeler* getGridLabeler() { return &grid_labeler; }
	ComplexCellDetector* getComplexCellDetector() { return &complex_cell_detector; }
	ValueTransferrer* getValueTransferrer() { return &value_transferrer; }
	CellSeparator* getCellSeparator() { return &cell_separator; }
	MultiLabelMarchingCuber* getMultiLabelMarchingCuber() { return &multi_label_marching_cuber; }
	MeshUpkeeper* getMeshUpkeeper() { return &mesh_upkeeper; }

	const TopoFixerSettings& getSettings() const { return settings; }

 private:
	void markProblematicElements(Grid3DInterface& grid_struct) const;
	// Initializes grid based on the provided input parameters. If `perturbed` is true, randomly
	// shifts the location of the grid origin while keeping mesh in bounds.
	void initGrid(const bool perturbed);

	// If per-module timings are enabled, measures time between `previous_time_point`and current time,
	// prints the time elapsed and returns the current time point.
	// Otherwise returns `previous_time_point`.
	std::chrono::high_resolution_clock::time_point measureTiming(
	    const std::chrono::high_resolution_clock::time_point& previous_time_point) const;

	// All the settings for all the things
	const TopoFixerSettings settings;

	// data structures
	Mesh3DCornerTable mesh;
	Grid3DSparseCubical grid;

	// modules
	GridLabeler grid_labeler;
	ComplexCellDetector complex_cell_detector;
	LabelResolver label_resolver;
	ValueTransferrer value_transferrer;
	CellSeparator cell_separator;
	MultiLabelMarchingCuber multi_label_marching_cuber;
	MeshUpkeeper mesh_upkeeper;
	StateSaver state_saver;

	// submodules
	GridMeshSoSIntersector intersector;

	// Scene
	std::unique_ptr<Scene> scene;

	// Runner step -- Might desync from scene if not using fixed dt
	size_t runner_current_step_ = 0;

	// Algorithm parameters
	const int orientation_ = 0;

	// Grid elements that caused problems during execution. We handle them separately, i.e.
	// we mark them as complex, thus the complex cell region is enlarged and modules are
	// rerun to try again.
	// Currently only faces are ever assigned, in general assign here any troublesome
	// elements that should cause the algorithm to backtrack and try again.
	absl::flat_hash_set<long long> problematic_vertices_;
	absl::flat_hash_set<long long> problematic_edges_;
	absl::flat_hash_set<long long> problematic_faces_;

	// Random machinery as a last resort to get out of degenerate cases.
	std::mt19937 random_gen_;
};
