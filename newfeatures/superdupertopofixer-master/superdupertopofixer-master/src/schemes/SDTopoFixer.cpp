/* SDTopoFixer.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the implementation file for the scheme that manages the SuperDuperTopoFixer code
 * execution.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "SDTopoFixer.h"

#include <chrono>
#include <filesystem>
#include <memory>
#include <unordered_set>

#include "../datastructures/mesh_io/ObjFileHandler.h"
#include "../scenes/ConstantVelocity.h"
#include "../scenes/CurlNoise.h"
#include "../scenes/GridAdvect.h"
#include "../scenes/MeshMultiplier.h"
#include "../scenes/NormalFlow.h"
#include "../scenes/Roll.h"
#include "../scenes/SmoothInverter.h"
#include "../scenes/Zalesak.h"

//------------------------------------------------------------
// constructors
//------------------------------------------------------------

// default constructor
// Some parameters for the mesh upkeeper are updated in the `init()`
// function.
SDTopoFixer::SDTopoFixer(const TopoFixerSettings& settings)
    : settings(settings),
      mesh(this->settings),
      grid_labeler(this->settings),
      complex_cell_detector(this->settings),
      label_resolver(this->settings),
      value_transferrer(this->settings),
      cell_separator(this->settings),
      multi_label_marching_cuber(this->settings),
      mesh_upkeeper(this->settings),
      state_saver(this->settings),
      intersector(this->settings) {
	if (settings.run_mode != TopoFixerSettings::RunMode::Scene) {
		scene = nullptr;
		return;
	}

	auto scene_type = settings.scene_type;
	double max_sim_time = settings.max_sim_time;
	if (scene_type == TopoFixerSettings::SceneType::NormalFlow) {
		scene = std::make_unique<NormalFlow>(&mesh, max_sim_time, settings);
	} else if (scene_type == TopoFixerSettings::SceneType::ConstantVelocity) {
		scene = std::make_unique<ConstantVelocityScene>(&mesh, max_sim_time);
	} else if (scene_type == TopoFixerSettings::SceneType::Zalesak) {
		scene = std::make_unique<ZalesakScene>(&mesh, max_sim_time);
	} else if (scene_type == TopoFixerSettings::SceneType::MeshMultiply) {
		scene = std::make_unique<MeshMultiplierScene>(&mesh, max_sim_time, settings);
	} else if (scene_type == TopoFixerSettings::SceneType::Curlnoise) {
		scene = std::make_unique<CurlNoiseScene>(&mesh, max_sim_time);
	} else if (scene_type == TopoFixerSettings::SceneType::SmoothInverter) {
		scene = std::make_unique<SmoothInverterScene>(&mesh, max_sim_time);
	} else if (scene_type == TopoFixerSettings::SceneType::Roll) {
		scene = std::make_unique<RollScene>(&mesh, max_sim_time);
	} else if (scene_type == TopoFixerSettings::SceneType::TwoRoll) {
		scene = std::make_unique<TwoRollScene>(&mesh, max_sim_time);
	} else if (scene_type == TopoFixerSettings::SceneType::GridAdvect) {
		scene = std::make_unique<GridAdvectScene>(&mesh, max_sim_time, settings.grid_advect_dir);
	}
	std::random_device random_device_;
	random_gen_ = std::mt19937(random_device_());
}

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// read input file and initialize data structure
int SDTopoFixer::init() {
	int return_value = 0;

	// Check that there exists a mesh input file. If not, quit.
	std::filesystem::path input_mesh_file = settings.input_mesh_file;
	std::cout << "-opening input mesh file: " << input_mesh_file << "\n";

	if (!std::filesystem::exists(input_mesh_file)) {
		std::cout << "-ERROR: No mesh input file found.\n";
		return 1;
	}

	if (settings.input_mesh_type == TopoFixerSettings::InputMeshType::Obj) {
		// Load mesh from obj file.
		ObjFileHandler obj_reader;
		auto [status, message] = obj_reader.readFromFile(&mesh, input_mesh_file);
		return_value = status;
		if (settings.verbosity >= 2) {
			std::cout << message << std::endl;
		}
	} else if (settings.input_mesh_type == TopoFixerSettings::InputMeshType::Bin) {
		// Load mesh from a corner table file.
		// TODO: implement consistency checks for loading from binary file
		return_value = mesh.loadBinary(input_mesh_file.native());
	}

	initGrid(/*perturbed=*/false);

	// Adjust mesh improvement parameters.
	mesh_upkeeper.setMinEdgeLength(grid.get_cell_dx() * settings.min_edge_length_rel_to_grid);
	mesh_upkeeper.setMaxEdgeLength(grid.get_cell_dx() * settings.max_edge_length_rel_to_grid);

	if (settings.verbosity >= 1) {
		std::cout << "-initialization with input file " << input_mesh_file
		          << " finished with return value " << return_value << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return return_value;
}

// read input file and initialize data structure
int SDTopoFixer::init(const std::vector<Vec3i>& triangle_vertices,
                      const std::vector<Vec3d>& vertex_positions,
                      const std::vector<VertexProperties>& vertex_properties,
                      const std::vector<Vec2i>& material_labels) {
	int return_value = 0;
	int result = mesh.restoreFromGeometry(triangle_vertices, vertex_positions, vertex_properties,
	                                      material_labels, /*add_to_existing=*/false,
	                                      /*offset_materials*/ false);
	if (result != 0) {
		return result;
	}
	initGrid(/*perturbed=*/false);

	// Adjust mesh improvement parameters.
	mesh_upkeeper.setMinEdgeLength(grid.get_cell_dx() * settings.min_edge_length_rel_to_grid);
	mesh_upkeeper.setMaxEdgeLength(grid.get_cell_dx() * settings.max_edge_length_rel_to_grid);

	if (settings.verbosity >= 1) {
		std::cout << "-initialization with input file " << settings.input_mesh_file
		          << " finished with return value " << return_value << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return return_value;
}

// function that coordinates the run of the SuperDuperTopoFixer scheme
int SDTopoFixer::runFixer(bool should_perturb_grid) {
	std::cout << "-Run Fixer" << std::endl;
	int return_value = 0;
	if (settings.verbosity >= 2) {
		std::cout << "Number of vertices in mesh: " << mesh.getNumberVerts() << std::endl;
		std::cout << "Number of triangles in mesh: " << mesh.getNumberTris() << std::endl;

		std::cout << "==========================================================================="
		             "=========="
		          << std::endl;
	}
	std::chrono::high_resolution_clock::time_point previous_time_point =
	    std::chrono::high_resolution_clock::now();

	initGrid(should_perturb_grid);

	// grid labeler
	if (settings.run_grid_labeler) {
		do {
			return_value = grid_labeler.run(mesh, grid, intersector, orientation_);
			if (return_value != 0) {
				if (settings.verbosity >= 1) {
					std::cout << "-perturbing grid " << return_value << std::endl;
					std::cout << "==========================================================================="
					             "=========="
					          << std::endl;
				}
				clearNonMeshState();
				initGrid(/*perturbed=*/true);
			}
		} while (return_value != 0);
		previous_time_point = measureTiming(previous_time_point);
	}
	if (settings.verbosity >= 2) {
		std::cout << "Number of allocated grid cells: " << grid.getNumAllocatedCells() << std::endl;
		std::cout << "==========================================================================="
		             "=========="
		          << std::endl;
	}

	// save state
	if (settings.run_state_saver) {
		state_saver.save(grid, mesh);
		previous_time_point = measureTiming(previous_time_point);
	}
	// loop that attempts to perform cell separation; if an error is encountered, complex cell
	// region is expanded, a valid state is loaded, and another attempt is made
	do {
		// complex cell detector
		if (settings.run_complex_cell_detector) {
			return_value = complex_cell_detector.run(mesh, grid, intersector, orientation_);
			previous_time_point = measureTiming(previous_time_point);
		}
		// label resolver
		if (settings.run_label_resolver) {
			return_value = label_resolver.run(mesh, grid, intersector, orientation_);
			previous_time_point = measureTiming(previous_time_point);
		}
		// value transferrer
		if (settings.run_value_transferrer) {
			return_value = value_transferrer.meshToGridTransfer(mesh, grid);
			previous_time_point = measureTiming(previous_time_point);
		}
		// cell separator
		if (settings.run_cell_separator) {
			return_value = cell_separator.run(mesh, grid, intersector, orientation_);
			previous_time_point = measureTiming(previous_time_point);
		}
		// if cell separation failed, enlargen the complex cell region and try again
		if (return_value != 0) {
			// load state
			state_saver.load(grid, mesh);
			grid.clear_mesh_edge_intersections();

			// determine the problematic regions
			// TODO: store the problematic elements inside the grid class, while making sure that when
			// a state is loaded, this information is correctly retained (i.e. not scrapped along with
			// the grid object)
			absl::flat_hash_set<long long> face_ids = cell_separator.getFailedSeparationFaces();
			problematic_faces_.insert(face_ids.begin(), face_ids.end());
			markProblematicElements(grid);
		}
	} while (return_value != 0);
	// marching cuber
	if (settings.run_multi_label_marching_cuber) {
		return_value = multi_label_marching_cuber.run(mesh, grid, intersector, orientation_);
		previous_time_point = measureTiming(previous_time_point);
	}
	// value transferrer before mesh upkeep
	if (settings.run_value_transferrer &&
	    settings.grid_to_mesh_interpolation_timing ==
	        TopoFixerSettings::GridToMeshInterpolationTiming::BeforeMeshUpkeep) {
		return_value = value_transferrer.gridToMeshTransferBeforeMeshUpkeep(mesh, grid);
		previous_time_point = measureTiming(previous_time_point);
	}
	// mesh upkeeper
	if (settings.run_mesh_upkeeper) {
		mesh_upkeeper.run(mesh, grid, intersector, orientation_);
		previous_time_point = measureTiming(previous_time_point);
	}
	// value transferrer after mesh upkeep
	if (settings.run_value_transferrer &&
	    settings.grid_to_mesh_interpolation_timing ==
	        TopoFixerSettings::GridToMeshInterpolationTiming::AfterMeshUpkeep) {
		return_value = value_transferrer.gridToMeshTransferAfterMeshUpkeep(mesh, grid);
		previous_time_point = measureTiming(previous_time_point);
	}

	if (settings.verbosity >= 1) {
		std::cout << "-Defragging mesh " << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	mesh.defragmentMesh();
	previous_time_point = measureTiming(previous_time_point);
	if (settings.verbosity >= 1) {
		std::cout << "-SuperDuperTopoFixer finished with return value " << return_value << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return return_value;
}

int SDTopoFixer::runScene() { return runSteps(std::numeric_limits<size_t>::max()); }

int SDTopoFixer::runSteps(size_t steps) {
	size_t current_step = 0;
	const double dt = settings.dt;
	const int run_every_n = std::max(1, settings.run_mesher_every_n_steps);
	const bool should_perturb_grid = settings.should_perturb_grid;

	while ((!scene->isFinished()) && ((steps < 0) || (current_step < steps))) {
		std::cout << "-starting scene step " << runner_current_step_ << std::endl;
		scene->step(dt);
		current_step++;
		runner_current_step_ += 1;
		if ((runner_current_step_ % run_every_n == 0) && runFixer(should_perturb_grid)) {
			return 1;
		}
		if (settings.should_output_frames) {
			saveMesh(runner_current_step_);
		}
		if (!scene->isFinished()) {
			clearNonMeshState();
		}
		std::cout << "-end scene " << std::endl;
	}
	return 0;
}

bool SDTopoFixer::isSimulationFinished() { return scene->isFinished(); }

int SDTopoFixer::runMeshPreprocess() { return mesh_upkeeper.runPreprocess(mesh, grid); }

void SDTopoFixer::saveMesh(int current_step) {
	std::string output_path = settings.output_path;
	std::string base_path = output_path.substr(0, output_path.size() - 3);
	auto output_type = settings.output_type;
	if (output_type == TopoFixerSettings::OutputType::Obj) {
		ObjFileHandler file_handler;
		file_handler.writeToFile(getMesh3DInterface(),
		                         base_path + std::to_string(current_step) + ".obj");
	} else {
		getMesh3DInterface()->writeInBin(base_path + std::to_string(current_step) + ".bin");
	}
}

void SDTopoFixer::clearNonMeshState() {
	grid = Grid3DSparseCubical();
	grid_labeler = GridLabeler(settings);
	complex_cell_detector = ComplexCellDetector(settings);
	label_resolver = LabelResolver(settings);
	value_transferrer = ValueTransferrer(settings);
	cell_separator.clearState();
	multi_label_marching_cuber = MultiLabelMarchingCuber(settings);
	state_saver = StateSaver(settings);
	mesh_upkeeper.clearState();
	problematic_vertices_.clear();
	problematic_edges_.clear();
	problematic_faces_.clear();

	mesh.clearNonPersistentState();
}

void SDTopoFixer::markProblematicElements(Grid3DInterface& grid_struct) const {
	for (long long vertex : problematic_vertices_) {
		grid_struct.markVertexAsComplex(vertex);
	}
	for (long long edge : problematic_edges_) {
		grid_struct.markEdgeAsTopoComplex(edge);
		grid_struct.markEdgeAsGeomComplex(edge);
	}
	for (long long face : problematic_faces_) {
		grid_struct.unmarkFaceAsTopoSimple(face);
		grid_struct.markFaceAsTopoComplex(face);
		grid_struct.markFaceAsGeomComplex(face);
	}
}

void SDTopoFixer::initGrid(const bool perturbed) {
	// find the bounding box of the loaded mesh, in order to determine the size of the grid
	// determine the smallest and largest coordinates present in the mesh
	Vec3d mesh_min, mesh_max;
	mesh.getMeshBounds(mesh_min, mesh_max);
	if (settings.verbosity >= 1) {
		std::cout << "mesh max: " << mesh_max << " mesh min: " << mesh_min << '\n';
	}
	// std::getchar();
	// pad the bounding box of the mesh, so that all of the mesh elements are strictly inside the
	// grid
	mesh_min -= 0.1;
	mesh_max += 0.1;

	Vec3d origin(0.0);
	double dx = 0.0;

	// initialize grid
	const int num_grid_cells = settings.num_grid_cells;
	if (settings.grid_bounding_box_style == TopoFixerSettings::GridBoundingBoxStyle::FixedCube) {
		// grid is a cube defined between `cube_min_coord` and `cube_max_coord`, algorithm will only run
		// correctly if all mesh vertices lie in this range; grid is divided into `num_grid_cells`
		// cubical cells in each axis
		double min_coord = settings.cube_min_coord;
		double max_coord = settings.cube_max_coord;
		assert(max_coord > min_coord);
		origin = Vec3d(min_coord);
		dx = (max_coord - min_coord) / num_grid_cells;
	} else if (settings.grid_bounding_box_style ==
	           TopoFixerSettings::GridBoundingBoxStyle::MinmaxCube) {
		// grid will be a cube defined between mesh_min and max(mesh_max), that is, one corner of the
		// grid is defined by the smallest x, smallest y, smallest z coordinate from among all the
		// vertices, but only the largest coordinate from mesh_max defines the other corner of the
		// grid, thus making sure the grid is a cube; grid is divided into `num_grid_cells` cubical
		// cells in each axis; mesh vertices are guaranteed to be within grid range by construction;
		// additionally, grid size is padded, to remove possible grid boundary degeneracies
		Vec3d mesh_length = mesh_max - mesh_min;
		double max_length = max(mesh_length);
		origin = mesh_min;
		dx = max_length / num_grid_cells;
	} else if (settings.grid_bounding_box_style ==
	           TopoFixerSettings::GridBoundingBoxStyle::MinmaxAxisAdjustedBlock) {
		// mesh is a block, not necessarily a cube, defined by the point mesh_min and by the parameter
		// `num_grid_cells`, and consisting of cubical cells; first `num_grid_cells` is used as the
		// number of cells in the axis that contains mesh vertices within the shortest interval, which
		// is used to determine the size of the cubical grid cell; number of grid cells in the two
		// remaining axes is then computed using this grid cell size to contain all of the mesh
		// vertices (number of grid cells in these two axes is therefore larger or equal to
		// `num_grid_cells`); mesh vertices are guaranteed to be within grid range by construction;
		// additionally, grid size is padded, to remove possible grid boundary degeneracies
		int num_x_grid_cells, num_y_grid_cells, num_z_grid_cells;
		Vec3d mesh_length = mesh_max - mesh_min;
		double grid_cell_size;
		if (mesh_length[0] <= mesh_length[1] && mesh_length[0] <= mesh_length[2]) {
			num_x_grid_cells = num_grid_cells;
			grid_cell_size = mesh_length[0] / num_x_grid_cells;
		} else if (mesh_length[1] <= mesh_length[0] && mesh_length[1] <= mesh_length[2]) {
			num_y_grid_cells = num_grid_cells;
			grid_cell_size = mesh_length[1] / num_y_grid_cells;
		} else if (mesh_length[2] <= mesh_length[0] && mesh_length[2] <= mesh_length[1]) {
			num_z_grid_cells = num_grid_cells;
			grid_cell_size = mesh_length[2] / num_z_grid_cells;
		}
		origin = mesh_min;
		dx = grid_cell_size;
	}
	if (perturbed) {
		std::uniform_real_distribution<> dis(0.0, std::min(dx / 2, 0.05));
		origin += Vec3d(dis(random_gen_), dis(random_gen_), dis(random_gen_));
	}
	grid.init(num_grid_cells, num_grid_cells, num_grid_cells, origin[0], origin[1], origin[2], dx);
}

std::chrono::high_resolution_clock::time_point SDTopoFixer::measureTiming(
    const std::chrono::high_resolution_clock::time_point& previous_time_point) const {
	if (!settings.measure_module_timings) {
		return previous_time_point;
	}

	auto now = std::chrono::high_resolution_clock::now();
	long long runtime =
	    std::chrono::duration_cast<std::chrono::microseconds>(now - previous_time_point).count();

	std::cout << "-The above module ran for " << runtime / 1000 << "ms" << std::endl;
	return now;
}
