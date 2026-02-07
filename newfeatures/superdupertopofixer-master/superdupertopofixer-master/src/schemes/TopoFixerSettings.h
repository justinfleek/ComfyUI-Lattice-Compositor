#pragma once

#include <limits>
#include <string>

// To add a property, first add it to this class, and then look at the documentation of the method
// "buildLookupTable()" in TopoFixerSettingsParser.cpp. It will tell you how to add code such that
// the property will be read from an input file.

class TopoFixerSettings {
 public:
	TopoFixerSettings() = default;

	// ------------------- Grid
	// Determines the number of grid cells to use. The actual usage then depends on the choice of grid
	// bounds (parameter `grid_bounding_box_style`).
	int num_grid_cells = 1;
	// Determines how will the grid be initialized. Possible values:
	// -"fixed_cube": grid will be a cube split into `num_grid_cells` number of cells in each
	// axis. Cube dimensions are specified by `cube_min_coord` and `cube_max_coord` parameters.
	//  Algorithm is only guaranteed to run correctly, if all mesh vertices are strictly inside
	// the cube.
	// -"minmax_cube": grid will be a cube defined between (mesh_x_min, mesh_y_min, mesh_z_min) and
	// (mesh_max, mesh_max, mesh_max), that is, only the largest coordinate from among mesh_x_max,
	// mesh_y_max, mesh_z_max defines the corner of the grid, making sure the grid is a cube; grid is
	// divided into `num_grid_cells` cubical cells in each axis; mesh vertices are guaranteed to be
	// within grid range by construction;  additionally, grid size is padded, to remove possible grid
	// boundary degeneracies
	// -"minmax_axis_adjusted_block": mesh is a block, not necessarily a cube, defined by the point
	// (mesh_x_min, mesh_y_min, mesh_z_min) and by the parameter `num_grid_cells`, and consisting of
	// cubical cells; first `num_grid_cells` is used as the number of cells in the axis that contains
	// mesh vertices within the shortest interval, which is used to determine the size of the cubical
	// grid cell; number of grid cells in the two remaining axes is then computed using this grid cell
	// size to contain all of the mesh vertices (number of grid cells in these two axes is therefore
	// larger or equal to `num_grid_cells`); mesh vertices are guaranteed to be within grid range by
	// construction;  additionally, grid size is padded, to remove possible grid boundary degeneracies
	enum class GridBoundingBoxStyle { FixedCube, MinmaxCube, MinmaxAxisAdjustedBlock };
	GridBoundingBoxStyle grid_bounding_box_style = GridBoundingBoxStyle::MinmaxCube;
	double cube_min_coord = 0.0;
	double cube_max_coord = 1.0;

	// Should the grid be perturbed before running topofixer and in-between each simulation step?
	bool should_perturb_grid = false;

	// ------------------- Mesh
	// Determines the file from which mesh will be loaded.
	std::string input_mesh_file = "";
	// Determines whether the input mesh is assumed to be an obj file ("obj"), or a corner table
	// binary file ("bin").
	enum class InputMeshType { Obj, Bin };
	InputMeshType input_mesh_type = InputMeshType::Obj;
	// Speficies the algorithm type to reconstruct the corner table for the input mesh. Only used when
	// `input_mesh_type` is "obj".
	// For "geometry" type the orientation tests are used to determine the opposites.
	// For "labels" label information is used to assign opposites.
	enum class OppositeReconstructionType { Geometry, Labels };
	OppositeReconstructionType opposite_reconstruction_type = OppositeReconstructionType::Geometry;
	// Determines whether to run multiple tests on the input mesh, that determine its suitability for
	// being processed by our algorithm. Tests are either optional (if they fail, the algorithm can
	// still run, though behavior is undefined) or critical (if they fail, the algorithm can't run and
	// will quit). Turning tests off decreses confidence in the quality of the input. If, however, the
	// input mesh is known to be suitable, turning off saves processing time. Possible values: "all",
	// "critical", any other value will make the code not launch any test.
	enum class InputMeshConsistencyTests { None, Critical, All };
	InputMeshConsistencyTests run_input_mesh_consistency_tests = InputMeshConsistencyTests::All;
	// Determines the amount by which triangle vertices are offset when determining which grid cells a
	// triangle could intersect.
	double triangle_registration_offset = 5e-5;
	// Sets a threshold below which no geometry test is performed when doing mesh operations such as
	// edge collapse.
	double mesh_short_edge_threshold = 1e-5;

	// ------------------- Complexity Tests
	// Complex test mode
	// -complex_test: run proper complex geometric and topological tests.
	// -resample_all: marks all cells as complex, causing surface to be resampled. Only used as debug
	// mode and should be avoided for real sims as it fill degrade all high-frequency details on the
	// surface.
	enum class ComplexCellResampleMode { ComplexTest, ResampleAll };
	ComplexCellResampleMode complex_cell_resample_mode = ComplexCellResampleMode::ComplexTest;

	// Determines the metric for deciding whether a topologically complex grid edge is geometrically
	// complex. Options are:
	// -none: decide complexity based on topology only
	// -inversion: complex if material vector along the edge ever enters a non-physical state
	enum class EdgeGeometricComplexityMetric { None, Inversion };
	EdgeGeometricComplexityMetric edge_geometric_complexity_metric =
	    EdgeGeometricComplexityMetric::Inversion;
	// Flag that determines whether the edge deep cell test should be run.
	bool run_deep_edge_test = true;
	// Determines how large of an edge neighborhood is considered when performing the edge deep cell
	// test. Edge deep cell test consideres edges that are flexible-complex, i.e. open to being
	// excluded from remeshing. If an edge that is topologically complex (has 2+ triangle
	// intersections), but not geometrically complex only ever enters materials that are on the labels
	// in the neighborhood of the edge, the nearby flexible-complex cells are relabeled as
	// non-complex. Depth parameter is interpreted as follows:
	// -0: only consider end vertices of the tested edge
	// -1: consider all vertices on cells adjacent to the tested edge
	// -2: consider all vertices in 1 plus vertices on all cells adjacent to cells in 1
	// ... and so on
	// The larger the depth parameter, the larger the mesh deformations that we consider features and
	// therefore don't remesh - we look in a larger neighborhood of the edge to see if there is a
	// vertex with a label that would prevent remeshing. In other words, the larger the depth
	// parameter, the less willing we are to perform topology changes. This is a double-edged sword:
	// considering acual features, such as occasional tentacles sprouting from the mesh, not remeshing
	// them seems to be the right call. However, it also means not performing merges between objects
	// on the thickness scale of (grid cell size) x (depth parameter), which we might want.
	int edge_deep_cell_test_depth = 1;
	// Determines the metric for deciding whether a topologically complex grid face is geometrically
	// complex. Options are::
	// -none: decide complexity based on topology only
	// -inversion: complex if material vector along the edge ever enters a non-physical state
	enum class FaceGeometricComplexityMetric { None, Inversion };
	FaceGeometricComplexityMetric face_geometric_complexity_metric =
	    FaceGeometricComplexityMetric::None;
	// Determines which grid faces are checked for complexity. Options are:
	// -all: all faces neighboring cells that have triangles intersecting them
	// -front: faces between complex and non-complex cells
	enum class FacesToCheckForComplexity { All, Front };
	FacesToCheckForComplexity faces_to_check_for_complexity = FacesToCheckForComplexity::Front;
	// Determines how thorough the complex face test should be, as a trade-off between speed and
	// accuracy/completeness of information. Options are:
	// -quick_reject: the minimum necessary amount of computation is performed, as soon as a face can
	// be labeled complex, the computation stops (eg. when a third graph component is discovered).
	// Correctness of this approach relies on other parts of the algorithm, especially the
	// intersector, to return correct output. This approach shouldn't be used for face graph
	// visualization, as the face graphs are only partially constructed.
	// -thorough: redundant computations are performed, including multiple correctness checks, and
	// construction of the whole face graph for visualization.
	enum class ComplexFaceTest { QuickReject, Thorough };
	ComplexFaceTest complex_face_test = ComplexFaceTest::Thorough;

	// ------------------- Grid Vertex Resolution
	// Determines the method for assigning unique material labels to complex grid vertices, and
	// optionally generates optimized positions for mesh vertices on grid edges in the complex region,
	// which will be used when making new mesh vertices during marching cubes reconstruction. Options
	// are:
	// -naive_BFS: does a naive BFS flood fill on grid vertices in the complex region. The BFS
	// heuristic used is that for a complex grid vertex v0, we iterate over its 6 grid neighbors in a
	// fixed order. If a neighbor v1 of v0 has a unique label l assigned, if l != 0, v0 inherits l. If
	// all adjacent vertices of v0 that have a unique label assigned have their label == 0, v0
	// inherits label 0. In other words, we try to assign a non-zero label to v0, and only assign the
	// zero label to v0 if it is the only feasible candidate. Given the fixed order in which we
	// traverse neighbors of v0, we prioritize "earlier" directions over "later" ones.
	// -path_tracing_BFS: does a BFS flood fill...
	// -fast_marching_method: UNDOCUMENTED
	enum class GridVertexResolutionMethod { NaiveBFS, PathTracingBFS, FastMarchingMethod };
	GridVertexResolutionMethod grid_vertex_resolution_method =
	    GridVertexResolutionMethod::FastMarchingMethod;
	// In case label resolution is performed via path tracing, this parameter determines the method
	// for its execution. Options are:
	// -naive: determine positions of all breaking points, measure distance between each breaking
	// point and each complex grid vertex; this approach is very accurate, but also very costly, used
	// primarily for prototyping
	// -all_breaking_points_per_trace: constructs a trace for each complex grid vertex; when merging
	// two traces, all breaking points encountered by the two traces are stored and used to determine
	// the overall closest breaking point; this approach is constructive, and uses only local data for
	// label resolution; this approach is still very accurate, while being much faster
	// -one_breaking_point_per_trace: constructs a trace for each complex grid vertex; when merging
	// two traces, only the closest breaking point per material is stored and used to determine the
	// overall closest breaking point; this approach loses some accuracy in favor of a slight speed
	// increase
	enum class PathTracingBFSMethod { Naive, AllBreakingPointsPerTrace, OneBreakingPointPerTrace };
	PathTracingBFSMethod path_tracing_BFS_method = PathTracingBFSMethod::Naive;

	// ------------------- Value Transfer
	// Determines which mesh vertices will have their values interpolated onto grid vertices. Options
	// for which mesh vertices are used for interpolating values onto grid vertices are:
	// -none: no mesh vertices, therefore no value transfer happens
	// -all: all mesh vertices
	// -in_complex_cells: mesh vertices in complex cells
	// -in_simple_front: mesh vertices in simple cells bordering complex cells via a grid face
	// -in_complex_cells_plus_simple_front: union of the two previous sets of mesh vertices
	// -on_tris_in_complex_cells: mesh vertices on triangles that intersect complex cells (the
	// vertices themselves can be arbitraily far from a complex region)
	// -on_tris_in_simple_front: mesh vertices on triangles that intersect simple cells bordering
	// complex cells via a grid face (the vertices themselves can be arbitraily far from a complex
	// region)
	// -on_tris_in_complex_cells_plus_simple_front: union of the two previous sets of mesh vertices
	enum class ValueGivingMeshVertices {
		None,
		All,
		InComplexCells,
		InSimpleFront,
		InComplexCellsPlusSimpleFront,
		OnTrisInComplexCells,
		OnTrisInSimpleFront,
		OnTrisInComplexCellsPlusSimpleFront
	};
	ValueGivingMeshVertices value_giving_mesh_vertices =
	    ValueGivingMeshVertices::InComplexCellsPlusSimpleFront;
	// Determines the method for interpolating values from mesh vertices onto grid vertices. Options
	// are:
	// -trilinear: the value of a given value giving mesh vertex is transferred onto the 8 grid
	// vertices of the grid cell that the mesh vertex lies in using trilinear weights
	// -average_in_cell: the value at a given grid vertex is the average of the values of value giving
	// mesh vertices in grid cells adjacent to the grid vertex
	enum class MeshToGridInterpolationMethod { Trilinear, AverageInCell };
	MeshToGridInterpolationMethod mesh_to_grid_interpolation_method =
	    MeshToGridInterpolationMethod::AverageInCell;
	// Determines the method for normalizing values stored on grid vertices. Options are:
	// -none: no normalization of values on grid vertices
	// -num_contributing_values: normalize the value at a grid vertex by the number of mesh vertices
	// that contributed to it
	// -expected_eight_values: normalize the value at a grid vertex by (8/number of contributing mesh
	// vertices); this corresponds to a configuration with one mesh vertex per grid cell, or
	// equivalently one mesh vertex per grid vertex
	// -num_contributing_cells: normalize the values at a grid vertex by the number of nearby grid
	// cells with at least one contributing mesh vertex
	enum class GridValueNormalizationMethod {
		None,
		NumContributingValues,
		ExpectedEightValues,
		NumContributingCells
	};
	GridValueNormalizationMethod grid_value_normalization_method =
	    GridValueNormalizationMethod::NumContributingCells;
	// Determines the method for spreading values stored on grid vertices onto grid vertices without
	// values stored on them. This is done in order to have an estimate of values at grid vertices
	// that didn't contain input mesh vertices, but that had mesh vertices generated in them during
	// marching cubes surface reconstruction. Options are:
	// -none: no spreading, values on grid vertices without values already stored on them are set to
	// zero
	// -flood_fill_onto_all_grid_vertices: values are spread onto all grid vertices via a flood fill
	// starting from those grid vertices that already have values stored on them
	// -flood_fill_onto_complex_region: values are spread onto grid vertices on complex cells via a
	// flood fill starting from vertices that already have values stored on them; to be sure that all
	// grid vertices on complex cells have values assigned, a check is executed after the flood fill
	// finishes, and a warning is given if the check fails; ASK: could it happen that it's impossible
	// to spread values onto all grid vertices in complex cells?
	enum class SpreadingValuesOnGridMethod {
		None,
		FloodFillOntoAllGridVertices,
		FloodFillOntoComplexRegion
	};
	SpreadingValuesOnGridMethod spreading_values_on_grid_method =
	    SpreadingValuesOnGridMethod::FloodFillOntoComplexRegion;
	// Determines the set of mesh vertices that will have values interpolated onto them from the
	// values on grid verticecs. Options are:
	// -none: no mesh vertices will have values interpolated onto them, all new vertices will have
	// values initialized to 0
	// -new: mesh vertices generated via marching cubes will have values interpolated onto them
	// -new_and_front: mesh vertices generated via marching cubes, and vertices generated by cell
	// separation will have values interpolated onto them
	// -all: all mesh vertices (including mesh vertices in the simple region) will have values
	// interpolated onto them
	enum class ValueTakingMeshVertices { None, New, NewAndFront, All };
	ValueTakingMeshVertices value_taking_mesh_vertices = ValueTakingMeshVertices::NewAndFront;
	// Determines whether grid-to-mesh value interpolation is executed before or after mesh upkeep.
	// Options are:
	// -before_mesh_upkeep
	// -after_mesh_upkeep
	enum class GridToMeshInterpolationTiming { BeforeMeshUpkeep, AfterMeshUpkeep };
	GridToMeshInterpolationTiming grid_to_mesh_interpolation_timing =
	    GridToMeshInterpolationTiming::BeforeMeshUpkeep;
	// Determines the method for interpolating values from grid vertices onto mesh vertices. Options
	// are:
	// -trilinear: the value of a given value taking mesh vertex is computed as the trilinear
	// interpolation of values on its adjacent grid verices (8 for a mesh vertex inside a grid cell, 4
	// for a mesh vertex on a grid face, 2 for a mesh vertex on a grid edge)
	// -average_on_cell_vertices: the value at a given value taking mesh vertex is the average of the
	// values on its adjacent grid vertices (8 for a mesh vertex inside a grid cell, 4
	// for a mesh vertex on a grid face, 2 for a mesh vertex on a grid edge)
	enum class GridToMeshInterpolationMethod { Trilinear, AverageOnCellVertices };
	GridToMeshInterpolationMethod grid_to_mesh_interpolation_method =
	    GridToMeshInterpolationMethod::Trilinear;

	// ------------------- Marching Cubes
	// Determines the marching cubes method applied when reconstructung mesh in complex cells. Options
	// are:
	// -8_octant_method: a procedural approach, we conceptually split each complex cell into 8 octant,
	// then consider the 12 connections between pairs of octant, each corresponding to an edge of the
	// complex cell. If materials at the endpoints of the edge don't match, triangles are constructed
	// to separate the octants. Results in a blocky surface.
	// -8_om_plus_optimized_2_mat: UNDOCUMENTED
	enum class MarchingCubesMethod { EightOctantMethod, EightOctantMethodPlusOptimizedTwoMat };
	MarchingCubesMethod marching_cubes_method = MarchingCubesMethod::EightOctantMethod;

	// ------------------- T1 resolver
	// Determines whether T1 resolution is allowed, even if pulling apart any pair of local regions
	// around a central vertex would result in a local area increase.
	bool allow_area_increasing_t1 = true;

	// ------------------- Mesh Improvement
	// Defines the acceptable ratio for the triangle sides. Triangles whose shortest / longest ratio
	// is lower than this value will get removed in the end of the pipeline.
	double slim_triangle_tolerance = 0.3;
	// Minimum allowed length of a mesh edge relative to a grid edge length. For example, value of 0.5
	// means that all triangle edges will be no smaller than half of the grid edge length.
	double min_edge_length_rel_to_grid = 0.5;
	// Maximum allowed length of a mesh edge relative to a grid edge length. For example, value of 2
	// means that all triangle edges will be no larger than twice the grid edge length.
	double max_edge_length_rel_to_grid = 1.5;
	// Maximum allowed angle of any triangle in degrees.
	double max_angle_size_deg = 179.5;
	// Determines whether an edge collapse can completely remove a small tetrahedron.
	bool allow_t2_edge_collapse = false;
	// Determines whether to improve quality only of Marching Cubes triangles or the whole mesh.
	bool improve_only_mc_tris = false;
	// If enabled, runs surface and non-manifold curve smoothing algorithms once before mesh
	// improvement operations.
	bool run_smoothing = true;

	// ------------------- Modules
	// Flags determining which modules to run.
	bool run_grid_labeler = true;
	bool run_complex_cell_detector = true;
	bool run_label_resolver = true;
	bool run_value_transferrer = true;
	bool run_state_saver = true;
	bool run_cell_separator = true;
	bool run_multi_label_marching_cuber = true;
	bool run_mesh_upkeeper = true;

	// ------------------- Rendering
	// Number of smoothing steps performed by JacobiSmoother, when called by SmoothingVisualizer.
	int vis_vertex_smoothing_steps = 5;
	// Determines whether value transfer is expected to be visualized. If yes, values are stored that
	// would otherwise be discarded.
	bool visualize_value_transfer = true;

	// ------------------- Running mode
	// Defines how the program will be run. Options:
	// -fixer: runs only TopoFixer surface tracking step.
	// -scene: runs a predetermined scene; runs the whole simulation and write meshes
	// -interactive: runs a predetermined scene; same as scene, but if in the viewer, pauses every N
	// frames
	// -render: Runs visualization to render a sequence of meshes either interactively or without
	// pauses, which can be useful for to-disk rendering. Only useful in viewer.
	enum class RunMode { Fixer, Scene, Render };
	RunMode run_mode = RunMode::Fixer;

	// Scene steps per update; default = run the whole simulation
	int interactive_mode_steps = std::numeric_limits<int>::max();

	// ------------------- Simulation params
	// Type of the simulation to run with mesh tracker.
	enum class SceneType {
		NotSet,
		NormalFlow,
		ConstantVelocity,
		Zalesak,
		MeshMultiply,
		Curlnoise,
		SmoothInverter,
		Roll,
		TwoRoll,
		GridAdvect
	};
	SceneType scene_type = SceneType::NotSet;
	// Value of the simulation time step.
	double dt = 0.01;
	// Maximum simulation time after which the simulation will stop. If the current simulation time
	// has exactly this value, the simulation will also stop.
	double max_sim_time = 0.0;
	// Specifies how many steps of simulation are taken between two runs of mesher.
	int run_mesher_every_n_steps = 1;
	// The location of grids to be used for advection in GridAdvect.
	std::string grid_advect_dir = "";

	// ------------------- Output
	// Defines if the output should be saved.
	bool should_output_frames = false;
	// Type of an output file, can be ascii format in obj or binary format (bin).
	enum class OutputType { Obj, Bin };
	OutputType output_type = OutputType::Obj;
	// Path to the file that will be saved after mesh finishes.
	std::string output_path = "";
	// Path to an output file where the screenshot will be rendered.
	std::string render_output_path = "";
	// Shifts the whole mesh in all axes by the specified amount
	double shift_mesh_by_constant = 0.0;

	// ------------------- Other
	/* Determines how much debug information is printed, eg.:
	 * 0: nothing is printed
	 * 1: results of individual modules/functions are printed
	 * 2: details on subprocesses of functions/modules are printed
	 * 3: details of geometry/mesh are printed (eg. vertex positions,...).
	 *
	 * Feel free to modify according to your needs.
	 */
	int verbosity = 1;
	// Flag that determines whether the program should pause when an inconsistency is detected.
	bool pause_when_inconsistent = false;
	// Enables timing measurements on per module basis.
	bool measure_module_timings = false;
};
