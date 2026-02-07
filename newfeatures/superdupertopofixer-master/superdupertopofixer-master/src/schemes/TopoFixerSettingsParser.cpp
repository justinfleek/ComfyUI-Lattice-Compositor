#include "TopoFixerSettingsParser.h"

#include <fstream>
#include <iostream>
#include <sstream>

#include "../utilities/string_util.h"

std::unique_ptr<TopoFixerSettingsParser> TopoFixerSettingsParser::fromFile(
    std::string_view input_path) {
	auto parser = std::unique_ptr<TopoFixerSettingsParser>(new TopoFixerSettingsParser());
	parser->is_ = std::make_unique<std::ifstream>(input_path.data());
	if (parser->is_->good()) {
		return parser;
	}
	return nullptr;
}

bool TopoFixerSettingsParser::parseIntParam(int* param, std::string&& str) {
	try {
		*param = std::stoi(str);
	} catch (std::exception& e) {
		std::cerr << "--Error parsing setting " << str << ", use default value " << std::endl;
		return false;
	}
	return true;
};

bool TopoFixerSettingsParser::parseDoubleParam(double* param, std::string&& str) {
	try {
		*param = std::stod(str);
	} catch (std::exception& e) {
		std::cerr << "--Error parsing setting " << str << ", use default value " << std::endl;
		return false;
	}
	return true;
}

bool TopoFixerSettingsParser::parseBoolParam(bool* param, std::string&& str) {
	try {
		std::transform(str.begin(), str.end(), str.begin(),
		               [](unsigned char c) { return std::tolower(c); });
		if (str == "false")
			*param = false;
		else if (str == "true")
			*param = true;
		else {
			int val = std::stoi(str);
			if (val == 0)
				*param = false;
			else if (val == 1)
				*param = true;
			else
				return false;
		}
	} catch (std::exception& e) {
		std::cerr << "--Error parsing setting " << str << ", use default value " << std::endl;
		return false;
	}
	return true;
}

bool TopoFixerSettingsParser::parseStringParam(std::string* param, std::string&& str) {
	*param = std::move(str);
	return true;
}

void TopoFixerSettingsParser::parse() {
	int line_counter = 0;
	LineResponse response;
	bool next_line = true;
	do {
		next_line = parseLine(&response);
		line_counter++;
		switch (response) {
			case LineResponse::ONE_TOKEN:
				std::cout << "Line " << line_counter << ": There is only one string token." << std::endl;
				break;
			case LineResponse::TOKEN_UNKNOWN:
				std::cout << "Line " << line_counter << ": Token refers to unknown property." << std::endl;
				break;
			case LineResponse::VALUE_INVALID:
				std::cout << "Line " << line_counter << ": Value invalid for this property." << std::endl;
				break;
		}
	} while (next_line);
}

bool TopoFixerSettingsParser::parseLine(LineResponse* response) {
	*response = LineResponse::OK;

	std::string line;
	std::getline(*is_, line);
	bool ret_val = !is_->eof();

	trim(line);
	if (line.empty() || line.at(0) == '#')
		return ret_val;

	auto first_space =
	    std::find_if(line.begin(), line.end(), [](unsigned char ch) { return std::isspace(ch); });
	if (first_space == line.end())  // only one token -> discard
	{
		*response = LineResponse::ONE_TOKEN;
		return ret_val;
	}

	std::string first_token(line.begin(), first_space);
	line.erase(line.begin(), first_space);
	ltrim(line);
	// line now has the second token, including spaces

	auto fptr = property_setter_map_.find(first_token);
	if (fptr == property_setter_map_.end())
		*response = LineResponse::TOKEN_UNKNOWN;
	else if (!fptr->second(std::move(line)))
		*response = LineResponse::VALUE_INVALID;
	return ret_val;
}

void TopoFixerSettingsParser::buildLookupTable() {
	// Currently, 5 types of property are supported: bool, enum, int, double, and string. To add a
	// property to the parser, you need to do two things: 1) Create a lambda function that calls the
	// appropriate parser function. To do this, copy one of the "auto f_... = [this]..." code snippets
	// for the appropriate property type from below, and adjust it to your specific property. 2) At
	// the end of this function body, add an entry to the property_setter_map_ braced initializer.

	// ------------------- Grid
	auto f_num_grid_cells = [this](std::string&& l) {
		return parseIntParam(&set_.num_grid_cells, std::move(l));
	};
	auto f_grid_bounding_box_style = [this](std::string&& l) {
		using E = TopoFixerSettings::GridBoundingBoxStyle;
		return parseEnumParam(
		    &set_.grid_bounding_box_style,
		    std::map<std::string, E>{{"fixed_cube", E::FixedCube},
		                             {"minmax_cube", E::MinmaxCube},
		                             {"minmax_axis_adjusted_block", E::MinmaxAxisAdjustedBlock}},
		    std::move(l));
	};
	auto f_cube_min_coord = [this](std::string&& l) {
		return parseDoubleParam(&set_.cube_min_coord, std::move(l));
	};
	auto f_cube_max_coord = [this](std::string&& l) {
		return parseDoubleParam(&set_.cube_max_coord, std::move(l));
	};
	auto f_should_perturb_grid = [this](std::string&& l) {
		return parseBoolParam(&set_.should_perturb_grid, std::move(l));
	};

	// ------------------- Mesh
	auto f_input_mesh_file = [this](std::string&& l) {
		return parseStringParam(&set_.input_mesh_file, std::move(l));
	};
	auto f_input_mesh_type = [this](std::string&& l) {
		using E = TopoFixerSettings::InputMeshType;
		return parseEnumParam(&set_.input_mesh_type,
		                      std::map<std::string, E>{{"obj", E::Obj}, {"bin", E::Bin}}, std::move(l));
	};
	auto f_opposite_reconstruction_type = [this](std::string&& l) {
		using E = TopoFixerSettings::OppositeReconstructionType;
		return parseEnumParam(
		    &set_.opposite_reconstruction_type,
		    std::map<std::string, E>{{"geometry", E::Geometry}, {"labels", E::Labels}}, std::move(l));
	};
	auto f_run_input_mesh_consistency_tests = [this](std::string&& l) {
		using E = TopoFixerSettings::InputMeshConsistencyTests;
		return parseEnumParam(
		    &set_.run_input_mesh_consistency_tests,
		    std::map<std::string, E>{{"none", E::None}, {"critical", E::Critical}, {"all", E::All}},
		    std::move(l));
	};
	auto f_triangle_registration_offset = [this](std::string&& l) {
		return parseDoubleParam(&set_.triangle_registration_offset, std::move(l));
	};
	auto f_mesh_short_edge_threshold = [this](std::string&& l) {
		return parseDoubleParam(&set_.mesh_short_edge_threshold, std::move(l));
	};

	// ------------------- Complexity Tests
	auto f_complex_cell_resample_mode = [this](std::string&& l) {
		using E = TopoFixerSettings::ComplexCellResampleMode;
		return parseEnumParam(&set_.complex_cell_resample_mode,
		                      std::map<std::string, E>{{"complex_test", E::ComplexTest},
		                                               {"resample_all", E::ResampleAll}},
		                      std::move(l));
	};
	auto f_edge_geometric_complexity_metric = [this](std::string&& l) {
		using E = TopoFixerSettings::EdgeGeometricComplexityMetric;
		return parseEnumParam(&set_.edge_geometric_complexity_metric,
		                      std::map<std::string, E>{{"none", E::None}, {"inversion", E::Inversion}},
		                      std::move(l));
	};
	auto f_run_deep_edge_test = [this](std::string&& l) {
		return parseBoolParam(&set_.run_deep_edge_test, std::move(l));
	};
	auto f_edge_deep_cell_test_depth = [this](std::string&& l) {
		return parseIntParam(&set_.edge_deep_cell_test_depth, std::move(l));
	};
	auto f_face_geometric_complexity_metric = [this](std::string&& l) {
		using E = TopoFixerSettings::FaceGeometricComplexityMetric;
		return parseEnumParam(&set_.face_geometric_complexity_metric,
		                      std::map<std::string, E>{{"none", E::None}, {"inversion", E::Inversion}},
		                      std::move(l));
	};
	auto f_faces_to_check_for_complexity = [this](std::string&& l) {
		using E = TopoFixerSettings::FacesToCheckForComplexity;
		return parseEnumParam(&set_.faces_to_check_for_complexity,
		                      std::map<std::string, E>{{"all", E::All}, {"front", E::Front}},
		                      std::move(l));
	};
	auto f_complex_face_test = [this](std::string&& l) {
		using E = TopoFixerSettings::ComplexFaceTest;
		return parseEnumParam(
		    &set_.complex_face_test,
		    std::map<std::string, E>{{"quick_reject", E::QuickReject}, {"thorough", E::Thorough}},
		    std::move(l));
	};

	// ------------------- Grid Vertex Resolution
	auto f_grid_vertex_resolution_method = [this](std::string&& l) {
		using E = TopoFixerSettings::GridVertexResolutionMethod;
		return parseEnumParam(&set_.grid_vertex_resolution_method,
		                      std::map<std::string, E>{{"naive_BFS", E::NaiveBFS},
		                                               {"path_tracing_BFS", E::PathTracingBFS},
		                                               {"fast_marching_method", E::FastMarchingMethod}},
		                      std::move(l));
	};
	auto f_path_tracing_BFS_method = [this](std::string&& l) {
		using E = TopoFixerSettings::PathTracingBFSMethod;
		return parseEnumParam(
		    &set_.path_tracing_BFS_method,
		    std::map<std::string, E>{{"naive", E::Naive},
		                             {"all_breaking_points_per_trace", E::AllBreakingPointsPerTrace},
		                             {"one_breaking_point_per_trace", E::OneBreakingPointPerTrace}},
		    std::move(l));
	};

	// ------------------- Value Transfer
	auto f_value_giving_mesh_vertices = [this](std::string&& l) {
		using E = TopoFixerSettings::ValueGivingMeshVertices;
		return parseEnumParam(
		    &set_.value_giving_mesh_vertices,
		    std::map<std::string, E>{
		        {"none", E::None},
		        {"all", E::All},
		        {"in_complex_cells", E::InComplexCells},
		        {"in_simple_front", E::InSimpleFront},
		        {"in_complex_cells_plus_simple_front", E::InComplexCellsPlusSimpleFront},
		        {"on_tris_in_complex_cells", E::OnTrisInComplexCells},
		        {"on_tris_in_simple_front", E::OnTrisInSimpleFront},
		        {"on_tris_in_complex_cells_plus_simple_front", E::OnTrisInComplexCellsPlusSimpleFront}},
		    std::move(l));
	};
	auto f_mesh_to_grid_interpolation_method = [this](std::string&& l) {
		using E = TopoFixerSettings::MeshToGridInterpolationMethod;
		return parseEnumParam(&set_.mesh_to_grid_interpolation_method,
		                      std::map<std::string, E>{{"trilinear", E::Trilinear},
		                                               {"average_in_cell", E::AverageInCell}},
		                      std::move(l));
	};
	auto f_grid_value_normalization_method = [this](std::string&& l) {
		using E = TopoFixerSettings::GridValueNormalizationMethod;
		return parseEnumParam(
		    &set_.grid_value_normalization_method,
		    std::map<std::string, E>{{"none", E::None},
		                             {"num_contributing_values", E::NumContributingValues},
		                             {"expected_eight_values", E::ExpectedEightValues},
		                             {"num_contributing_cells", E::NumContributingCells}},
		    std::move(l));
	};
	auto f_spreading_values_on_grid_method = [this](std::string&& l) {
		using E = TopoFixerSettings::SpreadingValuesOnGridMethod;
		return parseEnumParam(
		    &set_.spreading_values_on_grid_method,
		    std::map<std::string, E>{
		        {"none", E::None},
		        {"flood_fill_onto_all_grid_vertices", E::FloodFillOntoAllGridVertices},
		        {"flood_fill_onto_complex_region", E::FloodFillOntoComplexRegion}},
		    std::move(l));
	};
	auto f_value_taking_mesh_vertices = [this](std::string&& l) {
		using E = TopoFixerSettings::ValueTakingMeshVertices;
		return parseEnumParam(
		    &set_.value_taking_mesh_vertices,
		    std::map<std::string, E>{
		        {"none", E::None}, {"new", E::New}, {"new_and_front", E::NewAndFront}, {"all", E::All}},
		    std::move(l));
	};
	auto f_grid_to_mesh_interpolation_timing = [this](std::string&& l) {
		using E = TopoFixerSettings::GridToMeshInterpolationTiming;
		return parseEnumParam(&set_.grid_to_mesh_interpolation_timing,
		                      std::map<std::string, E>{{"before_mesh_upkeep", E::BeforeMeshUpkeep},
		                                               {"after_mesh_upkeep", E::AfterMeshUpkeep}},
		                      std::move(l));
	};
	auto f_grid_to_mesh_interpolation_method = [this](std::string&& l) {
		using E = TopoFixerSettings::GridToMeshInterpolationMethod;
		return parseEnumParam(
		    &set_.grid_to_mesh_interpolation_method,
		    std::map<std::string, E>{{"trilinear", E::Trilinear},
		                             {"average_on_cell_vertices", E::AverageOnCellVertices}},
		    std::move(l));
	};

	// ------------------- Marching Cubes
	auto f_marching_cubes_method = [this](std::string&& l) {
		using E = TopoFixerSettings::MarchingCubesMethod;
		return parseEnumParam(&set_.marching_cubes_method,
		                      std::map<std::string, E>{{"8_octant_method", E::EightOctantMethod},
		                                               {"8_om_plus_optimized_2_mat",
		                                                E::EightOctantMethodPlusOptimizedTwoMat}},
		                      std::move(l));
	};

	// ------------------- T1 resolver
	auto f_allow_area_increasing_t1 = [this](std::string&& l) {
		return parseBoolParam(&set_.allow_area_increasing_t1, std::move(l));
	};

	// ------------------- Mesh Improvement
	auto f_slim_triangle_tolerance = [this](std::string&& l) {
		return parseDoubleParam(&set_.slim_triangle_tolerance, std::move(l));
	};
	auto f_min_edge_length_rel_to_grid = [this](std::string&& l) {
		return parseDoubleParam(&set_.min_edge_length_rel_to_grid, std::move(l));
	};
	auto f_max_edge_length_rel_to_grid = [this](std::string&& l) {
		return parseDoubleParam(&set_.max_edge_length_rel_to_grid, std::move(l));
	};
	auto f_max_angle_size_deg = [this](std::string&& l) {
		return parseDoubleParam(&set_.max_angle_size_deg, std::move(l));
	};
	auto f_allow_t2_edge_collapse = [this](std::string&& l) {
		return parseBoolParam(&set_.allow_t2_edge_collapse, std::move(l));
	};
	auto f_improve_only_mc_tris = [this](std::string&& l) {
		return parseBoolParam(&set_.improve_only_mc_tris, std::move(l));
	};
	auto f_run_smoothing = [this](std::string&& l) {
		return parseBoolParam(&set_.run_smoothing, std::move(l));
	};

	// ------------------- Modules
	auto f_run_grid_labeler = [this](std::string&& l) {
		return parseBoolParam(&set_.run_grid_labeler, std::move(l));
	};
	auto f_run_complex_cell_detector = [this](std::string&& l) {
		return parseBoolParam(&set_.run_complex_cell_detector, std::move(l));
	};
	auto f_run_label_resolver = [this](std::string&& l) {
		return parseBoolParam(&set_.run_label_resolver, std::move(l));
	};
	auto f_run_value_transferrer = [this](std::string&& l) {
		return parseBoolParam(&set_.run_value_transferrer, std::move(l));
	};
	auto f_run_state_saver = [this](std::string&& l) {
		return parseBoolParam(&set_.run_state_saver, std::move(l));
	};
	auto f_run_cell_separator = [this](std::string&& l) {
		return parseBoolParam(&set_.run_cell_separator, std::move(l));
	};
	auto f_run_multi_label_marching_cuber = [this](std::string&& l) {
		return parseBoolParam(&set_.run_multi_label_marching_cuber, std::move(l));
	};
	auto f_run_mesh_upkeeper = [this](std::string&& l) {
		return parseBoolParam(&set_.run_mesh_upkeeper, std::move(l));
	};

	// ------------------- Rendering
	auto f_vis_vertex_smoothing_steps = [this](std::string&& l) {
		return parseIntParam(&set_.vis_vertex_smoothing_steps, std::move(l));
	};
	auto f_visualize_value_transfer = [this](std::string&& l) {
		return parseBoolParam(&set_.visualize_value_transfer, std::move(l));
	};

	// ------------------- Runnning mode
	auto f_run_mode = [this](std::string&& l) {
		using E = TopoFixerSettings::RunMode;
		return parseEnumParam(
		    &set_.run_mode,
		    std::map<std::string, E>{{"fixer", E::Fixer}, {"scene", E::Scene}, {"render", E::Render}},
		    std::move(l));
	};
	auto f_interactive_steps = [this](std::string&& l) {
		return parseIntParam(&set_.interactive_mode_steps, std::move(l));
	};

	// ------------------- Simulation params
	auto f_scene_type = [this](std::string&& l) {
		using E = TopoFixerSettings::SceneType;
		return parseEnumParam(&set_.scene_type,
		                      std::map<std::string, E>{
		                          {"not_set", E::NotSet},
		                          {"normal_flow", E::NormalFlow},
		                          {"constant_velocity", E::ConstantVelocity},
		                          {"zalesak", E::Zalesak},
		                          {"mesh_multiply", E::MeshMultiply},
		                          {"curlnoise", E::Curlnoise},
		                          {"smooth_inverter", E::SmoothInverter},
		                          {"roll", E::Roll},
		                          {"two_roll", E::TwoRoll},
		                          {"grid_advect", E::GridAdvect},
		                      },
		                      std::move(l));
	};
	auto f_dt = [this](std::string&& l) { return parseDoubleParam(&set_.dt, std::move(l)); };
	auto f_max_sim_time = [this](std::string&& l) {
		return parseDoubleParam(&set_.max_sim_time, std::move(l));
	};
	auto f_run_mesher_every_n_steps = [this](std::string&& l) {
		return parseIntParam(&set_.run_mesher_every_n_steps, std::move(l));
	};
	auto f_grid_advect_dir = [this](std::string&& l) {
		return parseStringParam(&set_.grid_advect_dir, std::move(l));
	};

	// ------------------- Output
	auto f_should_output_frames = [this](std::string&& l) {
		return parseBoolParam(&set_.should_output_frames, std::move(l));
	};
	auto f_output_type = [this](std::string&& l) {
		using E = TopoFixerSettings::OutputType;
		return parseEnumParam(&set_.output_type,
		                      std::map<std::string, E>{{"obj", E::Obj}, {"bin", E::Bin}}, std::move(l));
	};
	auto f_output_path = [this](std::string&& l) {
		return parseStringParam(&set_.output_path, std::move(l));
	};
	auto f_render_output_path = [this](std::string&& l) {
		return parseStringParam(&set_.render_output_path, std::move(l));
	};
	auto f_shift_mesh_by_constant = [this](std::string&& l) {
		return parseDoubleParam(&set_.shift_mesh_by_constant, std::move(l));
	};

	// ------------------- Other
	auto f_verbosity = [this](std::string&& l) {
		return parseIntParam(&set_.verbosity, std::move(l));
	};
	auto f_pause_when_inconsistent = [this](std::string&& l) {
		return parseBoolParam(&set_.pause_when_inconsistent, std::move(l));
	};
	auto f_measure_module_timings = [this](std::string&& l) {
		return parseBoolParam(&set_.measure_module_timings, std::move(l));
	};

	property_setter_map_ = std::unordered_map<std::string, std::function<bool(std::string && l)>>{
	    // ------------------- Grid
	    {"num_grid_cells", f_num_grid_cells},
	    {"grid_bounding_box_style", f_grid_bounding_box_style},
	    {"cube_min_coord", f_cube_min_coord},
	    {"cube_max_coord", f_cube_max_coord},
	    {"should_perturb_grid", f_should_perturb_grid},
	    // ------------------- Mesh
	    {"input_mesh_file", f_input_mesh_file},
	    {"input_mesh_type", f_input_mesh_type},
	    {"opposite_reconstruction_type", f_opposite_reconstruction_type},
	    {"run_input_mesh_consistency_tests", f_run_input_mesh_consistency_tests},
	    {"triangle_registration_offset", f_triangle_registration_offset},
	    {"mesh_short_edge_threshold", f_mesh_short_edge_threshold},
	    // ------------------- Complexity Tests
	    {"complex_cell_resample_mode", f_complex_cell_resample_mode},
	    {"edge_geometric_complexity_metric", f_edge_geometric_complexity_metric},
	    {"run_deep_edge_test", f_run_deep_edge_test},
	    {"edge_deep_cell_test_depth", f_edge_deep_cell_test_depth},
	    {"face_geometric_complexity_metric", f_face_geometric_complexity_metric},
	    {"faces_to_check_for_complexity", f_faces_to_check_for_complexity},
	    {"complex_face_test", f_complex_face_test},
	    // ------------------- Grid Vertex Resolution
	    {"grid_vertex_resolution_method", f_grid_vertex_resolution_method},
	    {"path_tracing_BFS_method", f_path_tracing_BFS_method},
	    // ------------------- Value Transfer
	    {"value_giving_mesh_vertices", f_value_giving_mesh_vertices},
	    {"mesh_to_grid_interpolation_method", f_mesh_to_grid_interpolation_method},
	    {"grid_value_normalization_method", f_grid_value_normalization_method},
	    {"spreading_values_on_grid_method", f_spreading_values_on_grid_method},
	    {"value_taking_mesh_vertices", f_value_taking_mesh_vertices},
	    {"grid_to_mesh_interpolation_timing", f_grid_to_mesh_interpolation_timing},
	    {"grid_to_mesh_interpolation_method", f_grid_to_mesh_interpolation_method},
	    // ------------------- Marching Cubes
	    {"marching_cubes_method", f_marching_cubes_method},
	    // ------------------- T1 resolver
	    {"allow_area_increasing_t1", f_allow_area_increasing_t1},
	    // ------------------- Mesh Improvement
	    {"slim_triangle_tolerance", f_slim_triangle_tolerance},
	    {"min_edge_length_rel_to_grid", f_min_edge_length_rel_to_grid},
	    {"max_edge_length_rel_to_grid", f_max_edge_length_rel_to_grid},
	    {"max_angle_size_deg", f_max_angle_size_deg},
	    {"allow_t2_edge_collapse", f_allow_t2_edge_collapse},
	    {"improve_only_mc_tris", f_improve_only_mc_tris},
	    {"run_smoothing", f_run_smoothing},
	    // ------------------- Modules
	    {"run_grid_labeler", f_run_grid_labeler},
	    {"run_complex_cell_detector", f_run_complex_cell_detector},
	    {"run_label_resolver", f_run_label_resolver},
	    {"run_value_transferrer", f_run_value_transferrer},
	    {"run_state_saver", f_run_state_saver},
	    {"run_cell_separator", f_run_cell_separator},
	    {"run_multi_label_marching_cuber", f_run_multi_label_marching_cuber},
	    {"run_mesh_upkeeper", f_run_mesh_upkeeper},
	    // ------------------- Rendering
	    {"vis_vertex_smoothing_steps", f_vis_vertex_smoothing_steps},
	    {"visualize_value_transfer", f_visualize_value_transfer},
	    // ------------------- Runnning mode
	    {"run_mode", f_run_mode},
	    {"interactive_steps", f_interactive_steps},
	    // ------------------- Simulation params
	    {"scene_type", f_scene_type},
	    {"dt", f_dt},
	    {"max_sim_time", f_max_sim_time},
	    {"run_mesher_every_n_steps", f_run_mesher_every_n_steps},
	    {"grid_advect_dir", f_grid_advect_dir},
	    // ------------------- Output
	    {"should_output_frames", f_should_output_frames},
	    {"output_type", f_output_type},
	    {"output_path", f_output_path},
	    {"render_output_path", f_render_output_path},
	    {"shift_mesh_by_constant", f_shift_mesh_by_constant},
	    // ------------------- Other
	    {"verbosity", f_verbosity},
	    {"pause_when_inconsistent", f_pause_when_inconsistent},
	    {"measure_module_timings", f_measure_module_timings}};
}
