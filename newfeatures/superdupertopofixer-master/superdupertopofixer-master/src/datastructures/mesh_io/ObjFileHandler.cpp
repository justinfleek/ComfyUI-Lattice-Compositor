#include "ObjFileHandler.h"

#include <filesystem>
#include <sstream>
#include <string>

#include "../../utilities/string_util.h"

std::tuple<int, std::string> ObjFileHandler::readFromFile(Mesh3DInterface* mesh,
                                                          const std::filesystem::path& filepath,
                                                          bool add_to_existing,
                                                          bool offset_materials) {
	if (!std::filesystem::exists(filepath)) {
		return {1, "-ERROR: file (" + filepath.string() + ") does not exist. \n"};
	}
	// check if the file can be opened
	std::ifstream is(filepath);
	if (!is.is_open()) {
		return {2, "-ERROR: file (" + filepath.string() + ") could not be opened. \n"};
	}
	auto [status, message] = readFromStream(mesh, is, add_to_existing, offset_materials);
	if (status == 0) {
		message += "Finished reading file: (" + filepath.string() + ")\n";
	}
	return {status, message};
}

std::tuple<int, std::string> ObjFileHandler::writeToFile(Mesh3DInterface* mesh,
                                                         const std::filesystem::path& filepath) {
	std::ofstream obj_file(filepath);
	if (!obj_file.is_open()) {
		return {2, "-ERROR: file (" + filepath.string() + ") could not be opened. \n"};
	}

	writeToStream(mesh, obj_file);

	std::ostringstream status;
	status << "-corner table saved in (" << filepath << ")" << std::endl;
	status << "====================================================================================="
	       << std::endl;
	return {0, status.str()};
}

std::tuple<int, std::string> ObjFileHandler::readFromStream(Mesh3DInterface* mesh, std::istream& is,
                                                            bool add_to_existing,
                                                            bool offset_materials) {
	// vectors to hold the data read from the input file
	std::vector<Vec3i> triangle_vertices;
	std::vector<Vec3d> vertex_positions;
	std::vector<VertexProperties> vertex_properties;
	std::vector<Vec2i> material_labels;

	double x, y, z;              // coordiates of a vertex
	double x_vel, y_vel, z_vel;  // velocity of a vertex
	VertexProperties vp;         // properties of a vertex
	int lr, ll;                  // materials on left/right side of a triangle
	FaceParserState face_parser_state;
	size_t current_line = 0;

	// read contents of the input file
	while (!is.eof()) {
		std::string keyword;
		is >> keyword;

		if (keyword == "v")  // vertex input
		{
			is >> x >> y >> z;
			vertex_positions.push_back({x, y, z});

		} else if (keyword ==
		           "v_vel")  // vertex velocity input, for backward compatibility with older files
		{
			is >> x_vel >> y_vel >> z_vel;
			vp = VertexProperties();
			vp.setVelocity({x_vel, y_vel, z_vel});
			vertex_properties.push_back(vp);
		}  // IMPORTANT: files are expected to specify either v_vel or v_props, not both.
		else if (keyword == "v_props")  // vertex properties input
		{
			is >> vp;
			vertex_properties.push_back(vp);
		} else if (keyword == "f")  // triangle input (f for face)
		{
			auto [status, message] = parseFaceLine(is, triangle_vertices, face_parser_state);
			if (status != 0) {
				message += " Occured at line " + std::to_string(current_line) + "\n";
				return {4, message};
			}
		} else if (keyword == "m")  // triangle labels (materials) input, we assume the first label
		                            // corresponds to the side into which right-hand-rule normal points
		{
			is >> lr >> ll;
			material_labels.push_back({lr, ll});
		}
		current_line++;
	}

	assert(vertex_properties.size() == 0 || vertex_properties.size() == vertex_positions.size());

	// fill the input data into our data structure
	int result = mesh->restoreFromGeometry(triangle_vertices, vertex_positions, vertex_properties,
	                                       material_labels, add_to_existing, offset_materials);
	if (result != 0) {
		return {3, "-ERROR: file cannot be restored into memory.\n"};
	}

	std::ostringstream read_properties;
	read_properties << "-from file were read:\n"
	                << "---" << vertex_positions.size() << " vertex positions\n"
	                << "---" << vertex_properties.size() << " vertex properties\n"
	                << "---" << triangle_vertices.size() << " triangle vertex indices\n"
	                << "---" << material_labels.size() << " material label pairs\n";
	return {0, read_properties.str()};
}

std::tuple<int, std::string> ObjFileHandler::writeToStream(Mesh3DInterface* mesh,
                                                           std::ostream& os) {
	mesh->orderLabelsOnManifoldPatches();

	// map that assignes indices to vertices, used to print indices of triangle vertices
	absl::flat_hash_map<Mesh3DVertex*, int> vertices_indices;

	// write vertices into file and assign indices to them
	int v_count = 1;
	for (Mesh3DVertex* vertex : mesh->ListVertices()) {
		os << "v " << vertex->getCoords() << std::endl;
		vertices_indices.insert({vertex, v_count});
		v_count++;
	}
	// write vertex properties into file
	for (Mesh3DVertex* vertex : mesh->ListVertices()) {
		os << "v_props " << vertex->getProperties() << std::endl;
	}
	// write triangles into file
	for (Mesh3DTriangle* triangle : mesh->ListTriangles()) {
		os << "f " << vertices_indices.at(triangle->getVertex(0)) << " "
		   << vertices_indices.at(triangle->getVertex(1)) << " "
		   << vertices_indices.at(triangle->getVertex(2)) << std::endl;
	}
	// write material pairs into file
	for (Mesh3DTriangle* triangle : mesh->ListTriangles()) {
		os << "m " << triangle->getLabel(0) << " " << triangle->getLabel(1) << std::endl;
	}
	return {0, ""};
}

std::tuple<int, std::string> ObjFileHandler::parseFaceLine(std::istream& is,
                                                           std::vector<Vec3i>& triangle_vertices,
                                                           FaceParserState& face_parser_state) {
	std::array<Vec3i, 3> tri_ids;
	for (int token_id = 0; token_id < 3; ++token_id) {
		std::string token;
		is >> token;

		std::vector<std::string> parts = split(token, "/");
		if (parts.size() > 3) {
			return {1, "Line has more than 3 values divided by a slash."};
		}

		FaceParserState token_state;
		for (size_t part_id = 0; part_id < parts.size(); ++part_id) {
			const std::string& part = parts[part_id];
			if (part.empty()) {
				continue;
			}
			// obj files start indexing from 1, therefore we have to decrease all indices by 1
			tri_ids[part_id][token_id] = std::stoi(part) - 1;
			token_state.set(part_id);
		}

		if (face_parser_state.none()) {
			face_parser_state = token_state;
		}

		if (face_parser_state != token_state) {
			return {1, "Mixing various types of face specification is not supported."};
		}
	}
	triangle_vertices.push_back(tri_ids[0]);
	return {0, ""};
}
