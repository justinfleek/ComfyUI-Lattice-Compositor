/* ObjFileHandler.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, Arian Etemadi, 2025
 *
 * Class that handles reading and writing data from an obj file.
 */

#include <bitset>
#include <filesystem>

#include "../Mesh3DInterface.h"

class ObjFileHandler {
 public:
	ObjFileHandler() = default;

	// Reads the obj file located at `filepath`  into memory, and calls function
	// `restoreFromGeometry()` to load the data into our data structure. See the description of that
	// function for requirements on vertices, vertex velocities, triangles, and material labels, and
	// how degenerate triangles are handled. Each line in the input file represents one element:
	//
	// -lines representing vertices should be in the format "v x y z", where 'v' indicates the line
	// represents a vertex, and `x`,`y`,`z` should be floating point values representing the vertex's
	// world position. Supports 'vc/vt/vn` OBJ format for specifying the vertex coordinates, textures
	// and normals. If this format is used, all face vertices have to be specified in the exactly the
	// same manner.
	// -lines representing vertex velocities should be in the format "v_vel x y z", where 'v_vel'
	// indicates the line represents a vertex velocity, and `x`,`y`,`z` should be floating point
	// values representing the vertex's global velocity
	// -lines representing triangles should be in the format "f a b c", where 'f' indicates the line
	// represents a triangle (mesh face), and `a`,`b`,`c` should be positive integer values
	// representing the triangle's three vertex indices (inherited from the order in which the
	// vertices are read from the input file). Vertex indexing in this context starts from 1, not 0!
	// -lines representing material label pairs should be in the format "m k l", where 'm' indicates
	// the line represents a material label pair, and `k`,`l` should be non-negative integers
	// representing the material label pair of a triangle. The n-th label pair read from input file is
	// associated to the n-th triangle read from the input file
	//
	// `add_to_existing` parameter determines if the mesh should be cleared before loading.
	// `offset_materials` indicates if materials should be offset by the largest already existing
	// material in the mesh to make them unique. See `mesh.restoreFromGeometry` method for more
	// details.
	// Returns 0 status and statistics on read elements on success.
	// Otherwise, non-zero status and a human-readable error message are returned.
	static std::tuple<int, std::string> readFromFile(Mesh3DInterface* mesh,
	                                                 const std::filesystem::path& filepath,
	                                                 bool add_to_existing = 0,
	                                                 bool offset_materials = 0);

	// Writes the mesh currently in memory into an obj file, listing each vertex with 3 double
	// coordinates, all vertex properties, each triangle with 3 integer vertex indices, and each
	// material pair with 2 integer material labels.
	static std::tuple<int, std::string> writeToFile(Mesh3DInterface* mesh,
	                                                const std::filesystem::path& filepath);

	// Same as above but using already created streams. Mostly useful for testing.
	static std::tuple<int, std::string> readFromStream(Mesh3DInterface* mesh, std::istream& is,
	                                                   bool add_to_existing = 0,
	                                                   bool offset_materials = 0);

	static std::tuple<int, std::string> writeToStream(Mesh3DInterface* mesh, std::ostream& os);

 private:
	// Used to check that all face vertices follow the same format.
	using FaceParserState = std::bitset<4>;

	static std::tuple<int, std::string> parseFaceLine(std::istream& is,
	                                                  std::vector<Vec3i>& triangle_vertices,
	                                                  FaceParserState& face_parser_state);
};