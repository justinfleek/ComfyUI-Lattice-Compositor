/* Grid3DInterface.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the implementation file for the grid interface. Functions that are uniform over all
 * implementations of the grid should be implemented here.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "Grid3DInterface.h"

#include <assert.h> /* assert */

//------------------------------------------------------------
// constructors
//------------------------------------------------------------

// default constructor
Grid3DInterface::Grid3DInterface() {
	// default (mostly nonsense) values
	nx = 10;
	ny = 10;
	nz = 10;
	x0 = 0.0;
	y0 = 0.0;
	z0 = 0.0;
	cell_dx = 0.1;

	// precompute helper variables
	nynz = ny * nz;
	num_cells = nx * nynz;
	nynz3 = nynz * 3;
	nz3 = nz * 3;
}

Grid3DInterface::Grid3DInterface(const long long grid_x, const long long grid_y,
                                 const long long grid_z, const double origin_x,
                                 const double origin_y, const double origin_z, const double dx) {
	nx = grid_x;
	ny = grid_y;
	nz = grid_z;
	x0 = origin_x;
	y0 = origin_y;
	z0 = origin_z;
	cell_dx = dx;

	// precompute helper variables for calculations involving grid sizes
	nynz = ny * nz;
	num_cells = nx * nynz;
	nynz3 = nynz * 3;
	nz3 = nz * 3;

	// precompute helper variables for calculations involving grid sizes one larger in each dimension
	nxp1 = nx + 1;
	nyp1 = ny + 1;
	nzp1 = nz + 1;
	nyp1nzp1 = (ny + 1) * (nz + 1);
	nyp1nzp13 = nyp1nzp1 * 3;
	nzp13 = nzp1 * 3;
}

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// initialization of regular grid
//
// input:
//		integers grid_x, grid_y, grid_z for the number of cells in each dimension
//		doubles origin_x, origin_y, origin_z for the physical location of the bottom corner of the
// grid
//      double dx for the physical length of a grid edge (grid cells are cubic, so dx is also
// the height and length, dx^2 is the area of a face, and dx^3 is cell volume
//
//	This function initializes the helper variables necessary to perform basic operations like
// encoding vertices/edges/faces/cells as IDs, returning physical locations of vertices, etc.
void Grid3DInterface::init(const long long grid_x, long long grid_y, long long grid_z,
                           double origin_x, double origin_y, double origin_z, const double dx) {
	nx = grid_x;
	ny = grid_y;
	nz = grid_z;
	x0 = origin_x;
	y0 = origin_y;
	z0 = origin_z;
	cell_dx = dx;

	// precompute helper variables for calculations involving grid sizes
	nynz = ny * nz;
	num_cells = nx * nynz;
	nynz3 = nynz * 3;
	nz3 = nz * 3;

	// precompute helper variables for calculations involving grids that are one larger in each
	// dimension
	//		for example, the number of cells in a row is nx, but number of vertices in a row is (nx+1).
	nxp1 = nx + 1;
	nyp1 = ny + 1;
	nzp1 = nz + 1;
	nyp1nzp1 = (ny + 1) * (nz + 1);
	nyp1nzp13 = nyp1nzp1 * 3;
	nzp13 = nzp1 * 3;
}

/////////////////////////////
//	functions which take in a unique integer ID of a grid[vertex, edge, face, cell] and output(i, j,
// k, orient) coordinates

// this function inverts the ID computation ID = (i*(ny+1)*(nz+1) + j*(nz+1) + k);
// and stores the result in the input (i,j,k) parameters.
//		... note that the calculation uses dimensions + 1, because there will be more 1 vertex (and
// edges, faces) along each dimension than cells
// input integer vertex ID vert_id
void Grid3DInterface::get_vertex_coords(const long long vert_id, long long& i, long long& j,
                                        long long& k) const {
	i = vert_id / nyp1nzp1;                  // number of rectangular plates of size (ny+1)*(nz+1)
	long long tmp = vert_id - i * nyp1nzp1;  // tmp = remainder after subtracting off i plates of
	                                         // (ny+1)*(nz+1) vertices each
	j = tmp / nzp1;                          // number of rows of (nz+1) vertices in the remainder
	k = tmp - j * nzp1;  // remaining number of vertices after subtracting the rows
}

// this function inverts the ID computation ID = (i*(ny+1)*(nz+1)*3 + j*(nz+1)*3 + k*3 + orient);
// and stores the result in the input (i,j,k,orient) parameters
// input integer edge ID edge_id
void Grid3DInterface::get_edge_coords(const long long edge_id, long long& i, long long& j,
                                      long long& k, long long& orient) const {
	i = edge_id / nyp1nzp13;
	long long tmp = edge_id - i * nyp1nzp13;
	j = tmp / nzp13;
	tmp = tmp - j * nzp13;
	k = tmp / 3;
	orient = tmp - k * 3;

	assert(orient >= 0 && orient <= 2);
}

// this function inverts the ID computation ID = (i*(ny+1)*(nz+1)*3 + j*(nz+1)*3 + k*3 + orient);
// and stores the result in the input (i,j,k,orient) parameters
// input integer face ID face_id
void Grid3DInterface::get_face_coords(const long long face_id, long long& i, long long& j,
                                      long long& k, long long& orient) const {
	// functionally the same as edge coordinates. face(i,j,k,o) has the same ID as edge(i,j,k,o).
	get_edge_coords(face_id, i, j, k, orient);
}

// this function inverts the ID computation ID = (i*(ny+1)*(nz+1) + j*(nz+1) + k);
// and stores the result in the input (i,j,k) parameters
// input integer cell ID cell_id
void Grid3DInterface::get_cell_coords(const long long cell_id, long long& i, long long& j,
                                      long long& k) const {
	// functionally the same as vertex coordinates. cell(i,j,k) has the same ID as vertex(i,j,k).
	get_vertex_coords(cell_id, i, j, k);
}

/////////////////////////////////
// functions which return a list of neighboring cells/faces/edges/vertices
//
//		These functions use the connectivity and topology of the grid to return a list of neighboring
// grid primitives.
// 		8 cells touch a vertex
// 		4 cells touch an edge
// 		2 cells touch a face
//      12 faces touch a vertex
// 		4 faces touch an edge
// 		6 faces touch a cell
// 		6 edges touch a vertex
//      4 edges touch a face
// 		12 edges touch a cell
// 		2 vertices touch an edge
// 		4 vertices touch a face
// 		8 vertices touch a cell
//
//		Edge with coordinates (i,j,k) and orientation 0 is the edge from vertex(i,j,k) to
// vertex(i+1,j,k)
// 		Edge with coordinates (i,j,k) and orientation 1 is the edge from vertex(i,j,k) to
// vertex(i,j+1,k)
// 		Edge with coordinates (i,j,k) and orientation 2 is the edge from vertex(i,j,k) to
// vertex(i,j,k+1)
//
//		Face with coordinates (i,j,k) and orientation 0 is the face in cell (i,j,k) containing vertex
// (i,j,k) with normal (1,0,0)
// 		Face with coordinates (i,j,k) and orientation 1 is the face in cell (i,j,k) containing vertex
// (i,j,k) with normal (0,1,0)
// 		Face with coordinates (i,j,k) and  orientation 2 is the face in cell (i,j,k) containing vertex
// (i,j,k) with normal (0,0,1)
//
//////////////////////////////////

// 8 cells touch a vertex
// input integer vertex coordinates (i,j,k)
// output a list of integer IDs of all cells which touch this vertex
//		...do not return any cells that are out of bounds
std::vector<long long> Grid3DInterface::get_cells_neighboring_vertex(const long long i,
                                                                     const long long j,
                                                                     const long long k) const {
	std::vector<long long> cells;
	add_cell_if_inbounds(i, j, k, cells);
	add_cell_if_inbounds(i - 1, j, k, cells);
	add_cell_if_inbounds(i, j - 1, k, cells);
	add_cell_if_inbounds(i, j, k - 1, cells);
	add_cell_if_inbounds(i - 1, j - 1, k, cells);
	add_cell_if_inbounds(i - 1, j, k - 1, cells);
	add_cell_if_inbounds(i, j - 1, k - 1, cells);
	add_cell_if_inbounds(i - 1, j - 1, k - 1, cells);
	return cells;
}

// 8 cells touch a vertex
// input integer vertex ID vertex_id
// output a list of integer IDs of all cells which touch this vertex
//		...do not return any cells that are out of bounds
std::vector<long long> Grid3DInterface::get_cells_neighboring_vertex(
    const long long vertex_id) const {
	long long i, j, k;
	get_vertex_coords(vertex_id, i, j, k);
	return get_cells_neighboring_vertex(i, j, k);
}

// 4 cells touch an edge
// input integer edge coordinates (i,j,k,orient)
// output a list of integer IDs of all cells which touch this edge
//		...do not return any cells that are out of bounds
std::vector<long long> Grid3DInterface::get_cells_neighboring_edge(const long long i,
                                                                   const long long j,
                                                                   const long long k,
                                                                   const long long orient) const {
	std::vector<long long> cells;

	if (orient == 0) {
		add_cell_if_inbounds(i, j, k, cells);
		add_cell_if_inbounds(i, j - 1, k, cells);
		add_cell_if_inbounds(i, j, k - 1, cells);
		add_cell_if_inbounds(i, j - 1, k - 1, cells);
	} else if (orient == 1) {
		add_cell_if_inbounds(i, j, k, cells);
		add_cell_if_inbounds(i - 1, j, k, cells);
		add_cell_if_inbounds(i, j, k - 1, cells);
		add_cell_if_inbounds(i - 1, j, k - 1, cells);
	} else if (orient == 2) {
		add_cell_if_inbounds(i, j, k, cells);
		add_cell_if_inbounds(i - 1, j, k, cells);
		add_cell_if_inbounds(i, j - 1, k, cells);
		add_cell_if_inbounds(i - 1, j - 1, k, cells);
	} else {
		std::cout << "get_cells_neighboring_edge(" << i << "," << j << "," << k << "," << orient
		          << ") has impossible orientation" << std::endl;
		exit(1);
	}

	return cells;
}
// 4 cells touch an edge
// input integer edge ID edge_id
// output a list of integer IDs of all cells which touch this edge
//		...do not return any cells that are out of bounds
std::vector<long long> Grid3DInterface::get_cells_neighboring_edge(const long long edge_id) const {
	long long i, j, k, o;
	get_edge_coords(edge_id, i, j, k, o);
	return get_cells_neighboring_edge(i, j, k, o);
}

std::vector<long long> Grid3DInterface::get_cells_neighboring_cell(const long long i,
                                                                   const long long j,
                                                                   const long long k) const {
	std::vector<long long> cells;
	add_cell_if_inbounds(i - 1, j, k, cells);
	add_cell_if_inbounds(i + 1, j, k, cells);
	add_cell_if_inbounds(i, j - 1, k, cells);
	add_cell_if_inbounds(i, j + 1, k, cells);
	add_cell_if_inbounds(i, j, k - 1, cells);
	add_cell_if_inbounds(i, j, k + 1, cells);
	return cells;
}

std::vector<long long> Grid3DInterface::get_cells_neighboring_cell(const long long cell_id) const {
	long long i, j, k;
	get_cell_coords(cell_id, i, j, k);
	return get_cells_neighboring_cell(i, j, k);
}

// 2 cells touch a face
// input integer face coordinates (i,j,k,orient)
// output a list of integer IDs of all cells which touch this face
//		...do not return any cells that are out of bounds
std::vector<long long> Grid3DInterface::get_cells_neighboring_face(const long long i,
                                                                   const long long j,
                                                                   const long long k,
                                                                   const long long orient) const {
	std::vector<long long> cells;

	if (orient == 0) {
		add_cell_if_inbounds(i, j, k, cells);
		add_cell_if_inbounds(i - 1, j, k, cells);
	} else if (orient == 1) {
		add_cell_if_inbounds(i, j, k, cells);
		add_cell_if_inbounds(i, j - 1, k, cells);
	} else if (orient == 2) {
		add_cell_if_inbounds(i, j, k, cells);
		add_cell_if_inbounds(i, j, k - 1, cells);
	} else {
		std::cout << "get_cells_neighboring_face(" << i << "," << j << "," << k << "," << orient
		          << ") has impossible orientation" << std::endl;
		exit(1);
	}

	return cells;
}

// 2 cells touch a face
// input integer face ID face_id
// output a list of integer IDs of all cells which touch this face
//		...do not return any cells that are out of bounds
std::vector<long long> Grid3DInterface::get_cells_neighboring_face(const long long face_id) const {
	long long i, j, k, o;
	get_face_coords(face_id, i, j, k, o);
	return get_cells_neighboring_face(i, j, k, o);
}

//	12 faces touch a vertex
// input integer vertex coordinates (i,j,k)
// output a list of integer IDs of all faces which touch this vertex
//		...do not return any faces that are out of bounds
std::vector<long long> Grid3DInterface::get_faces_neighboring_vertex(const long long i,
                                                                     const long long j,
                                                                     const long long k) const {
	std::vector<long long> faces;

	add_face_if_inbounds(i, j, k, 0, faces);
	add_face_if_inbounds(i, j - 1, k, 0, faces);
	add_face_if_inbounds(i, j, k - 1, 0, faces);
	add_face_if_inbounds(i, j - 1, k - 1, 0, faces);

	add_face_if_inbounds(i, j, k, 1, faces);
	add_face_if_inbounds(i - 1, j, k, 1, faces);
	add_face_if_inbounds(i, j, k - 1, 1, faces);
	add_face_if_inbounds(i - 1, j, k - 1, 1, faces);

	add_face_if_inbounds(i, j, k, 2, faces);
	add_face_if_inbounds(i - 1, j, k, 2, faces);
	add_face_if_inbounds(i, j - 1, k, 2, faces);
	add_face_if_inbounds(i - 1, j - 1, k, 2, faces);

	return faces;
}

//	12 faces touch a vertex
// input integer vertex ID vertex_id
// output a list of integer IDs of all faces which touch this vertex
std::vector<long long> Grid3DInterface::get_faces_neighboring_vertex(
    const long long vertex_id) const {
	long long i, j, k;
	get_vertex_coords(vertex_id, i, j, k);
	return get_faces_neighboring_vertex(i, j, k);
}

//	4 faces touch an edge
// input integer edge coordinates (i,j,k,orient)
// output a list of integer IDs of all faces which touch this edge
std::vector<long long> Grid3DInterface::get_faces_neighboring_edge(const long long i,
                                                                   const long long j,
                                                                   const long long k,
                                                                   const long long orient) const {
	std::vector<long long> faces;

	if (orient == 0) {
		add_face_if_inbounds(i, j, k, 2, faces);
		add_face_if_inbounds(i, j, k, 1, faces);
		add_face_if_inbounds(i, j - 1, k, 2, faces);
		add_face_if_inbounds(i, j, k - 1, 1, faces);
	} else if (orient == 1) {
		add_face_if_inbounds(i, j, k, 2, faces);
		add_face_if_inbounds(i, j, k, 0, faces);
		add_face_if_inbounds(i - 1, j, k, 2, faces);
		add_face_if_inbounds(i, j, k - 1, 0, faces);
	} else if (orient == 2) {
		add_face_if_inbounds(i, j, k, 0, faces);
		add_face_if_inbounds(i, j, k, 1, faces);
		add_face_if_inbounds(i, j - 1, k, 0, faces);
		add_face_if_inbounds(i - 1, j, k, 1, faces);
	} else {
		std::cout << "get_faces_neighboring_face(" << i << "," << j << "," << k << "," << orient
		          << ") has impossible orientation" << std::endl;
		exit(1);
	}

	return faces;
}

//	4 faces touch an edge
// input integer edge ID edge_id
// output a list of integer IDs of all faces which touch this edge
std::vector<long long> Grid3DInterface::get_faces_neighboring_edge(const long long edge_id) const {
	long long i, j, k, o;
	get_edge_coords(edge_id, i, j, k, o);
	return get_faces_neighboring_edge(i, j, k, o);
}

//	6 faces touch a cell
// input integer cell coordinates (i,j,k)
// output a list of integer IDs of all faces which touch this cell
std::vector<long long> Grid3DInterface::get_faces_neighboring_cell(const long long i,
                                                                   const long long j,
                                                                   const long long k) const {
	std::vector<long long> faces;
	add_face_if_inbounds(i, j, k, 0, faces);
	add_face_if_inbounds(i, j, k, 1, faces);
	add_face_if_inbounds(i, j, k, 2, faces);
	add_face_if_inbounds(i + 1, j, k, 0, faces);
	add_face_if_inbounds(i, j + 1, k, 1, faces);
	add_face_if_inbounds(i, j, k + 1, 2, faces);
	return faces;
}

//	6 faces touch a cell
// input integer cell ID cell_id
// output a list of integer IDs of all faces which touch this cell
std::vector<long long> Grid3DInterface::get_faces_neighboring_cell(const long long cell_id) const {
	long long i, j, k;
	get_cell_coords(cell_id, i, j, k);
	return get_faces_neighboring_cell(i, j, k);
}

//	6 edges touch a vertex
// input integer vertex coordinates (i,j,k)
// output a list of integer IDs of all edges which touch this vertex
std::vector<long long> Grid3DInterface::get_edges_neighboring_vertex(const long long i,
                                                                     const long long j,
                                                                     const long long k) const {
	std::vector<long long> edges;
	add_edge_if_inbounds(i, j, k, 0, edges);
	add_edge_if_inbounds(i - 1, j, k, 0, edges);
	add_edge_if_inbounds(i, j, k, 1, edges);
	add_edge_if_inbounds(i, j - 1, k, 1, edges);
	add_edge_if_inbounds(i, j, k, 2, edges);
	add_edge_if_inbounds(i, j, k - 1, 2, edges);
	return edges;
}

//	6 edges touch a vertex
// input integer vertex ID vertex_id
// output a list of integer IDs of all edges which touch this vertex
std::vector<long long> Grid3DInterface::get_edges_neighboring_vertex(
    const long long vertex_id) const {
	long long i, j, k;
	get_vertex_coords(vertex_id, i, j, k);
	return get_edges_neighboring_vertex(i, j, k);
}

//	4 edges touch a face
// input integer face coordinates (i,j,k,orient)
// output a list of integer IDs of all edges which touch this face
std::vector<long long> Grid3DInterface::get_edges_neighboring_face(const long long i,
                                                                   const long long j,
                                                                   const long long k,
                                                                   const long long orient) const {
	std::vector<long long> edges;

	if (orient == 0) {
		add_edge_if_inbounds(i, j, k, 1, edges);
		add_edge_if_inbounds(i, j, k, 2, edges);
		add_edge_if_inbounds(i, j, k + 1, 1, edges);
		add_edge_if_inbounds(i, j + 1, k, 2, edges);
	} else if (orient == 1) {
		add_edge_if_inbounds(i, j, k, 0, edges);
		add_edge_if_inbounds(i, j, k, 2, edges);
		add_edge_if_inbounds(i, j, k + 1, 0, edges);
		add_edge_if_inbounds(i + 1, j, k, 2, edges);
	} else if (orient == 2) {
		add_edge_if_inbounds(i, j, k, 0, edges);
		add_edge_if_inbounds(i, j, k, 1, edges);
		add_edge_if_inbounds(i, j + 1, k, 0, edges);
		add_edge_if_inbounds(i + 1, j, k, 1, edges);
	} else {
		std::cout << "get_edges_neighboring_face(" << i << "," << j << "," << k << "," << orient
		          << ") has impossible orientation" << std::endl;
		exit(1);
	}

	return edges;
}

//	4 edges touch a face
// input integer face ID face_id
// output a list of integer IDs of all edges which touch this face
std::vector<long long> Grid3DInterface::get_edges_neighboring_face(const long long face_id) const {
	long long i, j, k, o;
	get_face_coords(face_id, i, j, k, o);
	return get_edges_neighboring_face(i, j, k, o);
}

// 12 edges touch a cell
// input integer cell coordinates (i,j,k)
// output a list of integer IDs of all edges which touch this cell
std::vector<long long> Grid3DInterface::get_edges_neighboring_cell(const long long i,
                                                                   const long long j,
                                                                   const long long k) const {
	std::vector<long long> edges;

	add_edge_if_inbounds(i, j, k, 0, edges);
	add_edge_if_inbounds(i, j + 1, k, 0, edges);
	add_edge_if_inbounds(i, j, k + 1, 0, edges);
	add_edge_if_inbounds(i, j + 1, k + 1, 0, edges);

	add_edge_if_inbounds(i, j, k, 1, edges);
	add_edge_if_inbounds(i + 1, j, k, 1, edges);
	add_edge_if_inbounds(i, j, k + 1, 1, edges);
	add_edge_if_inbounds(i + 1, j, k + 1, 1, edges);

	add_edge_if_inbounds(i, j, k, 2, edges);
	add_edge_if_inbounds(i + 1, j, k, 2, edges);
	add_edge_if_inbounds(i, j + 1, k, 2, edges);
	add_edge_if_inbounds(i + 1, j + 1, k, 2, edges);

	return edges;
}

// 12 edges touch a cell
// input integer cell ID cell_id
// output a list of integer IDs of all edges which touch this cell
std::vector<long long> Grid3DInterface::get_edges_neighboring_cell(const long long cell_id) const {
	long long i, j, k;
	get_cell_coords(cell_id, i, j, k);
	return get_edges_neighboring_cell(i, j, k);
}

// return the orientation of `edge_id` and the ids of the two grid vertices that touch it
void Grid3DInterface::getEdgeVertsAndOrientation(const long long edge_id, long long& edge_v0,
                                                 long long& edge_v1,
                                                 long long& edge_orientation) const {
	long long i, j, k;
	get_edge_coords(edge_id, i, j, k, edge_orientation);

	edge_v0 = get_vertex_id(i, j, k);
	if (edge_orientation == 0) {
		edge_v1 = get_vertex_id(i + 1, j, k);
	} else if (edge_orientation == 1) {
		edge_v1 = get_vertex_id(i, j + 1, k);
	} else if (edge_orientation == 2) {
		edge_v1 = get_vertex_id(i, j, k + 1);
	} else {
		std::cout << "-ERROR: edge " << edge_id << " has impossible orientation " << edge_orientation
		          << std::endl;
		exit(1);
	}
}

//	2 vertices touch an edge
// input integer edge coordinates (i,j,k,orient)
// output a list of integer IDs of all vertices which touch this edge
std::vector<long long> Grid3DInterface::get_verts_neighboring_edge(const long long i,
                                                                   const long long j,
                                                                   const long long k,
                                                                   const long long orient) const {
	std::vector<long long> verts;

	add_vertex_if_inbounds(i, j, k, verts);
	if (orient == 0) {
		add_vertex_if_inbounds(i + 1, j, k, verts);
	} else if (orient == 1) {
		add_vertex_if_inbounds(i, j + 1, k, verts);
	} else if (orient == 2) {
		add_vertex_if_inbounds(i, j, k + 1, verts);
	} else {
		std::cout << "get_verts_neighboring_edge(" << i << "," << j << "," << k << "," << orient
		          << ") has impossible orientation" << std::endl;
		exit(1);
	}

	return verts;
}

//	2 vertices touch an edge
// input integer edge ID edge_id
// output a list of integer IDs of all vertices which touch this edge
std::vector<long long> Grid3DInterface::get_verts_neighboring_edge(const long long edge_id) const {
	long long i, j, k, o;
	get_edge_coords(edge_id, i, j, k, o);
	return get_verts_neighboring_edge(i, j, k, o);
}

//	4 vertices touch a face
// input integer face coordinates (i,j,k,orient)
// output a list of integer IDs of all vertices which touch this face
std::vector<long long> Grid3DInterface::get_verts_neighboring_face(const long long i,
                                                                   const long long j,
                                                                   const long long k,
                                                                   const long long orient) const {
	std::vector<long long> verts;

	if (orient == 0) {
		add_vertex_if_inbounds(i, j, k, verts);
		add_vertex_if_inbounds(i, j + 1, k, verts);
		add_vertex_if_inbounds(i, j, k + 1, verts);
		add_vertex_if_inbounds(i, j + 1, k + 1, verts);
	} else if (orient == 1) {
		add_vertex_if_inbounds(i, j, k, verts);
		add_vertex_if_inbounds(i, j, k + 1, verts);
		add_vertex_if_inbounds(i + 1, j, k, verts);
		add_vertex_if_inbounds(i + 1, j, k + 1, verts);
	} else if (orient == 2) {
		add_vertex_if_inbounds(i, j, k, verts);
		add_vertex_if_inbounds(i + 1, j, k, verts);
		add_vertex_if_inbounds(i, j + 1, k, verts);
		add_vertex_if_inbounds(i + 1, j + 1, k, verts);
	} else {
		std::cout << "get_verts_neighboring_face(" << i << "," << j << "," << k << "," << orient
		          << ") has impossible orientation" << std::endl;
		exit(1);
	}

	return verts;
}

//	4 vertices touch a face
// input integer face ID face_id
// output a list of integer IDs of all vertices which touch this face
std::vector<long long> Grid3DInterface::get_verts_neighboring_face(const long long face_id) const {
	long long i, j, k, o;
	get_face_coords(face_id, i, j, k, o);
	return get_verts_neighboring_face(i, j, k, o);
}

//	8 vertices touch a cell
// input integer cell coordinates (i,j,k)
// output a list of integer IDs of all vertices which touch this cell
std::vector<long long> Grid3DInterface::get_verts_neighboring_cell(const long long i,
                                                                   const long long j,
                                                                   const long long k) const {
	std::vector<long long> verts;
	add_vertex_if_inbounds(i, j, k, verts);
	add_vertex_if_inbounds(i + 1, j, k, verts);
	add_vertex_if_inbounds(i, j + 1, k, verts);
	add_vertex_if_inbounds(i, j, k + 1, verts);
	add_vertex_if_inbounds(i + 1, j + 1, k, verts);
	add_vertex_if_inbounds(i, j + 1, k + 1, verts);
	add_vertex_if_inbounds(i + 1, j, k + 1, verts);
	add_vertex_if_inbounds(i + 1, j + 1, k + 1, verts);
	return verts;
}

//	8 vertices touch a cell
// input integer cell ID cell_id
// output a list of integer IDs of all vertices which touch this cell
std::vector<long long> Grid3DInterface::get_verts_neighboring_cell(const long long cell_id) const {
	long long i, j, k;
	get_cell_coords(cell_id, i, j, k);
	return get_verts_neighboring_cell(i, j, k);
}

std::vector<long long> Grid3DInterface::get_verts_adjacent_to_vert(long long vert_id) const {
	long long i, j, k;
	get_vertex_coords(vert_id, i, j, k);
	std::vector<long long> verts;
	add_vertex_if_inbounds(i + 1, j, k, verts);
	add_vertex_if_inbounds(i - 1, j, k, verts);
	add_vertex_if_inbounds(i, j + 1, k, verts);
	add_vertex_if_inbounds(i, j - 1, k, verts);
	add_vertex_if_inbounds(i, j, k + 1, verts);
	add_vertex_if_inbounds(i, j, k - 1, verts);
	return verts;
}

// get neighboring vertex of a vertex with input `vertex_id` in input `direction`
// 0: x; 1: -x; 2: y; 3: -y; 4: z; 5: -z
//
long long Grid3DInterface::get_vertex_neighboring_vertex(const long long vertex_id,
                                                         const int direction) const {
	long long neib_vertex_id(-1);
	long long i, j, k;
	get_vertex_coords(vertex_id, i, j, k);

	switch (direction) {
		case 0:
			if (!vertex_out_of_bounds(i + 1, j, k))
				neib_vertex_id = get_vertex_id(i + 1, j, k);
			break;
		case 1:
			if (!vertex_out_of_bounds(i - 1, j, k))
				neib_vertex_id = get_vertex_id(i - 1, j, k);
			break;
		case 2:
			if (!vertex_out_of_bounds(i, j + 1, k))
				neib_vertex_id = get_vertex_id(i, j + 1, k);
			break;
		case 3:
			if (!vertex_out_of_bounds(i, j - 1, k))
				neib_vertex_id = get_vertex_id(i, j - 1, k);
			break;
		case 4:
			if (!vertex_out_of_bounds(i, j, k + 1))
				neib_vertex_id = get_vertex_id(i, j, k + 1);
			break;
		case 5:
			if (!vertex_out_of_bounds(i, j, k - 1))
				neib_vertex_id = get_vertex_id(i, j, k - 1);
			break;
	}

	return neib_vertex_id;
}

// get neighboring edge of input vertex in input direction
// 0: x; 1: -x; 2: y; 3: -y; 4: z; 5: -z
long long Grid3DInterface::get_edge_neighboring_vertex(const long long vertex_id,
                                                       const int direction) const {
	long long neighbor_vertex_id = get_vertex_neighboring_vertex(vertex_id, direction);
	if (neighbor_vertex_id == -1) {
		return -1;
	}

	switch (direction) {
		case 0:
			return vertex_id * 3;
		case 1:
			return neighbor_vertex_id * 3;
		case 2:
			return vertex_id * 3 + 1;
		case 3:
			return neighbor_vertex_id * 3 + 1;
		case 4:
			return vertex_id * 3 + 2;
		case 5:
			return neighbor_vertex_id * 3 + 2;
	}

	return -1;
}

//----------------------------------------------------------------
// functions for relating grid coordinates to world coordinates
//----------------------------------------------------------------

Vec3d Grid3DInterface::getVertexPosition(const long long i, const long long j,
                                         const long long k) const {
	return Vec3d(x0 + i * cell_dx, y0 + j * cell_dx, z0 + k * cell_dx);
}

Vec3d Grid3DInterface::getVertexPosition(const Vec3ll coords) const {
	return Vec3d(x0 + coords[0] * cell_dx, y0 + coords[1] * cell_dx, z0 + coords[2] * cell_dx);
}

void Grid3DInterface::getVertexPosition(const long long i, const long long j, const long long k,
                                        double& x, double& y, double& z) const {
	x = x0 + i * cell_dx;
	y = y0 + j * cell_dx;
	z = z0 + k * cell_dx;
}

void Grid3DInterface::getVertexPosition(const long long vertex_id, double& x, double& y,
                                        double& z) const {
	long long i, j, k;
	get_vertex_coords(vertex_id, i, j, k);
	getVertexPosition(i, j, k, x, y, z);
}

Vec3d Grid3DInterface::getVertexPosition(const long long vertex_id) const {
	long long i, j, k;
	get_vertex_coords(vertex_id, i, j, k);
	return getVertexPosition(i, j, k);
}

Vec3d Grid3DInterface::getCellMinPosition(const long long cell_id) const {
	long long i, j, k;
	get_cell_coords(cell_id, i, j, k);
	return Vec3d(i * cell_dx, j * cell_dx, k * cell_dx);
};

Vec3d Grid3DInterface::getCellMaxPosition(const long long cell_id) const {
	long long i, j, k;
	get_cell_coords(cell_id, i, j, k);
	return Vec3d((i + 1) * cell_dx, (j + 1) * cell_dx, (k + 1) * cell_dx);
};

long long Grid3DInterface::getCellForPoint(double x, double y, double z, long long& cell_id) const {
	long long i = static_cast<long long>((x - x0) / cell_dx);
	long long j = static_cast<long long>((y - y0) / cell_dx);
	long long k = static_cast<long long>((z - z0) / cell_dx);
	cell_id = get_cell_id(i, j, k);
	return !cell_out_of_bounds(i, j, k);
}

long long Grid3DInterface::getCellIdForPoint(Vec3d point) const {
	long long i = static_cast<long long>((point[0] - x0) / cell_dx);
	long long j = static_cast<long long>((point[1] - y0) / cell_dx);
	long long k = static_cast<long long>((point[2] - z0) / cell_dx);
	return get_cell_id(i, j, k);
}

Vec3ll Grid3DInterface::getCellCoordsForPoint(Vec3d point) const {
	long long i = static_cast<long long>((point[0] - x0) / cell_dx);
	long long j = static_cast<long long>((point[1] - y0) / cell_dx);
	long long k = static_cast<long long>((point[2] - z0) / cell_dx);
	return Vec3ll(i, j, k);
}

//------------------------------------------------------------
// ...
//------------------------------------------------------------

void Grid3DInterface::unsafeGetVertsNeighbouringEdge(const long long edge_id, long long& vert1_id,
                                                     long long& vert2_id) const {
	long long i, j, k, o;
	get_edge_coords(edge_id, i, j, k, o);
	unsafeGetVertsNeighbouringEdge(i, j, k, o, vert1_id, vert2_id);
}

void Grid3DInterface::unsafeGetVertsNeighbouringEdge(const long long i, const long long j,
                                                     const long long k, const long long orient,
                                                     long long& vert1_id,
                                                     long long& vert2_id) const {
	vert1_id = get_vertex_id(i, j, k);
	if (orient == 0) {
		vert2_id = get_vertex_id(i + 1, j, k);
	} else if (orient == 1) {
		vert2_id = get_vertex_id(i, j + 1, k);
	} else if (orient == 2) {
		vert2_id = get_vertex_id(i, j, k + 1);
	} else {
		std::cout << "unsafeGetVertsNeighbouringEdge(" << i << "," << j << "," << k << "," << orient
		          << ") has impossible orientation" << std::endl;
		exit(1);
	}
}

bool Grid3DInterface::are_edges_axis_coplanar(const std::vector<long long>& edge_ids) const {
	if (edge_ids.empty()) {
		return true;
	}
	std::vector<std::vector<long long>> verts_coords;
	verts_coords.reserve(edge_ids.size() * 2);
	for (long long edge_id : edge_ids) {
		for (long long vert_id : get_verts_neighboring_edge(edge_id)) {
			long long i, j, k;
			get_vertex_coords(vert_id, i, j, k);
			verts_coords.push_back({i, j, k});
		}
	}

	for (int o = 0; o < 3; ++o) {
		long long coord = verts_coords[0][o];
		bool all_match = true;
		for (const std::vector<long long>& coords : verts_coords) {
			if (coords[o] != coord) {
				all_match = false;
				break;
			}
		}
		if (all_match) {
			return true;
		}
	}
	return false;
}

////////////////////////////////////////
// Private helper functions
//

// helper functions for compiling lists of grid element IDs
// ... these functions take coordinates of a grid primitive, and adds its ID to the input list if it
// is not outside of the grid
void Grid3DInterface::add_vertex_if_inbounds(const long long i, const long long j,
                                             const long long k, std::vector<long long>& IDs) const {
	if (!vertex_out_of_bounds(i, j, k)) {
		IDs.push_back(get_vertex_id(i, j, k));
	}
}
void Grid3DInterface::add_edge_if_inbounds(const long long i, const long long j, const long long k,
                                           const long long orient,
                                           std::vector<long long>& IDs) const {
	if (!edge_out_of_bounds(i, j, k, orient)) {
		IDs.push_back(get_edge_id(i, j, k, orient));
	}
}
void Grid3DInterface::add_face_if_inbounds(const long long i, const long long j, const long long k,
                                           const long long orient,
                                           std::vector<long long>& IDs) const {
	if (!face_out_of_bounds(i, j, k, orient)) {
		IDs.push_back(get_face_id(i, j, k, orient));
	}
}
void Grid3DInterface::add_cell_if_inbounds(const long long i, const long long j, const long long k,
                                           std::vector<long long>& IDs) const {
	if (!cell_out_of_bounds(i, j, k)) {
		IDs.push_back(get_cell_id(i, j, k));
	}
}

// return width of a cubic grid cell
double Grid3DInterface::get_cell_dx() const { return cell_dx; }

// return dimensons of the grid
long long Grid3DInterface::get_dim_nx() const { return nx; }
long long Grid3DInterface::get_dim_ny() const { return ny; }
long long Grid3DInterface::get_dim_nz() const { return nz; }

// return number of cells
long long Grid3DInterface::get_num_cells() const { return num_cells; }

// functions required by grid-label
//
//  get verts on a selcected boundary
//  0: x_min; 1: x_max; 2: y_min; 3: y_max; 4: z_min; 5: z_max
//
std::vector<long long> Grid3DInterface::get_verts_on_boundary(const int boundary_id) const {
	std::vector<long long> boundary_verts_id;

	long long i, j, k;
	switch (boundary_id) {
		case 0:
			for (j = 0; j <= ny; ++j)
				for (k = 0; k <= nz; ++k) {
					boundary_verts_id.push_back(get_vertex_id(0, j, k));
				}
			break;
		case 1:
			for (j = 0; j <= ny; ++j)
				for (k = 0; k <= nz; ++k) {
					boundary_verts_id.push_back(get_vertex_id(nx, j, k));
				}
			break;
		case 2:
			for (i = 0; i <= nx; ++i)
				for (k = 0; k <= nz; ++k) {
					boundary_verts_id.push_back(get_vertex_id(i, 0, k));
				}
			break;
		case 3:
			for (i = 0; i <= nx; ++i)
				for (k = 0; k <= nz; ++k) {
					boundary_verts_id.push_back(get_vertex_id(i, ny, k));
				}
			break;
		case 4:
			for (i = 0; i <= nx; ++i)
				for (j = 0; j <= ny; ++j) {
					boundary_verts_id.push_back(get_vertex_id(i, j, 0));
				}
			break;
		case 5:
			for (i = 0; i <= nx; ++i)
				for (j = 0; j <= ny; ++j) {
					boundary_verts_id.push_back(get_vertex_id(i, j, nz));
				}
			break;
	}

	return boundary_verts_id;
}

std::vector<Vec3ll> Grid3DInterface::get_face_triangles(const long long face_id) const {
	std::vector<long long> face_vertex_ids = get_verts_neighboring_face(face_id);
	return {Vec3ll(face_vertex_ids[0], face_vertex_ids[1], face_vertex_ids[2]),
	        Vec3ll(face_vertex_ids[2], face_vertex_ids[1], face_vertex_ids[3])};
}

// get the minimum coordinates of the grid
Vec3d Grid3DInterface::getOriginCoords() const { return Vec3d(x0, y0, z0); }

Vec3d Grid3DInterface::getCellCenter(long long cell_id) const {
	long long i, j, k;
	get_cell_coords(cell_id, i, j, k);
	return Vec3d(x0 + i * cell_dx, y0 + j * cell_dx, z0 + k * cell_dx) + Vec3d(cell_dx * 0.5);
}

Vec3d Grid3DInterface::getFaceCenter(long long face_id) const {
	long long i, j, k, o;
	double x, y, z;
	get_face_coords(face_id, i, j, k, o);
	getVertexPosition(i, j, k, x, y, z);
	assert(0 <= o && o <= 2);
	if (o == 0) {
		return Vec3d(x, y + 0.5 * cell_dx, z + 0.5 * cell_dx);
	} else if (o == 1) {
		return Vec3d(x + 0.5 * cell_dx, y, z + 0.5 * cell_dx);
	} else if (o == 2) {
		return Vec3d(x + 0.5 * cell_dx, y + 0.5 * cell_dx, z);
	}
	// Dummy value that should never be reached.
	return Vec3d(0.0);
}

Vec3d Grid3DInterface::getEdgeCenter(long long edge_id) const {
	long long i, j, k, o;
	double x, y, z;
	get_edge_coords(edge_id, i, j, k, o);
	getVertexPosition(i, j, k, x, y, z);
	assert(0 <= o && o <= 2);
	if (o == 0) {
		return Vec3d(x + 0.5 * cell_dx, y, z);
	} else if (o == 1) {
		return Vec3d(x, y + 0.5 * cell_dx, z);
	} else if (o == 2) {
		return Vec3d(x, y, z + 0.5 * cell_dx);
	}
	// Dummy value that should never be reached.
	return Vec3d(0.0);
}

// return ids of the two grid faces of the input grid cell that are adjacent to input relative grid
// edge; `relative_edge_id` is a number between 0 an 11 that identifies a grid edge of `cell_id` as
// returned by `get_edges_neighboring_cell(cell_id)`; the faces are returned in a specific order,
// see function declaration for more details
std::vector<long long> Grid3DInterface::getFacesNeighboringEdgeInCell(int relative_edge_id,
                                                                      long long cell_id) const {
	assert(relative_edge_id >= 0 && relative_edge_id <= 11);
	long long i, j, k;
	get_cell_coords(cell_id, i, j, k);
	std::vector<long long> neighbor_faces;

	// `relative_edge_id` identifies an edge inside a cell based on the following configuration:
	// (i, j, k, 0), (i, j+1, k, 0), (i, j, k+1, 0), (i, j+1, k+1, 0),
	// (i, j, k, 1), (i+1, j, k, 1), (i, j, k+1, 1), (i+1, j, k+1, 1),
	// (i, j, k, 2), (i+1, j, k, 2), (i, j+1, k, 2), (i+1, j+1, k, 2),

	switch (relative_edge_id) {
		case 0:  // edge (i, j, k)-(i+1, j, k), orientation 0
			add_face_if_inbounds(i, j, k, 2, neighbor_faces);  // in z-plane
			add_face_if_inbounds(i, j, k, 1, neighbor_faces);  // in y-plane
			break;

		case 1:  // edge (i, j+1, k)-(i+1, j+1, k), orientation 0
			add_face_if_inbounds(i, j + 1, k, 1, neighbor_faces);  // in y-plane
			add_face_if_inbounds(i, j, k, 2, neighbor_faces);      // in z-plane
			break;

		case 2:  // edge (i, j, k+1)-(i+1, j, k+1), orientation 0
			add_face_if_inbounds(i, j, k, 1, neighbor_faces);      // in y-plane
			add_face_if_inbounds(i, j, k + 1, 2, neighbor_faces);  // in z-plane
			break;

		case 3:  // edge (i, j+1, k+1)-(i+1, j+1, k+1), orientation 0
			add_face_if_inbounds(i, j, k + 1, 2, neighbor_faces);  // in z-plane
			add_face_if_inbounds(i, j + 1, k, 1, neighbor_faces);  // in y-plane
			break;

		case 4:  // edge (i, j, k)-(i, j+1, k), orientation 1
			add_face_if_inbounds(i, j, k, 0, neighbor_faces);  // in x-plane
			add_face_if_inbounds(i, j, k, 2, neighbor_faces);  // in z-plane
			break;

		case 5:  // edge (i+1, j, k)-(i+1, j+1, k), orientation 1
			add_face_if_inbounds(i, j, k, 2, neighbor_faces);      // in z-plane
			add_face_if_inbounds(i + 1, j, k, 0, neighbor_faces);  // in x-plane
			break;

		case 6:  // edge (i, j, k+1)-(i, j+1, k+1), orientation 1
			add_face_if_inbounds(i, j, k + 1, 2, neighbor_faces);  // in z-plane
			add_face_if_inbounds(i, j, k, 0, neighbor_faces);      // in x-plane
			break;

		case 7:  // edge (i+1, j, k+1)-(i+1, j+1, k+1), orientation 1
			add_face_if_inbounds(i + 1, j, k, 0, neighbor_faces);  // in x-plane
			add_face_if_inbounds(i, j, k + 1, 2, neighbor_faces);  // in z-plane
			break;

		case 8:  // edge (i, j, k)-(i, j, k+1), orientation 2
			add_face_if_inbounds(i, j, k, 1, neighbor_faces);  // in y-plane
			add_face_if_inbounds(i, j, k, 0, neighbor_faces);  // in x-plane
			break;

		case 9:  // edge (i+1, j, k)-(i+1, j, k+1), orientation 2
			add_face_if_inbounds(i + 1, j, k, 0, neighbor_faces);  // in x-plane
			add_face_if_inbounds(i, j, k, 1, neighbor_faces);      // in y-plane
			break;

		case 10:  // edge (i, j+1, k)-(i, j+1, k+1), orientation 2
			add_face_if_inbounds(i, j, k, 0, neighbor_faces);      // in x-plane
			add_face_if_inbounds(i, j + 1, k, 1, neighbor_faces);  // in y-plane
			break;

		case 11:  // edge (i+1, j+1, k)-(i+1, j+1, k+1), orientation 2
			add_face_if_inbounds(i, j + 1, k, 1, neighbor_faces);  // in y-plane
			add_face_if_inbounds(i + 1, j, k, 0, neighbor_faces);  // in x-plane
			break;
	}

	return neighbor_faces;
}

// return ids of the three grid faces of the input grid cell that are adjacent to input relative
// grid vertex; `relative_vertex_id` is a number between 0 an 7 that identifies a grid vertex of
// `cell_id`, as returned by `get_verts_neighboring_cell(cell_id)`; the faces are returned in a
// specific order, see function declaration for more details
std::vector<long long> Grid3DInterface::getFacesNeighboringVertexInCell(int relative_vertex_id,
                                                                        long long cell_id) const {
	assert(relative_vertex_id >= 0 && relative_vertex_id <= 7);
	long long i, j, k;
	get_cell_coords(cell_id, i, j, k);
	std::vector<long long> neighbor_faces;

	switch (relative_vertex_id) {
		case 0:                                              // vertex (i,j,k)
			add_face_if_inbounds(i, j, k, 0, neighbor_faces);  // in x-plane
			add_face_if_inbounds(i, j, k, 1, neighbor_faces);  // in y-plane
			add_face_if_inbounds(i, j, k, 2, neighbor_faces);  // in z-plane
			break;
		case 1:                                                  // vertex (i+1,j,k)
			add_face_if_inbounds(i + 1, j, k, 0, neighbor_faces);  // in x-plane
			add_face_if_inbounds(i, j, k, 1, neighbor_faces);      // in y-plane
			add_face_if_inbounds(i, j, k, 2, neighbor_faces);      // in z-plane
			break;
		case 2:                                                  // vertex (i,j+1,k)
			add_face_if_inbounds(i, j, k, 0, neighbor_faces);      // in x-plane
			add_face_if_inbounds(i, j + 1, k, 1, neighbor_faces);  // in y-plane
			add_face_if_inbounds(i, j, k, 2, neighbor_faces);      // in z-plane
			break;
		case 3:                                                  // vertex (i,j,k+1)
			add_face_if_inbounds(i, j, k, 0, neighbor_faces);      // in x-plane
			add_face_if_inbounds(i, j, k, 1, neighbor_faces);      // in y-plane
			add_face_if_inbounds(i, j, k + 1, 2, neighbor_faces);  // in z-plane
			break;
		case 4:                                                  // vertex (i+1,j+1,k)
			add_face_if_inbounds(i + 1, j, k, 0, neighbor_faces);  // in x-plane
			add_face_if_inbounds(i, j + 1, k, 1, neighbor_faces);  // in y-plane
			add_face_if_inbounds(i, j, k, 2, neighbor_faces);      // in z-plane
			break;
		case 5:                                                  // vertex (i,j+1,k+1)
			add_face_if_inbounds(i, j, k, 0, neighbor_faces);      // in x-plane
			add_face_if_inbounds(i, j + 1, k, 1, neighbor_faces);  // in y-plane
			add_face_if_inbounds(i, j, k + 1, 2, neighbor_faces);  // in z-plane
			break;
		case 6:                                                  // vertex (i+1,j,k+1)
			add_face_if_inbounds(i + 1, j, k, 0, neighbor_faces);  // in x-plane
			add_face_if_inbounds(i, j, k, 1, neighbor_faces);      // in y-plane
			add_face_if_inbounds(i, j, k + 1, 2, neighbor_faces);  // in z-plane
			break;
		case 7:                                                  // vertex(i+1,j+1,k+1)
			add_face_if_inbounds(i + 1, j, k, 0, neighbor_faces);  // in x-plane
			add_face_if_inbounds(i, j + 1, k, 1, neighbor_faces);  // in y-plane
			add_face_if_inbounds(i, j, k + 1, 2, neighbor_faces);  // in z-plane
			break;
	}

	return neighbor_faces;
}

// return ids of the three grid vertices of the input grid cell that are adjacent to input relative
// grid vertex; `relative_vertex_id` is a number between 0 an 7 that identifies a grid vertex of
// `cell_id`, as returned by `get_verts_neighboring_cell(cell_id)`; the vertices are returned in a
// specific order, see function declaration for more details
std::vector<long long> Grid3DInterface::getVertsNeighboringVertexInCell(int relative_vertex_id,
                                                                        long long cell_id) const {
	assert(relative_vertex_id >= 0 && relative_vertex_id <= 7);
	long long i, j, k;
	get_cell_coords(cell_id, i, j, k);
	std::vector<long long> neighbor_vertices;

	switch (relative_vertex_id) {
		case 0:                                                    // vertex (i,j,k)
			add_vertex_if_inbounds(i + 1, j, k, neighbor_vertices);  // along x-axis
			add_vertex_if_inbounds(i, j + 1, k, neighbor_vertices);  // along y-axis
			add_vertex_if_inbounds(i, j, k + 1, neighbor_vertices);  // along z-axis
			break;
		case 1:                                                        // vertex (i+1,j,k)
			add_vertex_if_inbounds(i, j, k, neighbor_vertices);          // along x-axis
			add_vertex_if_inbounds(i + 1, j + 1, k, neighbor_vertices);  // along y-axis
			add_vertex_if_inbounds(i + 1, j, k + 1, neighbor_vertices);  // along z-axis
			break;
		case 2:                                                        // vertex (i,j+1,k)
			add_vertex_if_inbounds(i + 1, j + 1, k, neighbor_vertices);  // along x-axis
			add_vertex_if_inbounds(i, j, k, neighbor_vertices);          // along y-axis
			add_vertex_if_inbounds(i, j + 1, k + 1, neighbor_vertices);  // along z-axis
			break;
		case 3:                                                        // vertex (i,j,k+1)
			add_vertex_if_inbounds(i + 1, j, k + 1, neighbor_vertices);  // along x-axis
			add_vertex_if_inbounds(i, j + 1, k + 1, neighbor_vertices);  // along y-axis
			add_vertex_if_inbounds(i, j, k, neighbor_vertices);          // along z-axis
			break;
		case 4:                                                            // vertex (i+1,j+1,k)
			add_vertex_if_inbounds(i, j + 1, k, neighbor_vertices);          // along x-axis
			add_vertex_if_inbounds(i + 1, j, k, neighbor_vertices);          // along y-axis
			add_vertex_if_inbounds(i + 1, j + 1, k + 1, neighbor_vertices);  // along z-axis
			break;
		case 5:                                                            // vertex (i,j+1,k+1)
			add_vertex_if_inbounds(i + 1, j + 1, k + 1, neighbor_vertices);  // along x-axis
			add_vertex_if_inbounds(i, j, k + 1, neighbor_vertices);          // along y-axis
			add_vertex_if_inbounds(i, j + 1, k, neighbor_vertices);          // along z-axis
			break;
		case 6:                                                            // vertex (i+1,j,k+1)
			add_vertex_if_inbounds(i, j, k + 1, neighbor_vertices);          // along x-axis
			add_vertex_if_inbounds(i + 1, j + 1, k + 1, neighbor_vertices);  // along y-axis
			add_vertex_if_inbounds(i + 1, j, k, neighbor_vertices);          // along z-axis
			break;
		case 7:                                                        // vertex(i+1,j+1,k+1)
			add_vertex_if_inbounds(i, j + 1, k + 1, neighbor_vertices);  // along x-axis
			add_vertex_if_inbounds(i + 1, j, k + 1, neighbor_vertices);  // along y-axis
			add_vertex_if_inbounds(i + 1, j + 1, k, neighbor_vertices);  // along z-axis
			break;
	}

	return neighbor_vertices;
}

long long Grid3DInterface::getEdgeOrientation(long long edge_id) const { return edge_id % 3; }

long long Grid3DInterface::getFaceOrientation(long long face_id) const {
	return getEdgeOrientation(face_id);
}

bool Grid3DInterface::isPointInsideGrid(Vec3d point) const {
	return (point[0] >= x0 && point[1] >= y0 && point[2] >= z0 && point[0] <= x0 + (nx * cell_dx) &&
	        point[1] <= y0 + (ny * cell_dx) && point[2] <= z0 + (nz * cell_dx));
}