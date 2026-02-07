/* Grid3DInterface.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the header for the grid interface. It lists the virtual functions which are accessed by
 * modules and implemented in a child grid class.
 *
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <iostream>
#include <string>
#include <vector>

#include "../../abseil-cpp/absl/container/flat_hash_set.h"
#include "../utilities/SparseVector.h"
#include "GridLattice.h"
#include "GridMeshIntersection.h"
#include "Mesh3DInterface.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this interface defines functions that modules use to access the 3D grid data structure
class Grid3DInterface {
 protected:
	using SparseRaysContainer = GridLattice<long long, long long>;

 public:
	// constructors
	Grid3DInterface();
	Grid3DInterface(const long long grid_x, const long long grid_y, const long long grid_z,
	                const double origin_x, const double origin_y, const double origin_z,
	                const double dx);
	virtual ~Grid3DInterface() = default;

	// enums

	// Types of complex cells
	enum class ComplexCellType {
		kFixed,
		kFlexible,
		kBoth,
		kNumOfTypes,
	};

	using FaceGraph = absl::flat_hash_map<std::pair<Mesh3DVertex*, Mesh3DVertex*>, Mesh3DTriangle*>;

	////////////////
	// public functions

	// initialization
	void init(const long long grid_x, const long long grid_y, const long long grid_z,
	          const double origin_x, const double origin_y, const double origin_z, const double dx);

	// returns true if the coordinates of the grid element are outside of the grid, false otherwise
	inline bool vertex_out_of_bounds(const long long i, const long long j, const long long k) const;
	inline bool edge_out_of_bounds(const long long i, const long long j, const long long k,
	                               const long long orient) const;
	inline bool face_out_of_bounds(const long long i, const long long j, const long long k,
	                               const long long orient) const;
	inline bool cell_out_of_bounds(const long long i, const long long j, const long long k) const;

	// functions which take in (i,j,k) coordinates of a grid [vertex,edge,face,cell] and output a
	// unique integer ID
	inline long long get_vertex_id(const long long i, const long long j, const long long k) const;
	inline long long get_edge_id(const long long x, const long long y, const long long z,
	                             const long long orient) const;
	inline long long get_face_id(const long long x, const long long y, const long long z,
	                             const long long orient) const;
	inline long long get_cell_id(const long long x, const long long y, const long long z) const;

	// functions which take in a unique integer ID of a grid [vertex,edge,face,cell] and output
	// (i,j,k,orient) coordinates
	void get_vertex_coords(const long long vert_id, long long& i, long long& j, long long& k) const;
	void get_edge_coords(const long long edge_id, long long& i, long long& j, long long& k,
	                     long long& orient) const;
	void get_face_coords(const long long face_id, long long& i, long long& j, long long& k,
	                     long long& orient) const;
	void get_cell_coords(const long long cell_id, long long& i, long long& j, long long& k) const;

	/////////////////////////////
	// functions which return a list of neighboring cells/faces/edges/vertices
	std::vector<long long> get_cells_neighboring_vertex(const long long vertex_id) const;
	std::vector<long long> get_cells_neighboring_vertex(const long long vert_i,
	                                                    const long long vert_j,
	                                                    const long long vert_k) const;
	std::vector<long long> get_cells_neighboring_edge(const long long edge_id) const;
	std::vector<long long> get_cells_neighboring_edge(const long long edge_i, const long long edge_j,
	                                                  const long long edge_k,
	                                                  const long long edge_orient) const;
	std::vector<long long> get_cells_neighboring_face(const long long face_id) const;
	std::vector<long long> get_cells_neighboring_face(const long long face_i, const long long face_j,
	                                                  const long long face_k,
	                                                  const long long face_orient) const;

	std::vector<long long> get_faces_neighboring_vertex(const long long vertex_id) const;
	std::vector<long long> get_faces_neighboring_vertex(const long long vert_i,
	                                                    const long long vert_j,
	                                                    const long long vert_k) const;
	std::vector<long long> get_faces_neighboring_edge(const long long edge_id) const;
	std::vector<long long> get_faces_neighboring_edge(const long long edge_i, const long long edge_j,
	                                                  const long long edge_k,
	                                                  const long long edge_orient) const;
	std::vector<long long> get_faces_neighboring_cell(const long long cell_id) const;
	std::vector<long long> get_faces_neighboring_cell(const long long cell_i, const long long cell_j,
	                                                  const long long cell_k) const;
	std::vector<long long> get_cells_neighboring_cell(const long long cell_id) const;
	std::vector<long long> get_cells_neighboring_cell(const long long cell_i, const long long cell_j,
	                                                  const long long cell_k) const;

	std::vector<long long> get_edges_neighboring_vertex(const long long vertex_id) const;
	std::vector<long long> get_edges_neighboring_vertex(const long long vert_i,
	                                                    const long long vert_j,
	                                                    const long long vert_k) const;
	std::vector<long long> get_edges_neighboring_face(const long long face_id) const;
	std::vector<long long> get_edges_neighboring_face(const long long face_i, const long long face_j,
	                                                  const long long face_k,
	                                                  const long long face_orient) const;

	// return ids of edges neighboring input cell in the following order:
	// (i, j, k, 0), (i, j+1, k, 0), (i, j, k+1, 0), (i, j+1, k+1, 0),
	// (i, j, k, 1), (i+1, j, k, 1), (i, j, k+1, 1), (i+1, j, k+1, 1),
	// (i, j, k, 2), (i+1, j, k, 2), (i, j+1, k, 2), (i+1, j+1, k, 2),
	std::vector<long long> get_edges_neighboring_cell(const long long cell_id) const;
	std::vector<long long> get_edges_neighboring_cell(const long long cell_i, const long long cell_j,
	                                                  const long long cell_k) const;

	std::vector<long long> get_verts_neighboring_edge(const long long edge_id) const;
	std::vector<long long> get_verts_neighboring_edge(const long long edge_i, const long long edge_j,
	                                                  const long long edge_k,
	                                                  const long long edge_orient) const;
	std::vector<long long> get_verts_neighboring_face(const long long face_id) const;
	std::vector<long long> get_verts_neighboring_face(const long long face_i, const long long face_j,
	                                                  const long long face_k,
	                                                  const long long face_orient) const;
	std::vector<long long> get_verts_neighboring_cell(const long long cell_id) const;
	std::vector<long long> get_verts_neighboring_cell(const long long cell_i, const long long cell_j,
	                                                  const long long cell_k) const;
	void unsafeGetVertsNeighbouringEdge(const long long edge_id, long long& vert1_id,
	                                    long long& vert2_id) const;
	void unsafeGetVertsNeighbouringEdge(const long long edge_i, const long long edge_j,
	                                    const long long edge_k, const long long edge_orient,
	                                    long long& vert1_id, long long& vert2_id) const;
	std::vector<long long> get_verts_adjacent_to_vert(const long long vert_id) const;

	// --------------- get grid element neighbors constrained to a given cell

	// Returns a vector containing the ids of the two grid faces of the input cell that are adjacent
	// to the input relative edge. `relative_edge_id` has to be a number in the interval [0,11], it is
	// interpreted as the index in the vector returned by `get_edges_neighboring_cell(cell_id)`, which
	// contains ids of grid edges of the grid cell with `cell_id`. The faces are returned in a
	// specific order, based on their relative position to the grid edge. Specifically, let
	// `cell_vert` be a point in the middle of the input cell, `edge_vert` be a point in the middle of
	// the input edge, and `face_vert` be a point in the middle of an adjacent grid face. Face 0 is
	// chosen so that orientation `cell_vert`->`face_vert`->`edge_vert` + right hand rule points
	// towards vertex 0 of the input edge, and orientation `cell_vert`->`edge_vert`->`face_vert`
	// + right hand rule points towards vertex 1 of the input edge.
	std::vector<long long> getFacesNeighboringEdgeInCell(int relative_edge_id,
	                                                     long long cell_id) const;

	// Returns a vector containing the ids of the three grid vertices of the input cell that are
	// adjacent to the input relative vertex. `relative_vertex_id` has to be a number in the interval
	// [0,7], interpreted as an index in the vector returned by `get_verts_neighboring_cell(cell_id)`,
	// which contains ids of grid vertices of the grid cell with `cell_id`. The vertices adjacent to
	// the vertex with `relative_vertex_id` are returned in a specific order, first the vertex that
	// lies on the same x-axis parallel line, then the vertex that lies on the same y-axis parallel
	// line, and lastly the vertex that lies on the same z-axis parallel line.
	std::vector<long long> getVertsNeighboringVertexInCell(int relative_vertex_id,
	                                                       long long cell_id) const;

	// Returns a vector containing the ids of the three grid faces of the input cell that are adjacent
	// to the input relative vertex. `relative_vertex_id` has to be a number in the interval [0,7], it
	// is interpreted as the index in the vector returned by `get_verts_neighboring_cell(cell_id)`,
	// which contains ids of grid vertices of the grid cell with `cell_id`. The faces adjacent to the
	// vertex with `relative_vertex_id` are returned in a specific order, first the face orthogonal to
	// the x-axis, then the face orthogonal to the y-axis, and lastly the face orthogonal to the
	// z-axis.
	std::vector<long long> getFacesNeighboringVertexInCell(int relative_vertex_id,
	                                                       long long cell_id) const;

	// --------------- get grid element orientations

	// returns the orientation of input `edge_id` (i.e. its id modulo 3)
	long long getEdgeOrientation(long long edge_id) const;
	// returns the orientation of input `face_id` (i.e. its id modulo 3); functionally equivalent to
	// `getEdgeOrientation`
	long long getFaceOrientation(long long face_id) const;

	// Returns the orientation of `edge_id` and the ids of the two grid vertices that touch it. Only
	// safe to use on an edge that lies inside the grid, so that its endpoints also lie inside the
	// grid.
	void getEdgeVertsAndOrientation(const long long edge_id, long long& edge_v0, long long& edge_v1,
	                                long long& edge_orientation) const;

	// get the minimum coordinates of the grid
	Vec3d getOriginCoords() const;

	// functions to look around the vertex in the given direction
	long long get_vertex_neighboring_vertex(const long long vertex_id, const int direction) const;
	long long get_edge_neighboring_vertex(const long long vertex_id, const int direction) const;

	std::vector<long long> get_verts_on_boundary(
	    const int boundary_id) const;  // 0 x_min; 1 x_max; 2 y_min; 3 y_max; 4 z_min; 5 z_max

	// Returns 2 vectors of vertex ids, representing triangles for a given face. The normals of
	// triangles always point into positive directions.
	std::vector<Vec3ll> get_face_triangles(const long long face_id) const;

	// Returns `true` is input `point` lies within the grid, `false` otherwise.
	bool isPointInsideGrid(Vec3d point) const;

	// --------------- grid coordinates <-> world coordinates

	Vec3d getVertexPosition(const long long i, const long long j, const long long k) const;
	Vec3d getVertexPosition(const Vec3ll coords) const;

	void getVertexPosition(const long long i, const long long j, const long long k, double& x,
	                       double& y, double& z) const;
	Vec3d getVertexPosition(const long long vertex_id) const;
	void getVertexPosition(const long long vertex_id, double& x, double& y, double& z) const;

	Vec3d getCellMinPosition(const long long cell_id) const;
	Vec3d getCellMaxPosition(const long long cell_id) const;

	// Returns 1, if the point is inside grid, 0 otherwise. In case the point is inside, the cell_id
	// containing is provided.
	long long getCellForPoint(double x, double y, double z, long long& cell_id) const;
	Vec3ll getCellCoordsForPoint(Vec3d point) const;
	long long getCellIdForPoint(Vec3d point) const;

	// Checks if all grid edges in the input vector `edge_ids` lie in the same axial plane, by
	// checking if they all have at least one grid coordinate equal. If the input vector is empty,
	// returns true.
	bool are_edges_axis_coplanar(const std::vector<long long>& edge_ids) const;

	// Returns world coordinates of the point in the center of input `cell_id`.
	Vec3d getCellCenter(long long cell_id) const;
	// Returns world coordinates of the point in the center of input `face_id`.
	Vec3d getFaceCenter(long long face_id) const;
	// Returns world coordinates of the point in the center of input `edge_id`.
	Vec3d getEdgeCenter(long long edge_id) const;

	/////////////////
	// virtual functions

	// Vertex material functions. A precise definition depends on the implementation.
	virtual void setVertexMaterial(const long long vertex_id, SparseVector<int> material) = 0;
	virtual SparseVector<int> getVertexMaterial(const long long vertex_id) = 0;
	virtual void setVertexMaterialVectors(
	    absl::flat_hash_map<long long, SparseVector<int>> per_vertex_materials) = 0;

	virtual Vec3d getRayDirection(long long orientation) = 0;

	//-----------------------------------------------------------------------
	// Functions to handle conversion between mesh labels (arbitrary integers, acquired on algorithm
	// input) and grid labels (conseqcutive integers that start with 0 - the global outside).

	// Converts a pair of mesh labels to a pair of grid labels. Constructs a material encoder as
	// needed on the fly.
	virtual Vec2i convertMeshLabelsToGridLabels(Vec2i mesh_labels) = 0;
	// Constructs a material decoder to transform grid labels into mesh labels.
	virtual void constructMaterialDecoder() = 0;
	// Converts a grid label to a mesh label.
	virtual int convertGridLabelToMeshLabel(int grid_label) = 0;
	virtual Vec2i convertGridLabelToMeshLabel(Vec2i grid_labels) = 0;

	// Functions to reference cells with triangles.
	virtual void addTriangleToCell(const long long cell_id, Mesh3DTriangle* triangle_id) = 0;
	virtual void addTriangleToCellWithoutFlaggingRays(const long long cell_id,
	                                                  Mesh3DTriangle* triangle_id) = 0;
	virtual void remove_triangle_from_cell(const long long cell_id, Mesh3DTriangle* triangle_id) = 0;
	virtual std::vector<Mesh3DTriangle*> getCellTriangles(const long long cell_id) const = 0;
	virtual absl::flat_hash_set<Mesh3DTriangle*> get_cell_triangles_set(const long long cell_id) = 0;
	virtual std::vector<long long> getCellsWithTriangles() = 0;

	// Functions to keep track of grid edge intersections with triangles.
	virtual void addIntersectionToEdge(GridEdgeMeshFaceIntersection intersection) = 0;
	virtual std::vector<GridEdgeMeshFaceIntersection> get_intersections_on_edge(
	    const long long edge_id) = 0;

	// Interface to get grid rays in a sparse manner.
	// Only implemented in the sparse subclasses.
	virtual const SparseRaysContainer& getSparseRays(long long orientation) = 0;

	// Functions to keep track of complex elements of the grid.
	//---------------- manipulating complex vertices
	virtual bool isVertexMarkedComplex(const long long vertex_id) = 0;
	virtual void markVertexAsComplex(const long long vertex_id) = 0;

	//---------------- manipulating complex edges
	virtual bool isEdgeMarkedTopoComplex(const long long edge_id) = 0;
	virtual void markEdgeAsTopoComplex(const long long edge_id) = 0;
	virtual bool isEdgeMarkedGeomComplex(const long long edge_id) = 0;
	virtual void markEdgeAsGeomComplex(const long long edge_id) = 0;
	virtual bool doesEdgeHaveFixedComplexNeighbors(const long long edge_id) = 0;
	virtual bool isFrontEdge(const long long edge_id) = 0;
	virtual absl::flat_hash_set<long long> getTopoComplexGeomSimpleEdges() = 0;
	virtual absl::flat_hash_set<long long> getGeomComplexEdges() = 0;

	//---------------- manipulating complex faces
	virtual bool isFaceMarkedTopoSimple(const long long face_id) = 0;
	virtual void markFaceAsTopoSimple(const long long face_id) = 0;
	virtual void unmarkFaceAsTopoSimple(const long long face_id) = 0;
	virtual bool isFaceMarkedTopoComplex(const long long face_id) = 0;
	virtual void markFaceAsTopoComplex(const long long face_id) = 0;
	virtual bool isFaceMarkedTopoSuspicious(const long long face_id) = 0;
	virtual void markFaceAsTopoSuspicious(const long long face_id) = 0;
	virtual bool isFaceMarkedGeomComplex(const long long face_id) = 0;
	virtual void markFaceAsGeomComplex(const long long face_id) = 0;

	//---------------- manipulating complex cells
	virtual bool isCellMarkedComplex(const long long cell_id, const ComplexCellType type) const = 0;
	virtual void markCellAsComplex(const long long cell_id, const ComplexCellType type) = 0;
	virtual void unmarkCellAsComplex(const long long cell_id, const ComplexCellType type) = 0;
	virtual void markCellAsEdgeDeep(const long long cell_id) = 0;
	virtual void markCellAsEdgeShallow(const long long cell_id) = 0;
	virtual absl::flat_hash_set<long long> getEdgeDeepCells() const = 0;
	virtual absl::flat_hash_set<long long> getEdgeShallowCells() const = 0;
	virtual std::vector<long long> getComplexCellsVector(const ComplexCellType type) const = 0;
	virtual absl::flat_hash_set<long long> getComplexCellsSet(const ComplexCellType type) const = 0;
	// Returns ids of faces that separate complex cells from non-complex cells.
	virtual std::vector<long long> getFrontFacesVector() const = 0;
	virtual absl::flat_hash_set<long long> getFrontFacesSet() const = 0;
	virtual std::vector<long long> getComplexRegionFrontCellsVector() const = 0;
	virtual absl::flat_hash_set<long long> getComplexRegionFrontCellsSet() const = 0;
	virtual std::vector<long long> getSimpleRegionFrontCellsVector() const = 0;
	virtual absl::flat_hash_set<long long> getSimpleRegionFrontCellsSet() const = 0;
	virtual absl::flat_hash_set<long long> getTopoComplexFaces() const = 0;
	virtual bool isFaceInComplexFront(long long face_id) const = 0;

	// Functions to manipulate the mesh intersection data on edges and faces.
	virtual void add_mesh_vertex_to_edge(const long long edge_id, Mesh3DVertex* v1) = 0;
	virtual std::vector<Mesh3DVertex*> get_mesh_vertices_on_edge(const long long edge_id) = 0;
	virtual void add_mesh_edge_intersection_to_grid_face(
	    const long long face_id, GridFaceMeshEdgeIntersection intersection) = 0;
	virtual std::vector<GridFaceMeshEdgeIntersection> get_mesh_edge_intersections_on_face(
	    const long long face_id) = 0;
	virtual void clear_mesh_edge_intersections() = 0;

	virtual void add_graph_on_face(const long long face_id,
	                               const std::pair<Mesh3DVertex*, Mesh3DVertex*>& edge,
	                               Mesh3DTriangle* outside_triangle) = 0;
	virtual absl::flat_hash_map<std::pair<Mesh3DVertex*, Mesh3DVertex*>, Mesh3DTriangle*>
	getGraphOnFace(const long long face_id) const = 0;

	// Converts all pointers saved on the grid from old version to a new one by using index converters
	// saved in the mesh state.
	virtual void update_mesh_pointers(const Mesh3DSaveState& idx_converters) = 0;

	virtual void addInterpolatedVertPropsOnVertex(long long vertex_id, VertexProperties vert_props) = 0;
	virtual VertexProperties getInterpolatedVertPropsFromVertex(long long vertex_id) = 0;
	virtual void setRaysUpdatedValue(bool value) = 0;
	virtual bool isMeshVertexInGridCellNaive(Mesh3DVertex* mesh_vertex, long long cell_id) = 0;

	virtual int getLabelFromUniqueMaterialVector(long long grid_vertex) = 0;
	virtual bool isVertexInComplexRegion(long long grid_vertex) = 0;

	virtual void addUniqueLabeling(long long grid_vertex, int label) = 0;
	virtual absl::flat_hash_map<long long, int>::iterator getUniqueLabeling(
	    long long grid_vertex) = 0;
	virtual bool hasUniqueLabeling(long long grid_vertex) = 0;
	virtual absl::flat_hash_map<long long, int>& getUniqueLabelingMap() = 0;
	virtual void addOptimizedMCEdgePoint(long long grid_edge, Vec3d optimized_point) = 0;
	virtual absl::flat_hash_map<long long, Vec3d>::iterator getOptimizedMCEdgePoint(
	    long long grid_edge) = 0;
	virtual bool hasOptimizedMCEdgePoint(long long grid_edge) = 0;

	//---------------FUNCITONS TO MANIPULATE ELEMENTS GENERATED BY MARCHING CUBES-----------------
	virtual std::pair<absl::flat_hash_map<Mesh3DVertex*, long long>::iterator, bool>
	insertNewMeshVertexIntoCellSet(Mesh3DVertex* vertex, long long cell_id) = 0;
	virtual std::pair<absl::flat_hash_map<Mesh3DVertex*, long long>::iterator, bool>
	insertNewMeshVertexIntoFaceSet(Mesh3DVertex* vertex, long long face_id) = 0;
	virtual std::pair<absl::flat_hash_map<Mesh3DVertex*, long long>::iterator, bool>
	insertNewMeshVertexIntoEdgeSet(Mesh3DVertex* vertex, long long edge_id) = 0;
	virtual std::pair<absl::flat_hash_set<Mesh3DVertex*>::iterator, bool>
	insertNewMeshVertexIntoT1Set(Mesh3DVertex* vertex) = 0;

	virtual bool isVertexNewInCell(Mesh3DVertex* vertex) = 0;
	virtual bool isVertexNewOnFace(Mesh3DVertex* vertex) = 0;
	virtual bool isVertexNewOnEdge(Mesh3DVertex* vertex) = 0;
	virtual bool isVertexNewT1(Mesh3DVertex* vertex) = 0;

	virtual absl::flat_hash_map<Mesh3DVertex*, long long>& getNewMeshVerticesInCells() = 0;
	virtual absl::flat_hash_map<Mesh3DVertex*, long long>& getNewMeshVerticesOnFaces() = 0;
	virtual absl::flat_hash_map<Mesh3DVertex*, long long>& getNewMeshVerticesOnEdges() = 0;
	virtual absl::flat_hash_set<Mesh3DVertex*>& getNewT1MeshVertices() = 0;

	// helper functions for compiling lists of grid element IDs
	void add_vertex_if_inbounds(const long long i, const long long j, const long long k,
	                            std::vector<long long>& IDs) const;
	void add_edge_if_inbounds(const long long i, const long long j, const long long k,
	                          const long long orient, std::vector<long long>& IDs) const;
	void add_face_if_inbounds(const long long i, const long long j, const long long k,
	                          const long long orient, std::vector<long long>& IDs) const;
	void add_cell_if_inbounds(const long long i, const long long j, const long long k,
	                          std::vector<long long>& IDs) const;

	// return width of a cubic grid cell
	double get_cell_dx() const;
	// return dimensons of the grid
	long long get_dim_nx() const;
	long long get_dim_ny() const;
	long long get_dim_nz() const;
	// return number of cells
	long long get_num_cells() const;
	virtual long long getNumAllocatedCells() const = 0;

 private:
	// data members
	double x0, y0, z0;  // origin of the grid
	double cell_dx;     // width of a cubic grid cell (same as height or depth of a cubic grid cell)
	long long nx, ny, nz;  // dimensions of the grid

	// helper variables to avoid multiple re-computations when decoding vertex, edge, face, and cell
	// IDs
	long long nxp1, nyp1, nzp1;  // nx+1, ny+1, nz+1... used for counting #faces, #edges, and #verts,
	                             // which are one more than #cells in each dimension
	long long num_cells;         // precomputing nx*ny*nz
	long long nynz, nyp1nzp1;    // precomputing ny*nz and (ny+1)*(nz+1)
	long long nynz3, nyp1nzp13;  // precomputing ny*nz*3 and (ny+1)*(nz+1)*3
	long long nz3, nzp13;        // precomputing nz*3 and (nz+1)*3
};

// inline function here
// input: vertex coordinates (i, j, k)
// output bool: true if the vertex is out of bounds, false otherwise
//
// out of bounds if i,j, or k are negative
// out of bounds if i > nx (i larger than maximum number of vertices in x dimension)
//	... similar for j and k directions
//
//	Note that nx, ny, nz are the number of grid *cells* in each dimension.
//		... the number of vertices will be one more in each dimension,
//			because vertices are on the boundary of the grid.
inline bool Grid3DInterface::vertex_out_of_bounds(const long long i, const long long j,
                                                  const long long k) const {
	return (i < 0 || i > nx || j < 0 || j > ny || k < 0 || k > nz);
}

// input: edge coordinates (i, j, k)
// output bool: true if the edge is out of bounds, false otherwise
//
// out of bounds if i,j, or k are negative
// out of bounds if i > nx (i larger than maximum number of edges in x dimension)
//	... similar for j and k directions
// out of bounds (actually complete nonsense) if orientation is anything other than 0, 1, or 2.
//
//	Note that nx, ny, nz are the number of grid *cells* in each dimension.
//		... the number of edges will be one more in each dimension,
//			because edges are on the boundary of the grid.
inline bool Grid3DInterface::edge_out_of_bounds(const long long i, const long long j,
                                                const long long k, const long long orient) const {
	// coordinate checks are functionally equivalent to vertex_out_of_bounds,
	//		... plus checking for edge orientation
	return (vertex_out_of_bounds(i, j, k) || orient < 0 || orient > 2);
}

// input: face coordinates (i, j, k)
// output bool: true if the face is out of bounds, false otherwise
//
// out of bounds if i,j, or k are negative
// out of bounds if i > nx (i larger than maximum number of faces in x dimension)
//	... similar for j and k directions
// out of bounds (actually complete nonsense) if orientation is anything other than 0, 1, or 2.
//
//	Note that nx, ny, nz are the number of grid *cells* in each dimension.
//		... the number of faces will be one more in each dimension,
//			because faces are on the boundary of the grid.
inline bool Grid3DInterface::face_out_of_bounds(const long long i, const long long j,
                                                const long long k, const long long orient) const {
	// functionally equivalent to edge_out_of_bounds().
	return edge_out_of_bounds(i, j, k, orient);
}

// input: cell coordinates (i, j, k)
// output bool: true if the cell is out of bounds, false otherwise
//
// out of bounds if i,j, or k are negative
// out of bounds if i >= nx (i larger than maximum number of cells in x dimension)
//	... similar for j and k directions
//
// Note: The maximum coordinate bounds are different for cells compared to other primitives,
//			because verts, edges, and faces form the boundary of a cell,
//			so there will be one fewer cell in each row than the other grid primitives.
inline bool Grid3DInterface::cell_out_of_bounds(const long long i, const long long j,
                                                const long long k) const {
	return (i < 0 || i >= nx || j < 0 || j >= ny || k < 0 || k >= nz);
}

//////////////////////////
//
// Grid ID functions
//
// functions which take in (i,j,k) coordinates of a grid [vertex,edge,face,cell] and output a unique
// integer ID
//		ID is generated by numbering all cells in order,
//			first along z direction:		(0,0,0), (0,0,1), (0,0,2), ... to (0,0,nz)
//			then along y direction:			(0,1,0), (0,1,1), ... (0,2,0), (0,2,1), ... to (0,ny,nz)
//			then finally along x direction: (1,0,0), (1,0,1), ...  to (nx,ny,nz)
//				(Note that we iterate up to (nx,ny,nz) instead of (nx-1, ny-1, nz-1),
//				because vertices, edges, and faces will have one more element than cells in each
// dimension.)
//
//		incrementing by (0,0,1) increases ID by 1.
//		incrementing by (0,1,0) increases ID by (nz+1) (an entire row of cells)
//		incrementing by (1,0,0) increases ID by (ny+1)*(nz+1) (an entire rectangular plate full of
// cells
//
//		Edges and Faces also have one of 3 possible *orientations*, which adds another dimension.
//			In these cases, we count by iterating through a 4D grid instead of 3D.
//
//		Edge with coordinates (i,j,k) and orientation 0 is the edge from vertex(i,j,k) to
// vertex(i+1,j,k)
// 		Edge with coordinates (i,j,k) and orientation 1 is the edge from vertex(i,j,k) to
// vertex(i,j+1,k)
// 		Edge with coordinates (i,j,k) and orientation 2 is the edge from vertex(i,j,k) to
// vertex(i,j,k+1)
//
//		Face with coordinates (i,j,k) and orientation 0 is the face in cell (i,j,k) containing vertex
//(i,j,k) with normal (1,0,0)
// 		Face with coordinates (i,j,k) and orientation 1 is the face in cell (i,j,k) containing vertex
// (i,j,k) with normal (0,1,0)
// 		Face with coordinates (i,j,k) and orientation 2 is the face in cell (i,j,k) containing vertex
// (i,j,k) with normal (0,0,1)

// input vertex coordinates (i,j,k)
// returns unique integer ID for this vertex
// encoding algorithm is explained in larger comment above
inline long long Grid3DInterface::get_vertex_id(const long long i, const long long j,
                                                const long long k) const {
	return (i * nyp1 + j) * nzp1 + k;  // equivalent to: return i*(ny+1)*(nz+1) + j*(nz+1) + k;
}

// input edge coordinates (i,j,k,orient)
// returns unique integer ID for this edge
// encoding algorithm is explained in larger comment above
inline long long Grid3DInterface::get_edge_id(const long long i, const long long j,
                                              const long long k, const long long orient) const {
	return ((i * nyp1 + j) * nzp1 + k) * 3 +
	       orient;  // equivalent to: return i*(ny+1)*(nz+1)*3 + j*(nz+1)*3 + k*3 + orient;
}

// input face coordinates (i,j,k,orient)
// returns unique integer ID for this face
// encoding algorithm is explained in larger comment above
inline long long Grid3DInterface::get_face_id(const long long i, const long long j,
                                              const long long k, const long long orient) const {
	return get_edge_id(i, j, k, orient);
}

// input cell coordinates (i,j,k)
// returns unique integer ID for this cell
// encoding algorithm is explained in larger comment above
inline long long Grid3DInterface::get_cell_id(const long long i, const long long j,
                                              const long long k) const {
	return get_vertex_id(i, j, k);
}