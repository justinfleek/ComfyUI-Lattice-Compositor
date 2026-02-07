/* Grid3DSparseCubical.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, 2021
 *
 * This header defines a sparse cubical grid, intended to store information only on a small subset
 * of all grid cells. One useful example is trackng state only on a mesh surface, instead of the
 * whole interior.
 *
 * Modules should only access it through its parent interface class (Grid3DInterface).
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <unordered_map>
#include <unordered_set>

#include "../../abseil-cpp/absl/container/flat_hash_map.h"
#include "../../abseil-cpp/absl/container/flat_hash_set.h"
#include "Grid3DInterface.h"
#include "GridMeshIntersection.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// Implementation of Grid3DInterface in a sparse manner. Sparcity is maintained by keeping
// information only about cells that cointain triangles or by keeping information for specifically
// reference cell elements.
class Grid3DSparseCubical : public Grid3DInterface {
 public:
	// constructors
	Grid3DSparseCubical();
	virtual ~Grid3DSparseCubical() = default;

	// Functions to handle materials in a sparse way.
	// The material of the vertex is the same as assigned by the `set_vertex_material` function.
	// If no material is assigned to a vertex, we get the material of a closest neighbour vertex on
	// the sparse ray when looking towards the origin of the ray.
	// This final check is possible due to material vector being a piecewise constant function with
	// changes exactly at the mesh boundaries. These changes are kept on the rays.
	virtual void setVertexMaterial(const long long vertex_id, SparseVector<int> material) override;
	virtual SparseVector<int> getVertexMaterial(const long long vertex_id) override;
	// Erases previous vertex material vector values and sets new ones from the passed object.
	virtual void setVertexMaterialVectors(
	    absl::flat_hash_map<long long, SparseVector<int>> per_vertex_materials) override;

	// Returns a unit vector corresponding to `orientation`, i.e. pointing in the increasing direction
	// of the coordinate axis determined by `orientation`.
	virtual Vec3d getRayDirection(long long orientation) override;

	//-----------------------------------------------------------------------
	// Functions to handle conversion between mesh labels (arbitrary integers, acquired on algorithm
	// input) and grid labels (conseqcutive integers that start with 0 - the global outside).

	// Converts a pair of mesh labels to a pair of grid labels. If a mesh label is encountered that is
	// not yet mapped to a grid label, the corresponding [key,value] pair is added to
	// `material_encoder`. NOTE: it might be safer/more efficient to construct the encoder directly
	// when loading a mesh.
	virtual Vec2i convertMeshLabelsToGridLabels(Vec2i mesh_labels) override;

	// Constructs `material_decoder`, which transforms grid labels into mesh labels, by inverting the
	// `material_encoder` map.
	virtual void constructMaterialDecoder() override;
	// Converts a grid label to a mesh label using `material_decoder`, if the input `grid_label` is
	// not registered with any mesh label, returns -1 and prints an error.
	virtual int convertGridLabelToMeshLabel(int grid_label) override;
	// Converts a grid label pair to a mesh label pair using `material_decoder` using the function for
	// converting a single grid label to mesh label.
	virtual Vec2i convertGridLabelToMeshLabel(Vec2i grid_labels) override;

	//-----------------------------------------------------------------------
	// Functions to handle sparcity, tracking only cells intersecting with mesh triangles.

	// Registers the input `triangle` as potentially intersecting the grid cell with input `cell_id`
	// by adding an entry to `per_cell_triangles_`. This might cause a change in which cells are
	// tracked in the sparse ray lattices, therefore the `is_sparse_rays_lattice_updated` flags are
	// set to false.
	virtual void addTriangleToCell(const long long cell_id, Mesh3DTriangle* triangle) override;

	// Registers the input `triangle` as potentially intersecting the grid cell with input `cell_id`
	// by adding an entry to `per_cell_triangles_`. Does not set `is_sparse_rays_lattice_updated`
	// flags to false, used when many triangles are added sequentially.
	virtual void addTriangleToCellWithoutFlaggingRays(const long long cell_id,
	                                                  Mesh3DTriangle* triangle_id) override;

	// Sets the `is_sparse_rays_lattice_updated` flags to input value, typically called with input
	// value `flase` after registering a new triangle on the grid.
	virtual void setRaysUpdatedValue(bool value) override;

	virtual void remove_triangle_from_cell(const long long cell_id,
	                                       Mesh3DTriangle* triangle_id) override;
	virtual std::vector<Mesh3DTriangle*> getCellTriangles(const long long cell_id) const override;
	virtual absl::flat_hash_set<Mesh3DTriangle*> get_cell_triangles_set(
	    const long long cell_id) override;
	// return all the key values from `per_cell_triangles_` map, i.e. all cell ids that have triangles
	// registered on them
	virtual std::vector<long long> getCellsWithTriangles() override;

	// Functions to track intersections of grid elements with a mesh.
	virtual void addIntersectionToEdge(GridEdgeMeshFaceIntersection intersection) override;
	virtual std::vector<GridEdgeMeshFaceIntersection> get_intersections_on_edge(
	    const long long edge_id) override;
	virtual void add_mesh_edge_intersection_to_grid_face(
	    const long long face_id, GridFaceMeshEdgeIntersection intersection) override;
	virtual std::vector<GridFaceMeshEdgeIntersection> get_mesh_edge_intersections_on_face(
	    const long long face_id) override;
	virtual void clear_mesh_edge_intersections() override;

	// Returns a collection of allocated grid vertices grouped into rays. Rays are buckets that hold
	// elements that line on the same line for a given direction. Elements are sorted by the
	// increasing coordinate along the line. In other words, each ray represents a traversal order of
	// elements that lie on the same line.
	virtual const SparseRaysContainer& getSparseRays(long long orientation) override;

	// Functions to deal with complex elements on the grid.
	//---------------- manipulating vertex complexity
	virtual bool isVertexMarkedComplex(const long long vertex_id) override;
	virtual void markVertexAsComplex(const long long vertex_id) override;

	//---------------- manipulating edge complexity
	virtual bool isEdgeMarkedTopoComplex(const long long edge_id) override;
	virtual void markEdgeAsTopoComplex(const long long edge_id) override;
	virtual bool isEdgeMarkedGeomComplex(const long long edge_id) override;
	virtual void markEdgeAsGeomComplex(const long long edge_id) override;
	virtual bool doesEdgeHaveFixedComplexNeighbors(const long long edge_id) override;
	virtual bool isFrontEdge(const long long edge_id) override;
	virtual absl::flat_hash_set<long long> getGeomComplexEdges() override;
	virtual absl::flat_hash_set<long long> getTopoComplexGeomSimpleEdges() override;

	//---------------- manipulating face complexity
	virtual bool isFaceMarkedTopoSimple(const long long face_id) override;
	virtual void markFaceAsTopoSimple(const long long face_id) override;
	virtual void unmarkFaceAsTopoSimple(const long long face_id) override;
	virtual bool isFaceMarkedTopoComplex(const long long face_id) override;
	virtual void markFaceAsTopoComplex(const long long face_id) override;
	virtual bool isFaceMarkedTopoSuspicious(const long long face_id) override;
	virtual void markFaceAsTopoSuspicious(const long long face_id) override;
	virtual bool isFaceMarkedGeomComplex(const long long face_id) override;
	virtual void markFaceAsGeomComplex(const long long face_id) override;
	virtual absl::flat_hash_set<long long> getTopoComplexFaces() const override;

	//---------------- manipulating cell complexity
	virtual bool isCellMarkedComplex(const long long cell_id,
	                                 const ComplexCellType type) const override;
	virtual void markCellAsComplex(const long long cell_id, const ComplexCellType type) override;
	virtual void unmarkCellAsComplex(const long long cell_id, const ComplexCellType type) override;
	virtual void markCellAsEdgeDeep(const long long cell_id) override;
	virtual void markCellAsEdgeShallow(const long long cell_id) override;
	virtual std::vector<long long> getComplexCellsVector(const ComplexCellType type) const override;
	virtual absl::flat_hash_set<long long> getComplexCellsSet(
	    const ComplexCellType type) const override;

	//---------------- retrieve front elements
	// Functions to retrieve front elements - a front face is any face adjacent to one complex and one
	// simple cell, complex region front cells/simple region front cells are cells from the respective
	// regions that are adjacent to front faces (i.e. complex cells neighboring simple cells and
	// simple cells neighboring complex cells respectively).
	virtual bool isFaceInComplexFront(long long face_id) const override;
	virtual std::vector<long long> getFrontFacesVector() const override;
	virtual absl::flat_hash_set<long long> getFrontFacesSet() const override;
	virtual std::vector<long long> getComplexRegionFrontCellsVector() const override;
	virtual absl::flat_hash_set<long long> getComplexRegionFrontCellsSet() const override;
	virtual std::vector<long long> getSimpleRegionFrontCellsVector() const override;
	virtual absl::flat_hash_set<long long> getSimpleRegionFrontCellsSet() const override;

	virtual absl::flat_hash_set<long long> getEdgeDeepCells() const override;
	virtual absl::flat_hash_set<long long> getEdgeShallowCells() const override;

	// Functions to track mesh elements on the grid. Useful to pass information on the complex cell
	// front faces and for further sewing of marching cubes interfaces with original mesh.
	virtual void add_mesh_vertex_to_edge(const long long edge_id, Mesh3DVertex* v1) override;
	virtual std::vector<Mesh3DVertex*> get_mesh_vertices_on_edge(const long long edge_id) override;

	virtual void add_graph_on_face(const long long face_id,
	                               const std::pair<Mesh3DVertex*, Mesh3DVertex*>& edge,
	                               Mesh3DTriangle* outside_triangle) override;
	virtual absl::flat_hash_map<std::pair<Mesh3DVertex*, Mesh3DVertex*>, Mesh3DTriangle*>
	getGraphOnFace(const long long face_id) const override;

	// Goes through each data structure that contains pointers to mesh elements saved on the grid, and
	// updates these pointers using the index conversion maps in the provided Mesh3DSaveState. When
	// saving, this means converting mesh pointers to numerical indices. When loading, this means
	// converting numerical indices to mesh pointers. NOTE: in case we choose to save additional mesh
	// pointers on the grid, this function will need to be updated.
	virtual void update_mesh_pointers(const Mesh3DSaveState& idx_converters) override;

	virtual void addInterpolatedVertPropsOnVertex(long long vertex_id, VertexProperties vert_props) override;
	virtual VertexProperties getInterpolatedVertPropsFromVertex(long long vertex_id) override;
	virtual bool isMeshVertexInGridCellNaive(Mesh3DVertex* mesh_vertex, long long cell_id) override;

	// Retrieves the unique label on `grid_vertex`, assuming its material vector is unique. Otherwise
	// the result is not defined.
	virtual int getLabelFromUniqueMaterialVector(long long grid_vertex) override;

	// Checks if the input `grid_vertex` is inside the complex region (at least one of its neighbor
	// cells is complex).
	virtual bool isVertexInComplexRegion(long long grid_vertex) override;

	// for each grid vertex in the complex region stores the unique material label on that vertex
	virtual void addUniqueLabeling(long long grid_vertex, int label) override;
	virtual absl::flat_hash_map<long long, int>::iterator getUniqueLabeling(
	    long long grid_vertex) override;
	virtual bool hasUniqueLabeling(long long grid_vertex) override;
	virtual absl::flat_hash_map<long long, int>& getUniqueLabelingMap() override;
	//
	virtual void addOptimizedMCEdgePoint(long long grid_edge, Vec3d optimized_point) override;
	virtual absl::flat_hash_map<long long, Vec3d>::iterator getOptimizedMCEdgePoint(
	    long long grid_edge) override;
	virtual bool hasOptimizedMCEdgePoint(long long grid_edge) override;

	//---------------FUNCITONS TO MANIPULATE ELEMENTS GENERATED BY MARCHING CUBES-----------------
	// Insert the pair (`vertex`, grid element id) into one of three sets, based on which type of grid
	// element was `vertex` generated in/on. Returns the insertion return value (pair consisting of an
	// iterator to the inserted element (or to the element that prevented the insertion) and a bool
	// denoting whether the insertion took place).
	virtual std::pair<absl::flat_hash_map<Mesh3DVertex*, long long>::iterator, bool>
	insertNewMeshVertexIntoCellSet(Mesh3DVertex* vertex, long long cell_id) override {
		return new_mesh_vertices_in_cells.insert({vertex, cell_id});
	}
	virtual std::pair<absl::flat_hash_map<Mesh3DVertex*, long long>::iterator, bool>
	insertNewMeshVertexIntoFaceSet(Mesh3DVertex* vertex, long long face_id) override {
		return new_mesh_vertices_on_faces.insert({vertex, face_id});
	}
	virtual std::pair<absl::flat_hash_map<Mesh3DVertex*, long long>::iterator, bool>
	insertNewMeshVertexIntoEdgeSet(Mesh3DVertex* vertex, long long edge_id) override {
		return new_mesh_vertices_on_edges.insert({vertex, edge_id});
	}
	virtual std::pair<absl::flat_hash_set<Mesh3DVertex*>::iterator, bool>
	insertNewMeshVertexIntoT1Set(Mesh3DVertex* vertex) override {
		return new_T1_split_mesh_vertices.insert(vertex);
	}

	virtual bool isVertexNewInCell(Mesh3DVertex* vertex) override {
		return new_mesh_vertices_in_cells.count(vertex);
	};
	virtual bool isVertexNewOnFace(Mesh3DVertex* vertex) override {
		return new_mesh_vertices_on_faces.count(vertex);
	};
	virtual bool isVertexNewOnEdge(Mesh3DVertex* vertex) override {
		return new_mesh_vertices_on_edges.count(vertex);
	};
	virtual bool isVertexNewT1(Mesh3DVertex* vertex) override {
		return new_T1_split_mesh_vertices.count(vertex);
	}

	// Return the map new mesh vertex->id of grid cell/face/edge it was generated in/on.
	virtual absl::flat_hash_map<Mesh3DVertex*, long long>& getNewMeshVerticesInCells() override {
		return new_mesh_vertices_in_cells;
	}
	virtual absl::flat_hash_map<Mesh3DVertex*, long long>& getNewMeshVerticesOnFaces() override {
		return new_mesh_vertices_on_faces;
	}
	virtual absl::flat_hash_map<Mesh3DVertex*, long long>& getNewMeshVerticesOnEdges() override {
		return new_mesh_vertices_on_edges;
	}
	virtual absl::flat_hash_set<Mesh3DVertex*>& getNewT1MeshVertices() override {
		return new_T1_split_mesh_vertices;
	}

	virtual long long getNumAllocatedCells() const override { return per_cell_triangles_.size(); }

 private:
	// Picks vertices of given cells and shoots rays in direction defined by orientation. The
	// resulting collection of rays is returned.
	SparseRaysContainer constructLatticeForCells(const std::vector<long long>& cell_ids,
	                                             long long orientation) const;

	absl::flat_hash_set<long long> complex_vertices_;
	absl::flat_hash_set<long long> topo_complex_edges_;
	absl::flat_hash_set<long long> geom_complex_edges_;
	absl::flat_hash_set<long long> topo_simple_faces_;
	absl::flat_hash_set<long long> topo_complex_faces_;
	absl::flat_hash_set<long long> topo_suspicious_faces_;
	absl::flat_hash_set<long long> geom_complex_faces_;
	absl::flat_hash_set<long long> fixed_complex_cells_;
	absl::flat_hash_set<long long> flexible_complex_cells_;
	absl::flat_hash_set<long long> edge_shallow_cells_;
	absl::flat_hash_set<long long> edge_deep_cells_;

	// These are mutable to allow lazy evaluation.
	mutable std::vector<long long> complex_cell_front_faces_;
	mutable bool is_complex_cell_front_updated_;

	absl::flat_hash_map<long long, SparseVector<int>> per_vertex_material_labels_;
	// for each grid vertex in the complex region stores the unique material label on that vertex
	absl::flat_hash_map<long long, int> unique_labeling;
	//
	absl::flat_hash_map<long long, Vec3d> optimizedMCEdgeVertices;

	// Data that facilitates sparse storage of material labels. `material_encoder` maps mesh labels,
	// which are arbitrary integers to grid labels, which are conscutive integers that start with 0 -
	// the global outside. [key,value] pairs are added in function `convertMeshLabelsToGridLabels`,
	// when a mesh label is encountered for the first time.
	absl::flat_hash_map<int, int> material_encoder;
	// Helper variable used in constructing `material_encoder`, that tracks the currently lowest
	// assigned grid label value. It is therefore <= `mesh.getNumberLabels`. Initialized to 1 in the
	// constructor, since label 0 is fixed to be the global outside label.
	int lowest_non_used_material;

	// converts grid labels to mesh labels
	// TODO: this could be made faster by implementing it as a vector
	absl::flat_hash_map<int, int> material_decoder;
	// Maps a grid edge to a vector of grid edge-mesh triangle intersections on it.
	absl::flat_hash_map<long long, std::vector<GridEdgeMeshFaceIntersection>> per_edge_intersections_;
	// Maps a grid edge to a vector of grid edge-mesh triangle intersection information on it. It is
	// different from the above in that it doesn't specifically remember triangles, but rather the
	// labels that would have been on the triangles. This is used in marching cuber for unifying grid
	// vertex labels. Alternatively, we could move that whole procedure to a separate module before
	// cell separation and just use `per_edge_intersections_`;
	absl::flat_hash_map<long long, std::vector<GridEdgeMeshFaceIntersection>>
	    per_edge_intersections_no_triangles;
	absl::flat_hash_map<long long, std::vector<Mesh3DVertex*>> per_edge_mesh_vertices_;
	absl::flat_hash_map<long long, std::vector<GridFaceMeshEdgeIntersection>> per_face_mesh_edges_;
	// Maps a grid cell to a set of triangles that potentially intersect it.
	absl::flat_hash_map<long long, absl::flat_hash_set<Mesh3DTriangle*>> per_cell_triangles_;
	// Grid lattice that to a grid ray assigns grid vertices that lie on the ray, and are part of a
	// grid cell that has triangles registered on it. Facilitates sparse labeling.
	std::vector<SparseRaysContainer> sparse_rays_;
	// Three flags that track whether `sparse_rays_` lattice is up to date.
	std::vector<char> is_sparse_rays_lattice_updated;

	// a map that assigns to a grid vertex index a Vec3d calculated to be the distance weighted
	// interpolation of mesh vertex velocities on mesh vertices near the grid vertex; "near" in this
	// context means mesh vertices of triangles that intersect at least one of the 8 grid cells
	// adjacent to the grid vertex
	absl::flat_hash_map<long long, VertexProperties> interpolated_vert_props_on_vertices_;

	// a map that assigns to a grid face id a map that connects a pair of mesh vertices (on the face)
	// with a mesh triangle that is outside the complex region; used for sewing
	absl::flat_hash_map<long long,
	                    absl::flat_hash_map<std::pair<Mesh3DVertex*, Mesh3DVertex*>, Mesh3DTriangle*>>
	    graph_on_faces;

	// map where a key is the pointer to a mesh vertex generated inside a grid cell during surface
	// reconstruction, and its value is the id of the grid cell
	absl::flat_hash_map<Mesh3DVertex*, long long> new_mesh_vertices_in_cells;
	// map where a key is the pointer to a mesh vertex generated on a grid face during surface
	// reconstruction, and its value is the id of the grid face
	absl::flat_hash_map<Mesh3DVertex*, long long> new_mesh_vertices_on_faces;
	// map where a key is the pointer to a mesh vertex generated on a grid edge during surface
	// reconstruction, and its value is the id of the grid edge
	absl::flat_hash_map<Mesh3DVertex*, long long> new_mesh_vertices_on_edges;
	// set of mesh vertices generated during T1 resolution
	absl::flat_hash_set<Mesh3DVertex*> new_T1_split_mesh_vertices;
};