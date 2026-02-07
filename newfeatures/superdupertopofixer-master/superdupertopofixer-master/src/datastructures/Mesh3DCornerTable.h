/* Mesh3DCornerTable.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the header for the corner table mesh implementation. Modules should only access it
 * through its parent interface class (Mesh3DInterface).
 *
 * TODO:
 * - implement the mesh functionalities
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <fstream>
#include <iostream>
#include <unordered_set>

#include "../../abseil-cpp/absl/container/flat_hash_map.h"
#include "../../abseil-cpp/absl/container/flat_hash_set.h"
#include "../schemes/TopoFixerSettings.h"
#include "Mesh3DHalfCorner.h"
#include "Mesh3DInterface.h"
#include "Mesh3DSaveState.h"
#include "Mesh3DTriangle.h"
#include "Mesh3DVertex.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class manages the mesh data structure
class Mesh3DCornerTable : public Mesh3DInterface {
 public:
	// constructors
	Mesh3DCornerTable(const TopoFixerSettings& settings);
	virtual ~Mesh3DCornerTable() = default;

	// retrieve mesh information functions
	virtual int getNumberLabels() const override;
	virtual double getAverageEdgeLength() const override;
	virtual double getMinEdgeLength() const override;
	virtual double getMaxEdgeLength() const override;

	virtual const absl::flat_hash_set<Mesh3DTriangle*>& ListTriangles() const override {
		return mesh_triangles_list;
	};
	virtual const absl::flat_hash_set<Mesh3DVertex*>& ListVertices() const override {
		return mesh_vertices_list;
	};
	virtual const absl::flat_hash_set<Mesh3DHalfCorner*>& ListHalfCorners() const override {
		return mesh_half_corners_list;
	}

	virtual void clearEdgeCollapseCounters() override {
		t1_retraction_edge_collapse_cancel = 0;
		tetrahedron_edge_collapse_cancel = 0;
		in_plane_edge_collapse_cancel = 0;
		hoppe_criterion_edge_collapse_cancel = 0;
		double_four_valence_edge_collapse_cancel = 0;
		candidate_covering_edge_collapse_cancel = 0;
	}
	virtual void addT1RetractionEdgeCollapseCancel() override {
		t1_retraction_edge_collapse_cancel++;
	}
	virtual void addTetrahedronEdgeCollapseCancel() override { tetrahedron_edge_collapse_cancel++; }
	virtual void addInPlaneFlipEdgeCollapseCancel() override { in_plane_edge_collapse_cancel++; }
	virtual void addHoppeCriterionEdgeCollapseCancel() override {
		hoppe_criterion_edge_collapse_cancel++;
	}
	virtual void addDoubleFourValenceEdgeCollapseCancel() override {
		double_four_valence_edge_collapse_cancel++;
	}
	virtual void addCandidateCoveringEdgeCollapseCancel() override {
		candidate_covering_edge_collapse_cancel++;
	}
	virtual int getT1RetractionEdgeCollapseCancel() override {
		return t1_retraction_edge_collapse_cancel;
	}
	virtual int getTetrahedronEdgeCollapseCancel() override {
		return tetrahedron_edge_collapse_cancel;
	}
	virtual int getInPlaneFlipEdgeCollapseCancel() override { return in_plane_edge_collapse_cancel; }
	virtual int getHoppeCriterionEdgeCollapseCancel() override {
		return hoppe_criterion_edge_collapse_cancel;
	}
	virtual int getDoubleFourValenceEdgeCollapseCancel() override {
		return double_four_valence_edge_collapse_cancel;
	}
	virtual int getCandidateCoveringEdgeCollapseCancel() override {
		return candidate_covering_edge_collapse_cancel;
	}

	virtual absl::flat_hash_set<Mesh3DTriangle*>& getMCTriangles() override { return mc_triangles; }
	virtual const absl::flat_hash_set<Mesh3DTriangle*>& getMCTriangles() const override {
		return mc_triangles;
	}
	virtual void addMCTriangle(Mesh3DTriangle* triangle) override { mc_triangles.insert(triangle); }

	virtual absl::flat_hash_set<Mesh3DTriangle*>& getT1Triangles() override { return t1_triangles; }
	virtual const absl::flat_hash_set<Mesh3DTriangle*>& getT1Triangles() const override {
		return t1_triangles;
	}
	virtual void addT1Triangle(Mesh3DTriangle* triangle) override { t1_triangles.insert(triangle); }

	virtual absl::flat_hash_set<SortedMeshEdge>& getNoCollapseEdges() override {
		return no_collapse_edges;
	}
	virtual const absl::flat_hash_set<SortedMeshEdge>& getNoCollapseEdges() const override {
		return no_collapse_edges;
	}
	virtual void addNoCollapseEdge(Mesh3DVertex* v0, Mesh3DVertex* v1) override {
		no_collapse_edges.insert(SortedMeshEdge(v0, v1));
	}

	virtual absl::flat_hash_set<Mesh3DTriangle*>& getT1HFTriangles() override {
		return t1_hf_triangles;
	}
	virtual const absl::flat_hash_set<Mesh3DTriangle*>& getT1HFTriangles() const override {
		return t1_hf_triangles;
	}
	virtual void addT1HFTriangle(Mesh3DTriangle* triangle) override {
		t1_hf_triangles.insert(triangle);
	}

	// other functions for getting to mesh elements
	// go through manifold loop around center_vertex, starting from a halfcorner (no switching to
	// duals) and accumulate all half-corners in the `output_corners` vector.
	virtual void walkManifoldLoop(Mesh3DVertex* center, Mesh3DHalfCorner* start_halfcorner,
	                              std::vector<Mesh3DHalfCorner*>& output_corners) override;
	void walkAroundVertex(Mesh3DVertex* center_vertex,
	                      void (*halfcorner_function)(Mesh3DHalfCorner*, int),
	                      int function_int_arg = 0);
	//
	void getHalfCornerOppEdge(Mesh3DHalfCorner* opp_halfcorner, Mesh3DVertex* center_vertex,
	                          Mesh3DVertex* v2);

	// functions for retrieving drawing information
	virtual void getVertexPositions(std::vector<Vec3d>& vertex_positions) override;
	virtual Vec3d getMeshCenter() override;

	// mesh operations

	Mesh3DVertex* midSplitNewCoords(Mesh3DVertex* v1, Mesh3DVertex* v2);
	Mesh3DVertex* massCenterNewVert(Mesh3DTriangle* triangle);
	virtual Vec3d pVertCoords(Mesh3DVertex* v1, Mesh3DVertex* v2, double p) override;

	bool isPointInTri(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3, Mesh3DVertex* vert) const;

	// Subdivides a given main triangle into three of them at given coordinates, storing the newly
	// created triangles in the provided pointers. Returns the newly created center of subdivision.
	virtual Mesh3DVertex* triangleSubdivFixedPoint(Mesh3DTriangle*& main_triangle,
	                                               Mesh3DTriangle*& second_triangle,
	                                               Mesh3DTriangle*& third_triangle,
	                                               Vec3d vert_coords) override;

	virtual Mesh3DVertex* EdgeSubdivisionFixedPoint(
	    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d vert_coords,
	    std::vector<Mesh3DTriangle*>& created_triangles) override;
	virtual void transferValuesEdgeSubdivision(Mesh3DVertex* v1, Mesh3DVertex* v2,
	                                           Mesh3DVertex* new_vertex) override;

	int lineIntersectsMesh(Mesh3DVertex* v1, Mesh3DVertex* v2);
	// Returns true if the edge flip across (v1, v2) was successful.
	virtual bool EdgeFlipFast(Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2) override;

	std::vector<Mesh3DHalfCorner*> hfcsAroundEdge(Mesh3DHalfCorner* start_halfcorner) const;

	//--------------------------MESH INFORMATION----------------------------------

	// Returns the number of stored mesh triangles and vertices respectively.
	virtual int getNumberTris() const override;
	virtual int getNumberVerts() const override;

	// Given HC `start_halfcorner` opposite (potentially non-manifold) mesh edge {v0,v1}, adds one HC
	// per extending vertex of this edge to input vector `output_corners` (i.e. rotates around the
	// edge). Optional parameter `include_start_halfcorner` specifies whether `start_halfcorner`
	// should be included in `output_corners` (true by default).
	virtual void walkAroundEdge(Mesh3DHalfCorner* start_halfcorner,
	                            std::vector<Mesh3DHalfCorner*>& output_corners,
	                            bool include_start_halfcorner = true) override;

	// Finds and stores the smallest and largest x,y,z coordinates among all the mesh vertices.
	virtual void getMeshBounds(Vec3d& mesh_min, Vec3d& mesh_max) override;

	// Returns true if the edge spanned by the halfcorner has more than two adjacent triangles.
	virtual bool isEdgeNonmanifold(Mesh3DHalfCorner* opp_edge_corner) const override;

	// Returns the unsigned size of angle spanned by (v1 - v2, v3 - v2) edges. If one of the sides of
	// the angle is 0 length, then it returns a negative value to indicate an error.
	virtual double getAngle(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3) const override;
	virtual double getAngle(Mesh3DHalfCorner* hfc) const override;

	// Returns the cosine of angle spanned by (v1 - v2, v3 - v2) edges. If one of the sides of
	// the angle is 0 length, then it returns -2 to indicate an error.
	virtual double getAngleCos(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3) const override;
	virtual double getAngleCos(Mesh3DHalfCorner* hfc) const override;
	// Finds a triangle in which v1 and v2 share an edge. If no such triangle exists, nullptr is
	// returned.
	virtual Mesh3DTriangle* getCommonTriangle(Mesh3DVertex* v1, Mesh3DVertex* v2) const override;

	// Constructs a map tat assigns to a mesh vertex all adjacent triangles. This is done by iterating
	// over all mesh triangles, not by walking around the vertex, and therefore works for non-manifold
	// vertices.
	virtual absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DTriangle*>>
	buildVertexTriangleAdjacency() const override;

	// Return the number of triangles that are adjacent to the mesh edge opposite of input
	// `opp_edge_corner`.
	virtual int edgeValence(Mesh3DHalfCorner* opp_edge_corner) override;

	virtual absl::flat_hash_set<Mesh3DHalfCorner*> getEdgesAroundVertex(
	    const Mesh3DVertex* center_vertex) const override;

	virtual absl::flat_hash_set<Mesh3DTriangle*> getTrianglesAroundVertex(
	    Mesh3DVertex* vertex) const override;

	virtual std::vector<Mesh3DTriangle*> getTriangleVectorAroundVertex(
	    Mesh3DVertex* vertex) const override;

	// Finds all triangles around an edge defined by two vertices and returns one half-corner per
	// found triangle.
	virtual std::vector<Mesh3DHalfCorner*> getHalfCornersAroundEdge(Mesh3DVertex* v1,
	                                                                Mesh3DVertex* v2) const override;

	// Returns all triangles around an edge defined by two vertices.
	virtual std::vector<Mesh3DTriangle*> getTrianglesAroundEdge(Mesh3DVertex* v1,
	                                                            Mesh3DVertex* v2) const override;
	// Returns all half-corners centered at a given vertex.
	virtual const absl::flat_hash_set<Mesh3DHalfCorner*>& getHalfCornersAtVertex(
	    Mesh3DVertex* vertex) const override;

	virtual void printTriangleVertexIndices(Mesh3DTriangle* triangle) const override;

	// Returns true if vertex `v` exists in mesh.
	virtual bool isVertexInMesh(Mesh3DVertex* v) const override;
	// Returns true if half-corner `h` exists in mesh.
	virtual bool isHalfCornerInMesh(Mesh3DHalfCorner* h) const override;
	// Returns true if triangle `t` exists in mesh.
	virtual bool isTriangleInMesh(const Mesh3DTriangle* t) const override;

	// Returns the sum of triangle areas across the whole mesh.
	virtual double getTotalArea() const override;
	virtual double getTotalKineticEnergy() const override;
	virtual absl::flat_hash_map<Mesh3DVertex*, double> getVertexAreas() const override;
	// Returns true if all edges around the vertex are manifold.
	virtual bool areEdgesAroundManifold(const Mesh3DVertex* v) const override;

	//--------------------------MESH MANIPULATION---------------------------------

	// Indexes local regions around `vertex`, that is, unique manifold neighborhoods around `vertex`,
	// using integers starting at zero. Returns a map that to each `TriSide` around `vertex` assigns
	// its local region index. This is done using the Union-Find data structure. Upon completion, the
	// output parameter `num_regions` will contain the number of local regions around the vertex.
	// NOTE: correctness of this function relies on the assumption that when we iterate over an
	// unordered set twice in a row, the order in which items are accessed is the same both times.
	// This is likely true in the case where the set itself is not modified between the two loops,
	// which is the case here. However, it is useful to keep in mind and check in case a bug appears
	// in the future.
	virtual absl::flat_hash_map<TriSide, size_t> uniteTrianglesInLocalRegions(
	    Mesh3DVertex* vertex, const absl::flat_hash_set<Mesh3DTriangle*>& triangles,
	    int& num_regions) const override;

	// Reindexes local regions according to their labels, ensuring that a region with a lower label
	// has a lower local region index.
	virtual void orderRegionsByLabels(absl::flat_hash_map<TriSide, size_t>& regions) const override;

	// Returns the adjacency matrix of local regions around a central vertex (i.e. a vertex shared by
	// all `triangles`) before pulling apart. To do this, we initialize a square zero matrix of size
	// equal to number of local regions around the central vertex. Then, for each triangle in
	// `triangles`, we take the two regions associated to its two sides (stored in
	// `sides_to_regions`), and set these regions as adjacent. The matrix is by construction
	// symmetric. Correctness of the matrix is predicated on correctness of the inputs `triangles` and
	// `sides_to_regions`.
	virtual std::vector<std::vector<int>> buildRegionsMatrix(
	    const absl::flat_hash_set<Mesh3DTriangle*>& triangles,
	    const absl::flat_hash_map<TriSide, size_t>& sides_to_regions,
	    const int num_regions) const override;

	virtual void shiftMeshByConstant(const int coordinate, const double amount) override;

	// Functions below perform mesh operation and update the adjacency map `vert_to_tris` to reflect
	// the change. They also return a vector of still existing vertices that have been modified by the
	// operation.
	virtual absl::flat_hash_set<Mesh3DVertex*> edgeSubdivisionWithUpdatedVerts(
	    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d split_coords) override;

	virtual absl::flat_hash_set<Mesh3DVertex*> edgeFlipWithUpdatedVerts(Mesh3DTriangle* triangle,
	                                                                    Mesh3DVertex* v1,
	                                                                    Mesh3DVertex* v2) override;

	virtual absl::flat_hash_set<Mesh3DVertex*> edgeCollapseWithUpdatedVerts(
	    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d new_vert_coords) override;

	virtual EdgeCollapseType edgeCollapse(Mesh3DTriangle* triangle, Mesh3DVertex* v1,
	                                      Mesh3DVertex* v2, Vec3d new_coords) override;

	// Remove interface between two regions, conceptually merging them into a single one and removing
	// all diving triangles between them.
	virtual void removeInterface(Vec2i interface) override;

	//--------------------------MESH MAINTENANCE----------------------------------

	// Make a new mesh vertex without specifying its coordinates, add it to `mesh_vertices_list`,
	// assign it an integer label, and return a pointer to it.
	virtual Mesh3DVertex* makeNewVertex() override;

	// Make a new mesh vertex at `vert_coords`, add it to `mesh_vertices_list`, assign it an integer
	// label, and return a pointer to it. Vertex velocity is either set to the optional parameter
	// `vert_vel` (if it is passed to the function), or set to the zero vector (otherwise).
	virtual Mesh3DVertex* makeNewVertexAtCoords(Vec3d vert_coords,
	                                            VertexProperties vert_props) override;
	virtual Mesh3DVertex* makeNewVertexAtCoords(Vec3d vert_coords) override;

	// Make a new mesh vertex at the center of mass of `triangle`, add it to `mesh_vertices_list`,
	// assign it an integer label, and return a pointer to it.
	virtual Mesh3DVertex* makeNewVertexAtTriangleMassCenter(Mesh3DTriangle* triangle) override;

	// Make a new mesh vertex at the midpoint of an edge with endpoints `v1` and `v2`, add it to
	// `mesh_vertices_list`, assign it an integer label, and return a pointer to it.
	virtual Mesh3DVertex* makeNewVertexAtEdgeMidpoint(Mesh3DVertex* v1, Mesh3DVertex* v2) override;

	virtual Mesh3DHalfCorner* makeNewHalfCorner(Mesh3DVertex* v, Mesh3DTriangle* t,
	                                            bool label_side) override;

	// Make a new mesh triangle between the three input vertices, with the input labels, and add it to
	// the list of triangles. Also make 6 new half-corners for the triangle, define their local
	// connectivity (`next`, `prev`, `dual` pointers), and add them to the list of half-corners.
	// `oppos` pointers have to be set externally. Set the half-corner at `v0` and on label side 0 as
	// the reference half-corner for the new triangle. Check if each input vertex has a half-corner
	// assigned, if not, assign it a newly generated half-corner on the 0-label side of the newly
	// generated triangle. Finally, return a pointer to the new triangle.
	virtual Mesh3DTriangle* makeNewTriangle(Mesh3DVertex* v0, Mesh3DVertex* v1, Mesh3DVertex* v2,
	                                        Vec2i labels) override;

	// Sets a new reference vertex for the `hfc` as `v`. Updates the adjacency map by removing the
	// `hfc` from the previous vertex list (if not nullptr) and by updating the new `v` list.
	virtual void setHFCVertex(Mesh3DHalfCorner* hfc, Mesh3DVertex* v) override;

	// Clear the datastructure completely, releasing all used memory.
	virtual void clear() override;

	//----------- delete triangles
	// Deletes the input triangle and its 6 HCs, removing them from `mesh_triangles_list` and
	// `mesh_half_corners_list`, freeing memory, and redirecting pointers that were pointed at them.
	virtual void deleteTriangle(const Mesh3DTriangle* triangle) override;

	//----------- delete vertices
	// Erases input vertex from `mesh_vertices_list` and deletes it from memory, doesn't delete any
	// HCs or redirect pointers.
	virtual void deleteVertex(Mesh3DVertex* vertex) override;

	//----------- delete half-corners
	virtual void deleteHalfCorner(Mesh3DHalfCorner* hfc) override;

	//----------- renew internal datastructures, so they don't take as much space.
	virtual void defragmentMesh() override;

	//----------- integer indices for deterministic intersections

	// Clears the current `vertex_index_map`, and assigns to each mesh vertex a negative integer index
	// from scratch. Each mesh vertex is assigned an index upon creation, so it's generally not
	// necessary to call this function, unless there is a specific reason to reassign indices cleanly.
	// Using these indices in the SoS intersection routine as priority values (instead of vertex
	// memory locations) makes intersection results deterministic.
	virtual void assignVertexIndexMap() override;

	// Retrieves the integer index for the input `vertex`.
	virtual int getVertexIndex(Mesh3DVertex* vertex) const override;

	//----------- mesh test functions
	// Runs a number of critical and optional tests to determine the quality of the mesh:
	// -check if all vertices have a reference half-corner (optional)
	// -check if all materials are non-negative integers (optional)
	// -check if all triangles have two distinct material labels (critical)
	// -SKIPPED: check if all half-corners have an opposite assigned (critical), only for binary load
	// -check that mutually opposite half-corners are consistently pointing to each other (critical)
	// -check that mutually opposite half-corners are extending the same edge (critical)
	// -check if all opposites have the same material (critical)
	// -ADD: check if all mesh is inside the grid box (critical), only for `unit_cube` grid type
	// COMMENT
	// Return values:
	// 0: all tests passed.
	// 1: critial tests passed, at least one optional test failed.
	// 2: at least one critical test failed.
	virtual int runMeshConsistencyChecks() override;

	//----------- state cleaning between simulation runs
	// Clears datastructures with temporary data which is used during topofixer runs.
	// Does not change the triangles and connectivity.
	virtual void clearNonPersistentState() override;

	//----------- Make triangles 0-orientation have smaller label without changing handness.
	// This means that if someone external was looking at one fixed side of the triangle, the order of
	// the half-corners on this side won't change.
	virtual void orderLabelsOnManifoldPatches() const override;

	//--------------------------MESH INPUT/OUTPUT---------------------------------
	// Clears exixsting mesh, and reads the corner table in Mesh3DSaveState format from a binary file,
	// indices saved on elements (typed as pointers) are converted to pointers. This function does not
	// support adding to an already existing mesh. Currently always returns 0.
	// TODO: implement mesh consistency checking when loading from a binary file & possibility to load
	// vertex velocities.
	virtual int loadBinary(std::string_view) override;

	// Writes the corner table in the form of Mesh3DSaveState into a binary file (pointers are
	// converted to indices and saved on elements, typed as pointers).
	// TODO: output vertex velocities.
	virtual void writeInBin(const std::string& output_file = "mesh.bin") override;

	// Writes the mesh into an easiely readable text file for debugging. All of the mesh is stored,
	// including pointers, which are translated to indices in order to simplify navigation.
	// TODO: output vertex velocities.
	virtual void writeInText(const std::string& output_file = "mesh.txt") override;

	// Returns a snapshot of the mesh, i.e. the lists of vertices, triangles, and half-corners, saved
	// within an instance of Mesh3DSaveState. This requires the storage of the elements themselves,
	// and of index conversion maps, where a pointer to each element is associated with an index. In
	// order to maintain pointer consistency, pointers among the elements are remapped using the index
	// conversion maps. As such, within Mesh3DSaveState, every element is associated with an index,
	// which allows for reconstruction of the corner table in the pointer form.
	virtual Mesh3DSaveState getCurrentSaveState() override;

	// First, deletes all current data in the mesh corner table. Then allocates memory for the new
	// corner table, based on the elemets in the input `save_state`, and sets up inverse index
	// conversion maps, so that every index is associated with a pointer to an element. Element data
	// is then copied from `save_state` into the corner table, and pointers are restored using the
	// inverse index conversion maps - indices are used to retrieve pointers to the newly allocated
	// objects. Finally, returns a save state that contains the inverse index conversion maps
	// (mappings from indices of `save_state` to the pointers to newly created elements). This will be
	// used to reconstruct correct pointers to mesh elements saved on the grid in StateSaver class.
	virtual Mesh3DSaveState restoreFromSaveState(const Mesh3DSaveState& save_state) override;
	// Save as above but does not delete existing data.
	virtual Mesh3DSaveState appendFromSaveState(const Mesh3DSaveState& save_state) override;

	// Loads geometry specified in the three input vecotrs into our mesh data structure, then
	// determines and stores connectivity between elements via the use of half-corners. Each entry in
	// `triangle_vertices` represents a triangle by three integer indices of its vertices. Each entry
	// in `vertex_positions` represents a vertex by three double world coordinates. Vertex with index
	// K has its world position stored at `vertex_positions[K]`. Here we therefore index vertices from
	// 0 to `vertex_positions.size()-1`. Each entry in `vertex_velocities` represents the global
	// velocity of an input mesh vertex (K-th velocity vector is associated with the K-th vertex in
	// `vertex_positions`. Each entry in `material_labels` represents a material pair by two integer
	// labels. K-th material pair in `material_labels` is associated to the K-th triangle in
	// `triangle_vertices`.

	// Materials should be non-negative integers, otherwise unexpected behavior can occur. Two
	// materials in a pair must be distinct, and materials on neighboring triangles must match.
	// Vertices that are not part of triangles are generally not safe, and the algorithm's behavior in
	// their presence is not guaranteed. If a triangle is combinatorially degenerate (two of its
	// vertices have time same index), it is ignored. Likewise, material input corresponding (by
	// order) to a combinatorially degenerate triangle is ignored.

	// The `add_to_existing` optional paramter determines whether the newly loaded mesh data should be
	// added to the already existing mesh data stored in the corner table, or if the currently
	// existing mesh data should be cleared first. In case data is added, vertex indices are offset by
	// amount equal to the number of vertices currently in the corner table, so that the newly read
	// triangles are formed among the newly read vertices. Additionally, if data is added, the
	// optional parameter `offset_materials` determines whether newly loaded material labels should
	// likewise be offset by the largest material label currently saved on the corner table elements
	// (therefore making the newly loaded materials completely distinct from the already existing
	// ones), or not (in which case the newly loaded materials might be the same as the existing
	// ones).
	virtual int restoreFromGeometry(const std::vector<Vec3i>& triangle_vertices,
	                                const std::vector<Vec3d>& vertex_positions,
	                                const std::vector<VertexProperties>& vertex_properties,
	                                const std::vector<Vec2i>& material_labels,
	                                const int add_to_existing, const int offset_materials) override;

 private:
	//--------------------------EDGE COLLAPSE----------------------------------
	// This check requires that v1 and v2 are moved to a new position already.
	bool isCollapseGeometricallyValid(Mesh3DVertex* v1, Mesh3DVertex* v2,
	                                  const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_around_v1,
	                                  const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_around_v2,
	                                  Vec3d v1_coords, Vec3d v2_coords, Vec3d new_coords);

	bool isCollapseValidAroundVertex(Mesh3DVertex* v1, Mesh3DVertex* v2,
	                                 const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_around_v1,
	                                 const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_around_v2,
	                                 Vec3d new_coords);
	// Matches half-corners extending (v1, v3) after collapse of an (v1, v2) edge.
	// Uses existing connectivity in (v1, v2, v3) triangle to match new opposites and stores them in
	// the `opposite_map`. This can lead to inversions not being correctly handled but is useful for
	// short edges where inversion cannot happen. `extending_hfcs` have to be over (v1, v3)  for the
	// function to work correctly.
	void assignOppositesTopologically(
	    Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3,
	    const std::vector<Mesh3DHalfCorner*>& extending_hfcs,
	    absl::flat_hash_map<Mesh3DHalfCorner*, Mesh3DHalfCorner*>& opposite_map);

	// Finds holes around an edge `v1 - v2`, given half-corners adjacent to each vertex and
	// half-corners extending the `v1 - v2`. A hole is a pair of edges adjacent to v1 and v2 that
	// share a common vertex but do not have a common face. Returns a mapping from a common vertex to
	// a pair of edges.
	absl::flat_hash_map<Mesh3DVertex*, std::pair<Mesh3DHalfCorner*, Mesh3DHalfCorner*>>
	findHolesAroundEdge(const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_v1,
	                    const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_v2,
	                    const std::vector<Mesh3DHalfCorner*>& extending_hfcs);

	// Returns true if there is at least one hole around `v1 - v2`. Can be used for fast pruning of
	// invalid collapses.
	bool hasHolesAroundEdge(const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_v1,
	                        const absl::flat_hash_set<Mesh3DHalfCorner*>& hfcs_v2,
	                        const std::vector<Mesh3DHalfCorner*>& extending_hfcs);

	// Checks if existing configuration of holes can be collapsed.
	Mesh3DCornerTable::EdgeCollapseType checkHoppeCriterion(
	    const absl::flat_hash_map<Mesh3DVertex*, std::pair<Mesh3DHalfCorner*, Mesh3DHalfCorner*>>&
	        holes);

	int triangleNotFlip(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3, Vec3d new_coords);

	Mesh3DCornerTable::EdgeCollapseType getEdgeCollapseType(
	    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d new_coords,
	    const std::vector<Mesh3DHalfCorner*>& extending_hfcs,
	    const absl::flat_hash_map<Mesh3DVertex*, std::pair<Mesh3DHalfCorner*, Mesh3DHalfCorner*>>&
	        holes);

	bool checkOpposAroundEdge(Vec3d edgev1_coords, Vec3d edgev2_coords,
	                          const std::vector<Mesh3DHalfCorner*>& extending_hfcs);
	int sameSemiplane(Vec3d p1, Vec3d p2, Vec3d a, Vec3d b) const;
	void transferValuesEdgeCollapse(Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d v1_coords,
	                                Vec3d v2_coords, Vec3d new_coords) const;

	int restoreOppositesGeometrically(
	    const std::map<std::pair<int, int>, std::vector<Mesh3DHalfCorner*>>& extending_corners,
	    const std::vector<Mesh3DVertex*>& mesh_vertices_vec);

	int restoreOppositesByLabels(
	    const std::map<std::pair<int, int>, std::vector<Mesh3DHalfCorner*>>& extending_corners);

	// data members
	const TopoFixerSettings* settings;

	absl::flat_hash_set<Mesh3DTriangle*> mesh_triangles_list;
	absl::flat_hash_set<Mesh3DVertex*> mesh_vertices_list;
	absl::flat_hash_set<Mesh3DHalfCorner*> mesh_half_corners_list;
	absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DHalfCorner*>> vertex_to_hfc_map;

	// set of mesh triangles that are generated during surface reconstruction
	absl::flat_hash_set<Mesh3DTriangle*> mc_triangles;
	// set of mesh triangles that are generated during T1 resolution
	absl::flat_hash_set<Mesh3DTriangle*> t1_triangles;
	// set of hole-filling mesh triangles that are generated during T1 resolution
	absl::flat_hash_set<Mesh3DTriangle*> t1_hf_triangles;
	// mesh edges that are forbidden to be collapsed
	absl::flat_hash_set<SortedMeshEdge> no_collapse_edges;

	// stores an integer index for each mesh vertex (used as priority values in SoS intersections,
	// thus making intersection results deterministic)
	absl::flat_hash_map<Mesh3DVertex*, int> vertex_index_map;
	// stores the next integer index to be assigned to a mesh vertex (for SoS intersections); mesh
	// vertex indices start from -1 and are decresing
	int vertex_index_to_assign;

	// counters for different types of edge collapse cancels
	int t1_retraction_edge_collapse_cancel;
	int tetrahedron_edge_collapse_cancel;
	int in_plane_edge_collapse_cancel;
	int hoppe_criterion_edge_collapse_cancel;
	int double_four_valence_edge_collapse_cancel;
	int candidate_covering_edge_collapse_cancel;

	// If the edge is below this length, the geometric tests are not performed for it.
	const double kShortEdgeThreshold;
};