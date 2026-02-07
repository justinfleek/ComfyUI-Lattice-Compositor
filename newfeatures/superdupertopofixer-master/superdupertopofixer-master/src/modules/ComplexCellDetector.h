/* ComplexCellDetector.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the header for the module that detects complex cells.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "ModuleInterface.h"
#include "../schemes/TopoFixerSettings.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class manages the flow of the complex cell detection code
class ComplexCellDetector : public ModuleInterface {
 public:
	// constructors
	ComplexCellDetector(const TopoFixerSettings& settings) : settings(&settings){};
	virtual ~ComplexCellDetector() = default;

	// functions
	virtual int run(Mesh3DInterface& mesh, Grid3DInterface& grid, GridMeshIntersector& intersector,
	                int orientation) override;

	absl::flat_hash_map<long long, std::vector<std::pair<Vec3d, Vec3d>>>* getAllFaceGraphs() {
		return &all_face_graphs;
	}

 private:
	const TopoFixerSettings* settings;
	// Functions that traverse elements of the grid and mark topologically/geometrically complex ones.
	// These functions sacrifice sparcity for the ease of use by marking all elements, even the ones
	// that are not initially stored on the grid.
	void markComplexVertices(Grid3DInterface& grid, const int orientation) const;
	void markComplexEdges(Mesh3DInterface& mesh, Grid3DInterface& grid);
	void markComplexFaces(Mesh3DInterface& mesh, Grid3DInterface& grid,
	                      GridMeshIntersector& intersector);

	// Predicates to check if a given element is topologically/geometrically complex.
	// A vertex is complex, when its material is is ambigious.
	bool isVertexComplex(Grid3DInterface& grid, const long long vertex_id) const;
	// If `material_vector` is unique (i.e. has one 1 and all other 0s), returns the index
	// corresponding to the unique material entry. This configuration implies to a physically valid
	// state. If `material_vector` is not unique, returns -1.
	int findMaterialVectorUniqueEntry(const SparseVector<int>& material_vector) const;
	// An edge is topologically complex, when at least one of the following holds:
	// -it is intersected by two or more mesh triangles,
	// -it has previously been labeled complex.
	// The second case can happen when an edge has first been labeled topologically complex in
	// function `markComplexEdges`, and later function `propagateComplexCellFront` inquires again
	// about its complexity. Alternatively, some edges might be labeled complex as a consequence of
	// being adjacent to problematic regions that trigger a rollback (in practice there is currently
	// no functionality that would cause this to occur).
	bool isEdgeTopologicallyComplex(Grid3DInterface& grid, const long long edge_id) const;
	// An edge is geometrically complex, based on the "edge_geometric_complexity_metric" parameter:
	// -"none": topological complexity determines geometric complexity
	// -"inversion": checks whether a non-physical state is entered while traversing the input edge
	// (material vector becomes non-unique at any time)
	bool isEdgeGeometricallyComplex(Mesh3DInterface& mesh, Grid3DInterface& grid,
	                                const long long edge_id);
	// Traverses the input grid edge, after each intersection with a mesh triangle tests the material
	// vector for uniqueness. If the material vector ever enters a non-unique state, returns true.
	// Otherwise returns false.
	bool isMaterialFlippedAlongEdge(Mesh3DInterface& mesh, Grid3DInterface& grid,
	                                const long long edge_id);
	// Iterates over topologically complex, geometrically non-complex edges, and performs the deep
	// edge test. An edge is deep, if there exists at least one material encountered while traversing
	// the edge (we know them to be unique at every point), that is not present as the unique label on
	// vertices in the l1 neighborhood of the edge (size of this neighborhood is determined by the
	// parameter "edge_deep_cell_test_depth"). If an edge is determined to be deep, all its adjacent
	// cells are labeled as fixed-complex (must be remeshed). If the edge is not deep (i.e. it is
	// shallow), and all its adjacent cells are flexible-complex, we unmark them from being
	// flexible-complex, thus excluding them from being remeshed.
	void deepEdgeTest(Grid3DInterface& grid);
	// A face is topologically complex, when its face graph contains a cycle, or if it has been
	// labeled complex earlier. The second case can happen when a face has first been labeled
	// topologically complex in function `markComplexFaces`, and later function
	// `propagateComplexCellFront` inquires again about its complexity. Alternatively, some faces
	// might be labeled complex as a consequence of being adjacent to problematic regions that trigger
	// a rollback. The function can return:
	// -0: if the face is determined to not be topologically complex
	// -1: if the face is determined to be topologically complex
	// -2: if an inconsistency was determined during the topological complexity test
	int isFaceTopologicallyComplex(Mesh3DInterface& mesh, Grid3DInterface& grid,
	                               GridMeshIntersector& intersector, long long face_id);
	// A face is geometrically complex, based on the "face_geometric_complexity_metric" parameter:
	// -"none": topological complexity determines geometric complexity
	bool isFaceGeometricallyComplex(const long long edge_id) const;

	// Iteratively enlarge the complex cell region until all edges and cells on its boundary are
	// topologically simple. The motivation to do this is that we have to be able to connect the mesh
	// generated by marching cubes to the part of the mesh that doesn't get remeshed, and we only have
	// a recipe for connecting topologically simple elements.
	void propagateComplexCellFront(Mesh3DInterface& mesh, Grid3DInterface& grid,
	                               GridMeshIntersector& intersector);

	// ----------------- data members

	// map of all face graphs, in which an integer (face id) maps to a set of edges (pairs of mesh
	// vertices) constituting its face graph
	absl::flat_hash_map<long long, std::vector<std::pair<Vec3d, Vec3d>>> all_face_graphs;

	absl::flat_hash_map<long long, absl::flat_hash_set<int>> separating_materials;
	absl::flat_hash_map<long long, absl::flat_hash_set<int>> nearby_grid_materials;
};
