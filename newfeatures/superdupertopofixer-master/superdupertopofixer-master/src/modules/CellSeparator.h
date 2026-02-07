/* CellSeparator.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2021
 *
 * This is the header for the module that separates the triangles to be completely inside or
 * completely outside of the complex cell region.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <random>
#include <unordered_set>
#include <vector>

#include "../datastructures/Grid3DInterface.h"
#include "../datastructures/GridMeshIntersection.h"
#include "../datastructures/Mesh3DHalfCorner.h"
#include "../datastructures/Mesh3DSaveState.h"
#include "../datastructures/Mesh3DTriangle.h"
#include "../datastructures/Mesh3DVertex.h"
#include "../datastructures/TriangleSubdivision.h"
#include "../submodules/GridMeshIntersector.h"
#include "ModuleInterface.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
#include "../schemes/TopoFixerSettings.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class manages the flow of the cell separator module
class CellSeparator : public ModuleInterface {
 public:
	// constructors
	CellSeparator(const TopoFixerSettings& settings) : settings(&settings), random_gen_(random_dev_()){};
	virtual ~CellSeparator() = default;

	// functions
	virtual int run(Mesh3DInterface& mesh, Grid3DInterface& grid, GridMeshIntersector& intersector,
	                int orientation) override;

	std::vector<Mesh3DTriangle*> get_inside_triangles() {
		return std::vector<Mesh3DTriangle*>(inside_triangles_.begin(), inside_triangles_.end());
	};

	std::vector<Mesh3DTriangle*> get_outside_triangles() {
		return std::vector<Mesh3DTriangle*>(outside_triangles_.begin(), outside_triangles_.end());
	};

	absl::flat_hash_set<long long> getFailedSeparationFaces() const {
		return failed_separation_faces_;
	}

	void clearState();

 private:
	const TopoFixerSettings* settings;
	// Helper definition only used inside the class.
	using MeshEdge = std::pair<Mesh3DVertex*, Mesh3DVertex*>;

	struct TriangulationPoint {
		TriangulationPoint() = default;
		TriangulationPoint(Vec2d coords, long long element_id, bool is_internal)
		    : coords(coords), element_id(element_id), is_internal(is_internal){};
		// Barycentric coordinates of the point.
		Vec2d coords;
		// Corresponding element id in the grid. For internal points it is grid edge id, for boundary
		// points it is face id. If the point comes from the original triangle vertex, it is -1.
		long long element_id;
		// Indicates if the point comes from a grid edge.
		bool is_internal;
	};

	void addEdgesToGraphOnFace(Grid3DInterface& grid, Mesh3DInterface& mesh, Mesh3DVertex* v1,
	                           Mesh3DVertex* v2, long long face_id) const;

	// Puts all flood-fill reachable triangles starting from `start_triangles` that are not yet
	// labeled inside / outside into `flooded_triangles`.
	void floodTriangles(Mesh3DInterface& mesh,
	                    const absl::flat_hash_set<Mesh3DTriangle*>& start_triangles,
	                    bool is_start_inside, const absl::flat_hash_set<SortedMeshEdge>& graph_edges);

	// Returns triangle and if it is inside complex cell region for the first triple leaf that can be
	// consistently oriented.
	std::tuple<Mesh3DTriangle*, bool> orientTripleLeaves(
	    Grid3DInterface& grid, const std::vector<Mesh3DTriangle*>& triple_leaves,
	    const absl::flat_hash_map<Mesh3DVertex*, long long>& edge_vertex_to_grid_edge) const;

	// Determines if triangles not neighbouring any marked triangle are inside the
	// complex cell region. Returns the set of newly detected inside triangles.
	absl::flat_hash_set<Mesh3DTriangle*> markSeparateComponents(
	    Mesh3DInterface& mesh, Grid3DInterface& grid, const GridMeshIntersector& intersector,
	    const std::vector<long long>& complex_cells);

	void removeInternalMesh(Mesh3DInterface& mesh, Grid3DInterface& grid,
	                        const std::vector<long long>& complex_front_faces) const;

	// Returns a map that to each mesh triangle assigns a vector of `GridEdgeMeshFaceIntersection`s
	// that the triangle participates in. This is only done as reshuffilng of existing data, i.e. no
	// new intersections are caculated.
	absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>
	aggregateIntersectionsOnTriangles(Grid3DInterface& grid,
	                                  const std::vector<long long>& complex_front_faces) const;

	// Convert from a vector of subdivisions for each face to a map from MeshEdge to intersections.
	// Handles the orientation of the edge correctly. For each mesh edge the intersections are sorted
	// in increasing order of barycentric coordinates.
	absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>
	aggregateIntersectionsOnMeshEdges(Grid3DInterface& grid,
	                                  const std::vector<long long>& complex_front_faces) const;

	// Returns a set of triangles that will undergo a subdivision.
	absl::flat_hash_set<Mesh3DTriangle*> getSubdivisionTriangles(
	    Mesh3DInterface& mesh,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
	        face_intersections,
	    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
	        edge_to_intersections) const;

	// Computes triangulation points and segments from the intersection information.
	std::vector<CellSeparator::MeshEdge> extractTriangulationElements(
	    Grid3DInterface& grid, Mesh3DTriangle* triangle,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
	        face_intersections,
	    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
	        edge_to_intersections,
	    absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint>& vertex_to_tri_point) const;

	// Extracts subdivision segments and adds them to the grid, so they can be used for further
	// computations.
	void addSegmentsToFaceGraph(
	    Grid3DInterface& grid, Mesh3DInterface& mesh, Mesh3DTriangle* triangle,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
	        face_intersections,
	    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
	        edge_to_intersections) const;

	absl::flat_hash_map<SortedMeshEdge, std::vector<double>> spreadMeshEdgeIntersections(
	    absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
	        edge_to_intersections) const;

	void spreadMeshFaceIntersections(
	    Grid3DInterface& grid, Mesh3DTriangle* triangle,
	    absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint>& vertex_to_tri_point);

	Vec2d findSpreadDirection(Grid3DInterface& grid, const TriangulationPoint* first_inter,
	                          const TriangulationPoint* second_inter, Mesh3DTriangle* triangle,
	                          Vec3d tri_normal) const;

	void restoreOriginalIntersectionPositions(
	    absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
	        edge_to_intersections,
	    const absl::flat_hash_map<SortedMeshEdge, std::vector<double>>& edge_to_barys) const;

	// Perform subdivisions of given triangles in such a manner that two intersection points on edges
	// belonging to the same grid face are connected by a straight path.
	void subdivideTriangles(
	    Grid3DInterface& grid, Mesh3DInterface& mesh, const GridMeshIntersector& intersector,
	    const absl::flat_hash_set<Mesh3DTriangle*>& triangles,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
	        face_intersections,
	    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
	        edge_to_intersections);

	std::vector<std::vector<Mesh3DVertex*>> triangulateTri(
	    Grid3DInterface& grid, Mesh3DTriangle* triangle,
	    const absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint>& vertex_to_tri_point,
	    const std::vector<MeshEdge>& segments);

	absl::flat_hash_map<Mesh3DVertex*, int> assignIdxToVertices(
	    const absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint>& vertex_to_tri_point) const;

	std::vector<Vec2d> convertVerticesToIdx(
	    const absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint>& vertex_to_tri_point,
	    const absl::flat_hash_map<Mesh3DVertex*, int>& vertex_to_index) const;

	std::vector<Vec2i> convertSegmentsToIdx(
	    const std::vector<MeshEdge>& segments,
	    const absl::flat_hash_map<Mesh3DVertex*, int>& vertex_to_index) const;

	std::vector<Mesh3DVertex*> revertVertexMapping(
	    const absl::flat_hash_map<Mesh3DVertex*, int>& vertex_to_index) const;

	std::vector<std::vector<Mesh3DVertex*>> convertTriangleIdxToVertices(
	    const std::vector<Vec3i>& triangles_idx,
	    const std::vector<Mesh3DVertex*>& index_to_vertex) const;

	bool solveIntersection(const std::vector<Vec2i>& segments, const std::vector<Vec2d>& new_coords,
	                       const std::vector<Vec2i>& new_segments,
	                       std::vector<Vec3i>& triangles_idx) const;

	// Returns mapping from each subedges on a given triangle to their corresponding half-corners.
	// Specifically, for each edge of a triangle as defined by its vertices the subedges are found
	// with the help of the `edge_to_intersections` datastructure. For each subedge, the half-corner
	// for the original edge is take and recorded in the output. The order of the edges in the output
	// is important: the first vertex is oriented as the next half-corner and the second one as
	// previous half-corner.
	absl::flat_hash_map<MeshEdge, Mesh3DHalfCorner*> mapEdgeToOriginalHfc(
	    Mesh3DTriangle* triangle,
	    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
	        edge_to_intersections) const;

	// Returns allocated triangles as defined by `new_triangle_verts` inside the original `triangle`.
	// The halfcorners are also created and assigned appropriately with local neighbours without
	// opposites.
	std::vector<Mesh3DTriangle*> createMeshElements(
	    Mesh3DInterface& mesh, Mesh3DTriangle* triangle,
	    const std::vector<std::vector<Mesh3DVertex*>>& new_triangle_verts) const;

	// Assigns opposites for half-corners only if they share an edge. It is assumed that
	// `new_triangles` are the result of subdivision, thus, no non-manifold edges can be present.
	// If the half-corner does not have a matching pair, it is recorded into `all_edges_to_hfcs`.
	void connectInnerHalfcorners(
	    const std::vector<Mesh3DTriangle*>& new_triangles,
	    absl::flat_hash_map<MeshEdge, std::vector<Mesh3DHalfCorner*>>& all_edges_to_hfcs) const;
	// Assigns opposites based on the information about original triangle and how the half-corners
	// from `all_edges_to_hfcs` match with each other. In principle, it can match all new
	// half-corners, but the two functions are separated for performance reasons.
	void connectOuterHalfcorners(
	    const absl::flat_hash_map<Mesh3DTriangle*, Mesh3DTriangle*>& new_to_old_triangle,
	    const absl::flat_hash_map<MeshEdge, std::vector<Mesh3DHalfCorner*>>& all_edges_to_hfcs,
	    const absl::flat_hash_map<MeshEdge, absl::flat_hash_map<Mesh3DTriangle*, Mesh3DHalfCorner*>>&
	        edge_to_original_tri_hfc,
	    const absl::flat_hash_set<Mesh3DTriangle*>& subdivided_triangles) const;

	void assignInsidesOutsides(
	    Grid3DInterface& grid, const std::vector<Mesh3DTriangle*>& new_triangles,
	    Mesh3DTriangle* old_triangle,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
	        face_intersections,
	    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
	        edge_to_intersections,
	    const std::vector<MeshEdge>& segments);

	std::tuple<Mesh3DTriangle*, bool> markBoundaryTriangle(
	    Mesh3DTriangle* old_triangle,
	    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
	        edge_to_intersections,
	    const absl::flat_hash_map<SortedMeshEdge, std::vector<Mesh3DTriangle*>>& edge_to_tris) const;

	std::tuple<Mesh3DTriangle*, bool> markTripleLeaf(
	    Grid3DInterface& grid, const std::vector<Mesh3DTriangle*>& new_triangles,
	    Mesh3DTriangle* old_triangle,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
	        face_intersections) const;

	void floodLabelForNewTriangles(const std::vector<Mesh3DTriangle*>& new_triangles,
	                               Mesh3DTriangle* start_tri, bool is_inside,
	                               const std::vector<MeshEdge>& segments);

	// The function takes the id of a grid front face. Cell coordinates of the two grid cells adjacent
	// to such a face differ in exactly one component by exactly 1. The function returns true, if the
	// adjacent complex cell has the larger coordinate (i.e. is further in the increasing direction
	// along one of the coordinate axes).
	bool isComplexCellOnIncreasingSideOfFrontFace(Grid3DInterface& grid, long long face_id) const;

	// Retuns a cell that contains both faces. Returns -1 in faces don't share a cell.
	long long get_common_cell(Grid3DInterface& grid, long long first_face_id,
	                          long long second_face_id) const;

	// Returns 1 if the edge lies in the positive space of the grid face as defined by its normal
	// oriented in the positive direction of coordinates, 0 if the edge is in plane and -1 if the edge
	// is in the negative space.
	long long orient_grid_edge_against_grid_face(Grid3DInterface& grid, long long grid_edge_id,
	                                             long long grid_face_id) const;

	bool check_grid_graph(Grid3DInterface& grid) const;

	// TODO: this has to be factored out of here.
	static std::vector<long long> intersect_vectors(const std::vector<long long>& v1,
	                                                const std::vector<long long>& v2);

	bool markBadFaceGraph(Grid3DInterface& grid);

	// Moves barycentric coordinates further away from edges if they are close to it.
	Vec3d moveAwayFromTriEdge(Vec3d bary) const;
	// Same as above but the 3rd coordinate is implicit.
	Vec2d moveAwayFromTriEdge(Vec2d bary) const;

	// Returns the coordinates of a `point` projection to a triangle with a unnormalized `tri_normal`.
	Vec2d projectOnTriangle(Vec3d point, Mesh3DTriangle* triangle, Vec3d tri_normal) const;

	// Converts barycentric triangle coordinates into 2D coordinates where the first triangle vertex
	// is at (0, 0), the second one is at (1, 0) and the third one at (0, 1).
	Vec2d extractIndependentCoords(Vec3d bary) const;

	//----------- functions that aggregate mesh and grid data

	// Adds the input `intersection` to the input map `mesh_edge_to_intersection`, correctly sets its
	// `is_first_inside` and `is_second_inside` flags, so that they store which mesh vertex is inside
	// the complex region, and which is outside of it, and makes sure that the vertex saved as `first`
	// inside `intersection` has a lower pointer value than `second`. In order to make the assignement
	// of inside flags meaningful, it only makes sense to pass to this function an intersection taking
	// place on a front face.
	void addIntersectionToMeshEdge(
	    Grid3DInterface& grid, const GridFaceMeshEdgeIntersection& intersection,
	    absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
	        mesh_edge_to_intersections) const;

	absl::flat_hash_set<SortedMeshEdge> getGraphEdges(
	    Grid3DInterface& grid, const std::vector<long long>& front_faces) const;

	//----------- data members

	// Faces that the algorithm was not able to separate during execution.
	absl::flat_hash_set<long long> failed_separation_faces_;

	// TODO: think about how to actually make it pretty.
	const double kSnappingTolerance = 1e-7;

	// sets that partition mesh triangles into those that are completely inside the remeshed region,
	// and those that are completely outside of it
	absl::flat_hash_set<Mesh3DTriangle*> inside_triangles_;
	absl::flat_hash_set<Mesh3DTriangle*> outside_triangles_;

	// Used to resolve extreme degeneracies in cases where the exact positions of intersections do not
	// matter.
	std::random_device random_dev_;
	std::mt19937 random_gen_;
};
