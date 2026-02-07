/* GridMeshIntersector.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, 2021
 *
 * This is the header for submodule performing intersection between mesh and grid.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <iostream>
#include <unordered_map>
#include <vector>

#include "../datastructures/Grid3DInterface.h"
#include "../datastructures/GridMeshIntersection.h"
#include "../datastructures/Mesh3DInterface.h"
#include "../datastructures/Mesh3DTriangle.h"
#include "../datastructures/Mesh3DVertex.h"
#include "../schemes/TopoFixerSettings.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------
class GridMeshIntersector {
 public:
	/////////////////
	// constructors
	GridMeshIntersector(const TopoFixerSettings& settings) : settings_(&settings){};
	virtual ~GridMeshIntersector() = default;

	/////////////////
	// Intersection operations
	/////////////////

	// Finds intersections of all edges of the given `grid` with all triangles of the given `mesh`. If
	// `triangle_bounding_cells` are passed, then only these cells will used to determine the
	// intersections. Otherwise, mesh triangle bounding tests are performed first, and the calculated
	// data is used to determine which grid cells to test for intersections. Returns intersections
	// grouped into `GridLattice`s by grid orientation. An orientation corresponds to an increasing
	// coordinate axis direction, and can therefore take values from {0,1,2}. Value of orientation can
	// be used to index into the returned vector to get the lattice for the corresponding orientation,
	// e.g. zero-th element of returned vector corresponds to orientation 0.
	std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>> intersectMeshWithGridEdges(
	    const Grid3DInterface& grid, const Mesh3DInterface& mesh) const;
	std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>> intersectMeshWithGridEdges(
	    const Grid3DInterface& grid, const Mesh3DInterface& mesh,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>& triangle_bounding_cells)
	    const;
	std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>> intersectMeshWithGridEdges(
	    const Grid3DInterface& grid, const Mesh3DInterface& mesh,
	    const std::vector<std::pair<Mesh3DTriangle*, std::pair<Vec3ll, Vec3ll>>>&
	        triangle_bounding_ranges) const;

	// Tries to intersect a grid edge with triangle mesh. Appends successful intersections to the end
	// of the vector.
	virtual void intersect_grid_edge_with_mesh_triangle(
	    const Grid3DInterface& grid, const long long edge_id, const Mesh3DInterface& mesh,
	    Mesh3DTriangle* triangle, std::vector<GridEdgeMeshFaceIntersection>& intersections) const = 0;

	// Computes intersection between grid face, defined by its two face triangles, and two mesh
	// vertices. Returns 0, if there's no intersection and 1 if there's one. In case of successful
	// intersection, updates `intersection` vector to contain coordinates of intersection
	// and `bary_coord` to contain position along the v1-v2 segment where the intersection happens,
	// so that intersection = (1 - bary_coord) * v1 + bary_coord * v2.
	virtual int intersect_mesh_edge_with_grid_face_triangles(
	    const Grid3DInterface& grid, const std::vector<Vec3ll>& face_triangles,
	    const Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d& intersection,
	    double& bary_coord) const = 0;

	virtual int intersect_mesh_edge_with_grid_face_triangles_int_priorities(
	    const Grid3DInterface& grid, const std::vector<Vec3ll>& face_triangles,
	    const Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d& intersection,
	    double& bary_coord) const = 0;

	/////////////////
	// triangle bounding tests
	/////////////////

	// Returns a grid cell id where a given mesh `vertex` is located.
	virtual long long find_cell_id_for_mesh_vertex(const Grid3DInterface& grid,
	                                               const Mesh3DInterface& mesh,
	                                               Mesh3DVertex* vertex) const = 0;

	// Finds and returns all `grid` cells that form an axis-aligned bounding box around the input mesh
	// `triangle` + offset, i.e. the axis-aligned block of all grid cells potentially intersected by
	// `triangle` (the bounding box can include cells that do not intersect `triangle`). When testing
	// for mesh vertex - grid cell intersection, offsets (o,o,o) and (-o,-o,-o) are added to vertex
	// positions in order for the test to be more robust and rather include a larger portion of cells
	// than what would be strictly necessary. It is enough to test with the listed offsets (as opposed
	// to all combinations of + and - components), resulting axis-aligned bounding box doesn't change.
	std::vector<long long> findBoundingCellsForTriangle(const Grid3DInterface& grid,
	                                                    const Mesh3DInterface& mesh,
	                                                    Mesh3DTriangle* triangle) const;

	// For each mesh triangle performs the bounding test, that is, finds the block of axis-aligned
	// grid cells potentially intersected by it, and returns this data as a map.
	absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>> findBoundingCellsForAllTriangles(
	    const Grid3DInterface& grid, const Mesh3DInterface& mesh) const;

	// Returns minimum and maximum grid cell coordinates of a bounding box around a given mesh
	// `triangle`. The bounding box can include cells that do not intersect with a triangle at all.
	std::pair<Vec3ll, Vec3ll> findBoundingRangeForTriangle(const Grid3DInterface& grid,
	                                                       const Mesh3DInterface& mesh,
	                                                       Mesh3DTriangle* triangle) const;

	// A convenience function that computes bounding box for each triangle in a mesh separately.
	std::vector<std::pair<Mesh3DTriangle*, std::pair<Vec3ll, Vec3ll>>>
	findBoundingRangesForAllTriangles(const Grid3DInterface& grid, const Mesh3DInterface& mesh) const;

	/////////////////
	// Orientation tests
	/////////////////

	// Returns a positive value if the grid vertex with `grid_id` is located in the positive
	// semi-plane, a negative value if it's in the negative semi-plane and zero if it lies on the
	// plane. No assumptions should be made about the magnitude of the value.
	virtual double orient_grid_vertex_against_mesh_triangle(const Grid3DInterface& grid,
	                                                        const long long vert_id,
	                                                        const Mesh3DInterface& mesh,
	                                                        Mesh3DTriangle* triangle) const = 0;
	// Same as above but for mesh vertex and grid triangle.
	virtual double orient_mesh_vertex_against_grid_face_triangle(const Grid3DInterface& grid,
	                                                             const Vec3ll vertices,
	                                                             const Mesh3DInterface& mesh,
	                                                             Mesh3DVertex* vertex) const = 0;

	/////////////////
	// Degenerate case detection
	/////////////////

	// Returns elements of `grid` and `mesh` that lie dangerously close together. Specifically,
	// considers mesh vertices and edges, grid vertices and edges and intersections of grid edges with
	// triangles. If `triangle_bounding_cells` are passed, then only these bounding cells will used to
	// determine grid egde intersections.
	virtual std::vector<GridMeshDegeneracy> find_intersection_degeneracies(
	    const Grid3DInterface& grid, const Mesh3DInterface& mesh) const = 0;
	virtual std::vector<GridMeshDegeneracy> find_intersection_degeneracies(
	    const Grid3DInterface& grid, const Mesh3DInterface& mesh,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>& triangle_bounding_cells)
	    const = 0;

	const TopoFixerSettings* settings() const { return settings_; }

 private:
	const TopoFixerSettings* settings_;
	std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>> buildLattices(
	    const Grid3DInterface& grid,
	    const std::vector<GridEdgeMeshFaceIntersection>& intersections) const;
};

class GridMeshIntersectorNaive : public GridMeshIntersector {
 public:
	/////////////////
	// constructors

	GridMeshIntersectorNaive(const TopoFixerSettings& settings, double tolerance = 1.e-10);
	virtual ~GridMeshIntersectorNaive() = default;

	/////////////////
	// Intersection operations
	// See parent class for general comments and definitions.
	/////////////////

	virtual void intersect_grid_edge_with_mesh_triangle(
	    const Grid3DInterface& grid, const long long edge_id, const Mesh3DInterface& mesh,
	    Mesh3DTriangle* triangle,
	    std::vector<GridEdgeMeshFaceIntersection>& intersections) const override;

	virtual int intersect_mesh_edge_with_grid_face_triangles(
	    const Grid3DInterface& grid, const std::vector<Vec3ll>& face_triangles,
	    const Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d& intersection,
	    double& bary_coord) const override;

	virtual int intersect_mesh_edge_with_grid_face_triangles_int_priorities(
	    const Grid3DInterface& grid, const std::vector<Vec3ll>& face_triangles,
	    const Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d& intersection,
	    double& bary_coord) const override;

	/////////////////
	// Bounding boxes
	// See parent class for general comments and definitions.
	/////////////////

	virtual long long find_cell_id_for_mesh_vertex(const Grid3DInterface& grid,
	                                               const Mesh3DInterface& mesh,
	                                               Mesh3DVertex* vertex) const override;

	/////////////////
	// Orientation tests
	// See parent class for general comments and definitions.
	/////////////////

	virtual double orient_grid_vertex_against_mesh_triangle(const Grid3DInterface& grid,
	                                                        const long long vert_id,
	                                                        const Mesh3DInterface& mesh,
	                                                        Mesh3DTriangle* triangle) const override;
	virtual double orient_mesh_vertex_against_grid_face_triangle(const Grid3DInterface& grid,
	                                                             const Vec3ll vertices,
	                                                             const Mesh3DInterface& mesh,
	                                                             Mesh3DVertex* vertex) const override;

	/////////////////
	// Degenerate case detection
	// See parent class for general comments and definitions.
	/////////////////
	virtual std::vector<GridMeshDegeneracy> find_intersection_degeneracies(
	    const Grid3DInterface& grid, const Mesh3DInterface& mesh) const override;
	virtual std::vector<GridMeshDegeneracy> find_intersection_degeneracies(
	    const Grid3DInterface& grid, const Mesh3DInterface& mesh,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>& triangle_bounding_cells)
	    const override;

 private:
	/////////////////
	// Helper functions for degeneracy detection.
	/////////////////

	// Decide if the intersection trilinear coordinates correspond to the degenerate case. If it is
	// degeneracy, fill in the information about it in `degen_info` template and add it to the vector
	// of `degeneracies`.
	void extract_degeneracies_from_trilinear(const Vec3d& trilinear,
	                                         const std::vector<Mesh3DVertex*>& verts,
	                                         const GridMeshDegeneracy& degen_info,
	                                         std::vector<GridMeshDegeneracy>& degeneracies) const;
	void add_two_close_intersections_degeneracies(
	    std::vector<GridMeshDegeneracy>& result, const Grid3DInterface& grid,
	    const Mesh3DInterface& mesh,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>&
	        triangle_cell_intersections) const;
	Vec3d from_barycentric_to_trilinear(const Vec3d bary, const Mesh3DInterface& mesh,
	                                    Mesh3DTriangle* triangle) const;

	// Gets approximation of distance to the plane.
	double get_distance_to_triangle_plane(const Vec3d coords, const Mesh3DInterface& mesh,
	                                      Mesh3DTriangle* triangle) const;
	Vec3d project_on_triangle_plane(const Vec3d coords, const Mesh3DInterface& mesh,
	                                Mesh3DTriangle* triangle) const;

	bool is_inside_triangle(const Vec3d coords, const Mesh3DInterface& mesh,
	                        Mesh3DTriangle* triangle) const;
	Vec3d get_trilinear_coords(const Vec3d coords, const Mesh3DInterface& mesh,
	                           Mesh3DTriangle* triangle) const;
	Vec3d get_barycentric_coords(const Vec3d coords, const Mesh3DInterface& mesh,
	                             Mesh3DTriangle* triangle) const;

	Vec3d intersect_edge_with_triangle_plane(const Grid3DInterface& grid, const long long edge_id,
	                                         const Mesh3DInterface& mesh, Mesh3DTriangle* triangle,
	                                         double& step, bool& is_normal_aligned) const;
	double tolerance_;
};

// Intersector that uses Simulation of Simplicity predicates.
// The main idea is that each predicate is written in a such a way to make it look like intersecting
// elements are in general position. Ties are broken with the help of element indices.
// Based on Edelbrunner & Mücke's "Simulation of simplicity: a technique to cope with degenerate
// cases in geometric algorithms".
class GridMeshSoSIntersector : public GridMeshIntersector {
 public:
	GridMeshSoSIntersector(const TopoFixerSettings& settings) : GridMeshIntersector(settings) {}
	virtual ~GridMeshSoSIntersector() = default;

	/////////////////
	// Intersection operations
	// See parent class for general comments and definitions.
	/////////////////

	virtual void intersect_grid_edge_with_mesh_triangle(
	    const Grid3DInterface& grid, const long long edge_id, const Mesh3DInterface& mesh,
	    Mesh3DTriangle* triangle,
	    std::vector<GridEdgeMeshFaceIntersection>& intersections) const override;

	virtual int intersect_mesh_edge_with_grid_face_triangles(
	    const Grid3DInterface& grid, const std::vector<Vec3ll>& face_triangles,
	    const Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d& intersection,
	    double& bary_coord) const override;

	virtual int intersect_mesh_edge_with_grid_face_triangles_int_priorities(
	    const Grid3DInterface& grid, const std::vector<Vec3ll>& face_triangles,
	    const Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d& intersection,
	    double& bary_coord) const override;

	/////////////////
	// Bounding boxes
	// See parent class for general comments and definitions.
	/////////////////

	virtual long long find_cell_id_for_mesh_vertex(const Grid3DInterface& grid,
	                                               const Mesh3DInterface& mesh,
	                                               Mesh3DVertex* vertex) const override;

	/////////////////
	// Orientation tests
	// See parent class for general comments and definitions.
	/////////////////

	virtual double orient_grid_vertex_against_mesh_triangle(const Grid3DInterface& grid,
	                                                        const long long vert_id,
	                                                        const Mesh3DInterface& mesh,
	                                                        Mesh3DTriangle* triangle) const override;
	virtual double orient_mesh_vertex_against_grid_face_triangle(const Grid3DInterface& grid,
	                                                             const Vec3ll vertices,
	                                                             const Mesh3DInterface& mesh,
	                                                             Mesh3DVertex* vertex) const override;

	/////////////////
	// Degenerate case detection
	// See parent class for general comments and definitions.
	// TODO: Implement.
	/////////////////
	virtual std::vector<GridMeshDegeneracy> find_intersection_degeneracies(
	    const Grid3DInterface& grid, const Mesh3DInterface& mesh) const override {
		return {};
	};
	virtual std::vector<GridMeshDegeneracy> find_intersection_degeneracies(
	    const Grid3DInterface& grid, const Mesh3DInterface& mesh,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>& triangle_bounding_cells)
	    const override {
		return {};
	};

 private:
	// Normalizes barycentric coordinates such that no coordinate is exactly 1.0. This is useful for
	// intersections points that are known to lie inside the triangle but can be in degenerate
	// configurations. Assumes that no coordinate is exactly zero (which is satified for returns of
	// SoS functions).
	Vec3d normalizeBaryCoords(Vec3d bary) const;
};