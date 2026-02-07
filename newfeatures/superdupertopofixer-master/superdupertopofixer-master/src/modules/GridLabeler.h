/* GridLabeler.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the header for the module that labels the vertices of the grid in a sparse way.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <set>

#include "../datastructures/Grid3DInterface.h"
#include "../datastructures/GridMeshIntersection.h"
#include "../utilities/SparseVector.h"
#include "../utilities/vec.h"
#include "ModuleInterface.h"
#include "../schemes/TopoFixerSettings.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// This class manages the flow of the grid labeler module.
class GridLabeler : public ModuleInterface {
 public:
	// constructors
	GridLabeler(const TopoFixerSettings& settings) : settings(&settings){};
	virtual ~GridLabeler() = default;

	// Function that coordinates the run of the grid labeler module.
	virtual int run(Mesh3DInterface& mesh, Grid3DInterface& grid, GridMeshIntersector& intersector,
	                int orientation) override;

	// Returns the data structure holding grid vertex material vectors for each grid orientation that
	// were computed in the most recent execution of `run` function. Used only for visualization
	// purposes. After being computed, material vectors are stored on the grid and further processed
	// and transformed into unique labels in the algorithm pipeline. As such, material data for
	// computation should only ever be pulled from the grid, and not from the grid labeler!
	std::vector<absl::flat_hash_map<long long, SparseVector<int>>> getLabelsPerOrientation() const;

 private:
	const TopoFixerSettings* settings;

	// Save for each grid cell pointers to all mesh triangles that potentially intersect it, using a
	// map that to each mesh triangle assigns grid cells that the triangle potentially intersects.
	void registerTriangles(
	    Grid3DInterface& grid, const Mesh3DInterface& mesh,
	    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>& per_triangle_cells) const;

	// Same as above but uses bounding box ranges defined by the minimum and maximum grid cell
	// coordinates.
	void registerTriangles(Grid3DInterface& grid, const Mesh3DInterface& mesh,
	                       const std::vector<std::pair<Mesh3DTriangle*, std::pair<Vec3ll, Vec3ll>>>&
	                           per_triangle_cells) const;

	// Main grid labeling function. Iterates over sparse rays, for each ray, when an intersection is
	// encountered, updates the material vector. When a vertex that is stored in the vertex lattice is
	// encountered, saves on it the current version of the material vector. NUMERICS: comparison of
	// doubles using "<" may be inconsistent with SoS.
	// Returns true if all vertices were labeled successfully and places the results in `labels`.
	int labelGridVertices(
	    Grid3DInterface& grid,
	    const GridLattice<GridEdgeMeshFaceIntersection, long long>& intersection_lattice,
	    const GridLattice<long long, long long>& grid_vertex_lattice, int num_materials,
	    absl::flat_hash_map<long long, SparseVector<int>>& vertex_labels) const;

	// Updates `material_vector` as an `intersection` is encountered along a grid ray that points
	// along `direction`.
	// NUMERICS: performs a scalar product to determine the relative position of two vectors
	void updateMaterialVector(Grid3DInterface& grid, const GridEdgeMeshFaceIntersection& intersection,
	                          SparseVector<int>& material_vector) const;

	// Save each grid edge-mesh triangle intersection on its grid edge.
	void registerGridEdgeIntersections(
	    Grid3DInterface& grid,
	    const GridLattice<GridEdgeMeshFaceIntersection, long long>& intersection_lattice) const;

	// Get indices of vertices that have inconsistent labels that change depending on the orientation.
	absl::flat_hash_set<long long> getInconsistentVertices(
	    std::vector<absl::flat_hash_map<long long, SparseVector<int>>>& labels_per_orentation) const;

	// Changes the material for inconsistent vertices to be a single consistent one.
	void relabelInconsistentVertices(
	    std::vector<absl::flat_hash_map<long long, SparseVector<int>>>& labels_per_orentation,
	    const absl::flat_hash_set<long long>& inconsistent_vertices) const;

	// Marks cells adjacent to the inconsistent vertices as fixed complex.
	void markCellsWithInconsistentVertices(
	    Grid3DInterface& grid, const absl::flat_hash_set<long long>& inconsistent_vertices) const;

	// ----------------- data members

	// Stores the most recently calculated grid vertex material vectors, namely for each grid
	// orientation saves the map that assigns to a grid vertex id its material vector. After material
	// vector computation is finished, material vectors are transfered onto the grid for further
	// processing in the algorithm pipeline. This data structure is kept strictly only for
	// visualization of labeling, and mustn't be used to retrieve vertex material vectors, as these
	// might change during the course of the algorithm's run.
	std::vector<absl::flat_hash_map<long long, SparseVector<int>>> vertex_labels_per_orient_;
};
