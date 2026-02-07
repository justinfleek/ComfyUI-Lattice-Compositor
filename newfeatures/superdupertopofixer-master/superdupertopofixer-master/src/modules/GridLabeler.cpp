/* GridLabeler.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the implementation file for the module that labels the vertices of the grid.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "GridLabeler.h"

#include <unordered_map>
#include <unordered_set>

#include "../datastructures/GridMeshIntersection.h"
#include "../submodules/GridMeshIntersector.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// function that coordinates the run of the grid labeler module
int GridLabeler::run(Mesh3DInterface& mesh, Grid3DInterface& grid, GridMeshIntersector& intersector,
                     int orientation) {
	int return_value = 0;

	// for all mesh triangles, find all grid cells they potentially intersect
	std::vector<std::pair<Mesh3DTriangle*, std::pair<Vec3ll, Vec3ll>>> cell_intersections =
	    intersector.findBoundingRangesForAllTriangles(grid, mesh);

	// save for each grid cell pointers to all triangles that potentially intersect it
	registerTriangles(grid, mesh, cell_intersections);

	// detect intersections of mesh triangles with sparse grid edges, save in a separate grid lattice
	// for each grid orientation
	std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>> intersection_lattices =
	    intersector.intersectMeshWithGridEdges(grid, mesh, cell_intersections);

	// save each grid edge-mesh triangle intersection on its grid edge
	for (const auto& lattice : intersection_lattices) {
		registerGridEdgeIntersections(grid, lattice);
	}

	// compute grid vertex material vectors in a sparse way, separately for each grid orientation;
	// orientations correspond to positive cartesian coordinate directions, as defined by the
	// structure of the grid; we only consider positive grid orientations, because traversing grid
	// edge-mesh triangle intersections along a grid ray in either direction is bound to produce the
	// same result, as long as the input mesh is valid
	int num_orientations = 3;
	vertex_labels_per_orient_.resize(num_orientations);
	for (int orient = 0; orient < num_orientations; ++orient) {
		// construct a sparse vertex lattice in the current orientation direction
		const GridLattice<long long, long long>& sparse_rays = grid.getSparseRays(orient);
		// perform grid labeling in the current orientation direction, save the result in
		// `vertex_labels_per_orient_`
		absl::flat_hash_map<long long, SparseVector<int>> labels;
		int ok = labelGridVertices(grid, intersection_lattices[orient], sparse_rays,
		                           mesh.getNumberLabels(), vertex_labels_per_orient_[orient]);
		if (!ok) {
			return_value = 1;
			if (settings->verbosity >= 1) {
				std::cout << "-grid labeler finished with return value " << return_value << std::endl;
				std::cout << "============================================================================="
				             "========"
				          << std::endl;
			}
			return return_value;
		}
	}

	// Cells are relabeled and marked complex here because inconsistent vertices do not have breaking
	// points that make vertex complex.
	absl::flat_hash_set<long long> inconsistent_vertices =
	    getInconsistentVertices(vertex_labels_per_orient_);
	relabelInconsistentVertices(vertex_labels_per_orient_, inconsistent_vertices);
	markCellsWithInconsistentVertices(grid, inconsistent_vertices);
	grid.setVertexMaterialVectors(vertex_labels_per_orient_[orientation]);
	grid.constructMaterialDecoder();

	if (settings->verbosity >= 1) {
		std::cout << "-grid labeler finished with return value " << return_value << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return return_value;
}

// save for each grid cell pointers to all triangles that potentially intersect it
void GridLabeler::registerTriangles(
    Grid3DInterface& grid, const Mesh3DInterface& mesh,
    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>& per_triangle_cells) const {
	for (const auto& cell_it : per_triangle_cells) {
		Mesh3DTriangle* triangle = cell_it.first;
		const std::vector<long long>& cell_ids = cell_it.second;
		for (const long long cell_id : cell_ids) {
			grid.addTriangleToCellWithoutFlaggingRays(cell_id, triangle);
		}
	}

	// flag the sparse rays lattice as not updated, i.e. it should be rebuilt before use; this is
	// because previously empty (and thus ignored) cells might now contain triangles, and therefore
	// their vertices should be included in the sparse rays lattice
	grid.setRaysUpdatedValue(false);
}

void GridLabeler::registerTriangles(
    Grid3DInterface& grid, const Mesh3DInterface& mesh,
    const std::vector<std::pair<Mesh3DTriangle*, std::pair<Vec3ll, Vec3ll>>>& per_triangle_cells)
    const {
	for (const auto& [triangle, cell_range] : per_triangle_cells) {
		// There are more edges than cells, except in the direction of orientation.
		auto [min_coords, max_coords] = cell_range;
		for (long long i = min_coords[0]; i <= max_coords[0]; ++i) {
			for (long long j = min_coords[1]; j <= max_coords[1]; ++j) {
				for (long long k = min_coords[2]; k <= max_coords[2]; ++k) {
					long long cell_id = grid.get_cell_id(i, j, k);
					grid.addTriangleToCellWithoutFlaggingRays(cell_id, triangle);
				}
			}
		}
	}
	grid.setRaysUpdatedValue(false);
}

// returns the data structure holding grid vertex material vectors for each grid orientation
std::vector<absl::flat_hash_map<long long, SparseVector<int>>>
GridLabeler::getLabelsPerOrientation() const {
	return vertex_labels_per_orient_;
}

// for each sparse ray, process intersections on it, update the material vector, and store it on
// sparse grid vertices
int GridLabeler::labelGridVertices(
    Grid3DInterface& grid,
    const GridLattice<GridEdgeMeshFaceIntersection, long long>& intersection_lattice,
    const GridLattice<long long, long long>& grid_vertex_lattice, int num_materials,
    absl::flat_hash_map<long long, SparseVector<int>>& vertex_labels) const {
	// ASSERT: check that `intersection_lattice` and `grid_vertex_lattice` use the same grid
	// orientation
	assert(intersection_lattice.get_ray_direction() == grid_vertex_lattice.get_ray_direction());

	// iterate over the map of sparse rays; assigns to a pair of coordinates that identify a ray, a
	// vector of pairs {value,coordinate-on-ray}
	for (const auto& grid_ray : grid_vertex_lattice) {
		// material vector, reserves as many slots as there are materials
		// NOTE: this could be made sparse, especially for a big bubble cluster
		SparseVector<int> material_vector;
		// initialize the start of each ray to unique global outside, i.e. (1,0,0,....)
		material_vector.assign(0, 1);

		// retrieve the ray in the intersection lattice corresponding to the ray in the vertex lattice
		// grid ray has the structure: {{pair of ray coords}{vector of pairs{element,coord on ray}}}
		auto intersection_ray = intersection_lattice.find_ray(grid_ray.first);

		// if no mesh triangle was intersected along `grid_ray`
		if (intersection_ray == intersection_lattice.end()) {
			// iterate over vertices on the corresponding ray in grid vertex lattice
			for (const auto& vertex : grid_ray.second) {
				// for each store the unique global outside material vector (`vertex.element` is vertex id)
				vertex_labels[vertex.element] = material_vector;
			}
			// jump to the next ray
			continue;
		}

		// iterators to iterate over intersections on the current ray
		auto ray_iterator = intersection_ray->second.begin();
		const auto ray_iterator_end = intersection_ray->second.end();
		// loop to iterate over grid vertices on the current ray
		for (const auto& vertex : grid_ray.second) {
			// Step through the intersections on the current ray, updating the material vector, until
			// reaching the next vertex on the current `grid_ray`. NUMERICS: the "<" comparison in the
			// following loop might produce results inconsistent with SoS
			while (ray_iterator != ray_iterator_end && ray_iterator->coord_on_ray < vertex.coord_on_ray) {
				updateMaterialVector(grid, ray_iterator->element, material_vector);
				ray_iterator++;
				// ASSERT: once the last intersection on the ray is processed, the material vector should be
				// unique global outside
				if (ray_iterator == ray_iterator_end) {
					// assert(material_vector[0] == 1);
					for (int mat_it = 0, n = material_vector.getNNZ(); mat_it < n; ++mat_it) {
						int key = material_vector.getKey(mat_it);
						if (key != 0 && material_vector.getValue(mat_it) != 0) {
							return false;
						}
					}
				}
			}
			// once the coordinate of the next vertex on `grid_ray` is reached, save the current version
			// of `material_vector` on this grid vertex
			vertex_labels[vertex.element] = material_vector;
		}
	}
	return true;
}

// updates `material_vector` as the `intersection` is encountered along a grid ray
void GridLabeler::updateMaterialVector(Grid3DInterface& grid,
                                       const GridEdgeMeshFaceIntersection& intersection,
                                       SparseVector<int>& material_vector) const {
	Mesh3DTriangle* triangle = intersection.getTriangle();
	Vec2i labels = grid.convertMeshLabelsToGridLabels(triangle->getLabels());
	// change the material vector based on the orientation of `triangle` w.r.t. increasing grid ray
	// direction
	if (intersection.isTriNormalEdgeAligned()) {
		// entering into the material on triangle right hand normal side
		material_vector.add(labels[0], +1);
		material_vector.add(labels[1], -1);
	} else {
		// exiting from the material on triangle right hand normal side
		material_vector.add(labels[0], -1);
		material_vector.add(labels[1], +1);
	}
}

// save each grid edge-mesh triangle intersection on its grid edge
void GridLabeler::registerGridEdgeIntersections(
    Grid3DInterface& grid,
    const GridLattice<GridEdgeMeshFaceIntersection, long long>& intersection_lattice) const {
	for (const auto& ray_it : intersection_lattice) {
		for (const auto& point : ray_it.second) {
			grid.addIntersectionToEdge(point.element);
		}
	}
}

absl::flat_hash_set<long long> GridLabeler::getInconsistentVertices(
    std::vector<absl::flat_hash_map<long long, SparseVector<int>>>& labels_per_orentation) const {
	absl::flat_hash_set<long long> inconsistent_vertices;
	for (const auto& [vertex_id, material0] : labels_per_orentation[0]) {
		const SparseVector<int>& material1 = labels_per_orentation[1].at(vertex_id);
		const SparseVector<int>& material2 = labels_per_orentation[2].at(vertex_id);
		if (material0 != material1 || material0 != material2) {
			inconsistent_vertices.insert(vertex_id);
		}
	}
	return inconsistent_vertices;
}

void GridLabeler::relabelInconsistentVertices(
    std::vector<absl::flat_hash_map<long long, SparseVector<int>>>& labels_per_orentation,
    const absl::flat_hash_set<long long>& inconsistent_vertices) const {
	// For each vertex propagate material from 0-th orientation to all others.
	for (long long vertex : inconsistent_vertices) {
		SparseVector<int> material = labels_per_orentation[0][vertex];
		for (size_t i = 1; i < labels_per_orentation.size(); ++i) {
			labels_per_orentation[i][vertex] = material;
		}
	}
}

void GridLabeler::markCellsWithInconsistentVertices(
    Grid3DInterface& grid, const absl::flat_hash_set<long long>& inconsistent_vertices) const {
	for (long long vertex : inconsistent_vertices) {
		for (long long cell_id : grid.get_cells_neighboring_vertex(vertex)) {
			grid.markCellAsComplex(cell_id, Grid3DInterface::ComplexCellType::kFixed);
		}
	}
}
