/* GridMeshIntersector.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, 2021
 *
 * This is the implementation of intersection computation between grid and mesh.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "GridMeshIntersector.h"

#include <set>
#include <tuple>
#include <unordered_set>
#include <vector>

#include "../datastructures/Mesh3DVertex.h"
#include "../utilities/intersection/TriangleBoxIntersection.h"
#include "../utilities/tunicate/tunicate.h"
#include "../utilities/vec.h"

#pragma omp declare reduction(merge : std::vector<GridEdgeMeshFaceIntersection> : omp_out.insert( \
        omp_out.end(), omp_in.begin(), omp_in.end()))
//------------------------------------------------------------
// GridMeshIntersector functions
//------------------------------------------------------------
//------------------------------------------------------------
// grid edge-mesh triangle intersection tests
//------------------------------------------------------------

// performs bounding test on all mesh triangles, then using this data exectues the other version of
// `intersectMeshWithGridEdges`
std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>>
GridMeshIntersector::intersectMeshWithGridEdges(const Grid3DInterface& grid,
                                                const Mesh3DInterface& mesh) const {
	return intersectMeshWithGridEdges(grid, mesh, findBoundingRangesForAllTriangles(grid, mesh));
}

// perform grid edge-mesh triangle intersections, and use them as data to construct three
// `GridLattice`s, one per grid edge orientation (i.e. one per increasing coordinate axis direction)
std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>>
GridMeshIntersector::intersectMeshWithGridEdges(
    const Grid3DInterface& grid, const Mesh3DInterface& mesh,
    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>& triangle_bounding_cells)
    const {
	std::vector<GridEdgeMeshFaceIntersection> intersections;
	// iterate over mesh triangles, for each determine grid edges it intersects
	for (const auto& triangle_cell_it : triangle_bounding_cells) {
		Mesh3DTriangle* triangle = triangle_cell_it.first;
		const std::vector<long long>& cell_ids = triangle_cell_it.second;
		absl::flat_hash_set<long long> has_intersected_edge;
		// iterate over cells that `triangle` potentially intersects
		for (const long long cell : cell_ids) {
			for (const long long edge : grid.get_edges_neighboring_cell(cell)) {
				// the same edge can be investigated in multiple neighboring cells, therefore check whether
				// `edge` has already been investigated
				if ((has_intersected_edge.count(edge) == 0)) {
					// perform intersection test, if intersection is detected, store it in `intersections`
					intersect_grid_edge_with_mesh_triangle(grid, edge, mesh, triangle, intersections);
					has_intersected_edge.insert(edge);
				}
			}
		}
	}
	return buildLattices(grid, intersections);
}

std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>>
GridMeshIntersector::intersectMeshWithGridEdges(
    const Grid3DInterface& grid, const Mesh3DInterface& mesh,
    const std::vector<std::pair<Mesh3DTriangle*, std::pair<Vec3ll, Vec3ll>>>&
        triangle_bounding_ranges) const {
	std::vector<GridEdgeMeshFaceIntersection> intersections;
#pragma omp parallel for reduction(merge : intersections)
	for (const auto& [triangle, cell_range] : triangle_bounding_ranges) {
		for (int orientation = 0; orientation < 3; orientation++) {
			// There are more edges than cells, except in the direction of orientation.
			auto [min_coords, max_coords] = cell_range;
			max_coords += Vec3ll(1);
			max_coords[orientation] -= 1;

			for (long long i = min_coords[0]; i <= max_coords[0]; ++i) {
				for (long long j = min_coords[1]; j <= max_coords[1]; ++j) {
					for (long long k = min_coords[2]; k <= max_coords[2]; ++k) {
						long long edge_id = grid.get_edge_id(i, j, k, orientation);
						intersect_grid_edge_with_mesh_triangle(grid, edge_id, mesh, triangle, intersections);
					}
				}
			}
		}
	}
	return buildLattices(grid, intersections);
}

//------------------------------------------------------------
// triangle bounding tests
//------------------------------------------------------------

// performs the bounding test for each triangle, that is, finds and returns the axis-aligned block
// of all grid cells potentially intersected by input `triangle` + offset
std::vector<long long> GridMeshIntersector::findBoundingCellsForTriangle(
    const Grid3DInterface& grid, const Mesh3DInterface& mesh, Mesh3DTriangle* triangle) const {
	// save all the cells in the block of potentially intersected cells into `result_cells`
	auto [min_cell_coords, max_cell_coords] = findBoundingRangeForTriangle(grid, mesh, triangle);
	std::vector<long long> result_cells;
	long long total_size = dot(max_cell_coords - min_cell_coords, Vec3ll{1, 1, 1});
	result_cells.reserve(total_size);
	long long cell_id;
	for (long long i = min_cell_coords[0], max_i = max_cell_coords[0]; i <= max_i; i++) {
		for (long long j = min_cell_coords[1], max_j = max_cell_coords[1]; j <= max_j; j++) {
			for (long long k = min_cell_coords[2], max_k = max_cell_coords[2]; k <= max_k; k++) {
				cell_id = grid.get_cell_id(i, j, k);
				result_cells.push_back(cell_id);
			}
		}
	}
	return result_cells;
}

// performs the bounding test on all mesh triangles, and returns the gathered data as a map
absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>
GridMeshIntersector::findBoundingCellsForAllTriangles(const Grid3DInterface& grid,
                                                      const Mesh3DInterface& mesh) const {
	absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>> result;
	result.reserve(mesh.getNumberTris());
	for (Mesh3DTriangle* tri : mesh.ListTriangles()) {
		result[tri] = findBoundingCellsForTriangle(grid, mesh, tri);
	}
	return result;
}

std::vector<std::pair<Mesh3DTriangle*, std::pair<Vec3ll, Vec3ll>>>
GridMeshIntersector::findBoundingRangesForAllTriangles(const Grid3DInterface& grid,
                                                       const Mesh3DInterface& mesh) const {
	std::vector<std::pair<Mesh3DTriangle*, std::pair<Vec3ll, Vec3ll>>> result;
	result.reserve(mesh.getNumberTris());
	for (Mesh3DTriangle* tri : mesh.ListTriangles()) {
		result.emplace_back(tri, findBoundingRangeForTriangle(grid, mesh, tri));
	}
	return result;
}

std::pair<Vec3ll, Vec3ll> GridMeshIntersector::findBoundingRangeForTriangle(
    const Grid3DInterface& grid, const Mesh3DInterface& mesh, Mesh3DTriangle* triangle) const {
	const double offset = settings_->triangle_registration_offset;
	const std::vector<double> tolerance_offsets = {offset, -offset};
	const std::vector<Mesh3DVertex*> vertices = triangle->getVerts();
	std::vector<Vec3ll> cell_coords;
	cell_coords.reserve(3);

	// for each triangle vertex, find the cell intersected by the offset vertex position, and store in
	// `cell_coords`
	for (Mesh3DVertex* vertex : vertices) {
		Vec3d original_vcoords = vertex->getCoords();
		for (double tolerance : tolerance_offsets) {
			vertex->setCoords(original_vcoords + Vec3d(tolerance));
			long long cell_id = find_cell_id_for_mesh_vertex(grid, mesh, vertex);
			Vec3ll coords;
			grid.get_cell_coords(cell_id, coords[0], coords[1], coords[2]);
			cell_coords.push_back(coords);
		}
		vertex->setCoords(original_vcoords);
	}

	// find the bounding box of grid cells that are potentially intersected by `triangle`
	Vec3ll min_cell_coords = cell_coords[0];
	Vec3ll max_cell_coords = cell_coords[0];
	for (size_t i = 1; i < cell_coords.size(); ++i) {
		min_cell_coords = min_union(min_cell_coords, cell_coords[i]);
		max_cell_coords = max_union(max_cell_coords, cell_coords[i]);
	}
	return {min_cell_coords, max_cell_coords};
}

std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>>
GridMeshIntersector::buildLattices(
    const Grid3DInterface& grid,
    const std::vector<GridEdgeMeshFaceIntersection>& intersections) const {
	std::vector<std::vector<GridEdgeMeshFaceIntersection>> oriented_intersections(3);
	long long orientation;
	long long dummy_x, dummy_y, dummy_z;
	for (const auto& intersection : intersections) {
		grid.get_edge_coords(intersection.getEdgeId(), dummy_x, dummy_y, dummy_z, orientation);
		oriented_intersections[orientation].push_back(intersection);
	}

	auto position_extractor = [&grid](const GridEdgeMeshFaceIntersection& intersection) {
		long long dummy_orientation;
		Vec3ll coords;
		grid.get_edge_coords(intersection.getEdgeId(), coords[0], coords[1], coords[2],
		                     dummy_orientation);
		return coords;
	};

	// for each of the three orientations construct a `GridLattice`, using `oriented_intersections`
	// and `position_extractor`
	std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>> result;
	result.reserve(3);
	for (long long orientation = 0; orientation < 3; ++orientation) {
		result.emplace_back(oriented_intersections[orientation], orientation, position_extractor);
	}
	return result;
}

//------------------------------------------------------------
// GridMeshIntersectorNaive
//------------------------------------------------------------
//------------------------------------------------------------
// constructors
//------------------------------------------------------------
GridMeshIntersectorNaive::GridMeshIntersectorNaive(const TopoFixerSettings& settings,
                                                   double tolerance /*=1.e-10*/)
    : GridMeshIntersector(settings), tolerance_(tolerance) {}

void GridMeshIntersectorNaive::intersect_grid_edge_with_mesh_triangle(
    const Grid3DInterface& grid, const long long edge_id, const Mesh3DInterface& mesh,
    Mesh3DTriangle* triangle, std::vector<GridEdgeMeshFaceIntersection>& intersections) const {
	double step;
	bool is_normal_aligned;
	Vec3d intersection =
	    intersect_edge_with_triangle_plane(grid, edge_id, mesh, triangle, step, is_normal_aligned);
	if (step >= 0 && step <= 1 && is_inside_triangle(intersection, mesh, triangle)) {
		// Use egde coordinates for dimensions that are fixed.
		long long orientation;
		long long dummy_i, dummy_j, dummy_k;
		grid.get_edge_coords(edge_id, dummy_i, dummy_j, dummy_k, orientation);
		std::vector<long long> vert_ids = grid.get_verts_neighboring_edge(edge_id);
		Vec3d vert_coords;
		grid.getVertexPosition(vert_ids[0], vert_coords[0], vert_coords[1], vert_coords[2]);
		intersection[(orientation + 1) % 3] = vert_coords[(orientation + 1) % 3];
		intersection[(orientation + 2) % 3] = vert_coords[(orientation + 2) % 3];
		// TODO: fix barycentric coordinate computation.
		intersections.emplace_back(triangle, edge_id, intersection, Vec3d(0.3, 0.3, 0.3),
		                           is_normal_aligned);
	}
}

// TODO: Implement.
int GridMeshIntersectorNaive::intersect_mesh_edge_with_grid_face_triangles(
    const Grid3DInterface& grid, const std::vector<Vec3ll>& face_triangles,
    const Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d& intersection,
    double& bary_coords) const {
	return 0;
}

// TODO: Implement.
int GridMeshIntersectorNaive::intersect_mesh_edge_with_grid_face_triangles_int_priorities(
    const Grid3DInterface& grid, const std::vector<Vec3ll>& face_triangles,
    const Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d& intersection,
    double& bary_coords) const {
	return 0;
}

long long GridMeshIntersectorNaive::find_cell_id_for_mesh_vertex(const Grid3DInterface& grid,
                                                                 const Mesh3DInterface& mesh,
                                                                 Mesh3DVertex* vertex) const {
	Vec3d vertex_coords = vertex->getCoords();
	Vec3ll cell_coords;
	for (unsigned int i = 0; i < 3; ++i) {
		cell_coords[i] = floor(vertex_coords[i] / grid.get_cell_dx());
	}
	return grid.get_cell_id(cell_coords[0], cell_coords[1], cell_coords[2]);
}

double GridMeshIntersectorNaive::orient_grid_vertex_against_mesh_triangle(
    const Grid3DInterface& grid, const long long vert_id, const Mesh3DInterface& mesh,
    Mesh3DTriangle* triangle) const {
	Vec3d vert_pos;
	grid.getVertexPosition(vert_id, vert_pos[0], vert_pos[1], vert_pos[2]);
	return get_distance_to_triangle_plane(vert_pos, mesh, triangle);
}

// TODO: implement
double GridMeshIntersectorNaive::orient_mesh_vertex_against_grid_face_triangle(
    const Grid3DInterface& grid, const Vec3ll vertices, const Mesh3DInterface& mesh,
    Mesh3DVertex* vertex) const {
	return 0;
}

std::vector<GridMeshDegeneracy> GridMeshIntersectorNaive::find_intersection_degeneracies(
    const Grid3DInterface& grid, const Mesh3DInterface& mesh) const {
	return find_intersection_degeneracies(grid, mesh, findBoundingCellsForAllTriangles(grid, mesh));
}

std::vector<GridMeshDegeneracy> GridMeshIntersectorNaive::find_intersection_degeneracies(
    const Grid3DInterface& grid, const Mesh3DInterface& mesh,
    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>& triangle_bounding_cells)
    const {
	std::vector<GridMeshDegeneracy> result;
	absl::flat_hash_set<std::pair<Mesh3DTriangle*, long long>> is_triangle_grid_vertex_intersected;
	absl::flat_hash_set<std::pair<Mesh3DTriangle*, long long>> is_triangle_grid_edge_intersected;
	GridMeshDegeneracy degeneracy_template;
	degeneracy_template.type = GridMeshDegeneracy::Type::kGridNearTriangleBorder;
	for (const auto& triangle_cell_it : triangle_bounding_cells) {
		Mesh3DTriangle* triangle = triangle_cell_it.first;
		const std::vector<long long>& cell_ids = triangle_cell_it.second;
		std::vector<Mesh3DVertex*> verts = triangle->getVerts();
		for (const long long cell_id : cell_ids) {
			degeneracy_template.grid_info.type = GridMeshDegeneracy::GridInfo::ObjectType::kVertex;
			for (const long long grid_vert_id : grid.get_verts_neighboring_cell(cell_id)) {
				degeneracy_template.grid_info.vertex_id = grid_vert_id;
				if (is_triangle_grid_vertex_intersected.count({triangle, grid_vert_id})) {
					continue;
				}
				Vec3d grid_vert_pos;
				grid.getVertexPosition(grid_vert_id, grid_vert_pos[0], grid_vert_pos[1], grid_vert_pos[2]);

				Vec3d plane_coords = project_on_triangle_plane(grid_vert_pos, mesh, triangle);
				double distance_to_plane_sq = mag2(grid_vert_pos - plane_coords);
				if (distance_to_plane_sq < tolerance_ * tolerance_) {
					Vec3d trilinear = get_trilinear_coords(plane_coords, mesh, triangle);
					extract_degeneracies_from_trilinear(trilinear, verts, degeneracy_template, result);
				}
				is_triangle_grid_vertex_intersected.insert({triangle, grid_vert_id});
			}

			degeneracy_template.grid_info.type = GridMeshDegeneracy::GridInfo::ObjectType::kEdge;
			for (const long long edge : grid.get_edges_neighboring_cell(cell_id)) {
				degeneracy_template.grid_info.edge_id = edge;
				if (is_triangle_grid_edge_intersected.count({triangle, edge})) {
					continue;
				}
				double step;
				bool is_normal_aligned;
				Vec3d plane_coords =
				    intersect_edge_with_triangle_plane(grid, edge, mesh, triangle, step, is_normal_aligned);
				// There is no way to intersect an edge with a plane.
				if (step < -tolerance_ || step > 1.0) {
					continue;
				}
				Vec3d trilinear = get_trilinear_coords(plane_coords, mesh, triangle);
				extract_degeneracies_from_trilinear(trilinear, verts, degeneracy_template, result);
				is_triangle_grid_edge_intersected.insert({triangle, edge});
			}
		}
	}
	add_two_close_intersections_degeneracies(result, grid, mesh, triangle_bounding_cells);
	return result;
}

void GridMeshIntersectorNaive::extract_degeneracies_from_trilinear(
    const Vec3d& trilinear, const std::vector<Mesh3DVertex*>& verts,
    const GridMeshDegeneracy& degen_info, std::vector<GridMeshDegeneracy>& degeneracies) const {
	// Make sure we are close to triangle before doing any sophisticated checks.
	for (int j = 0; j < 3; ++j) {
		if (trilinear[j] < -tolerance_) {
			return;
		}
	}
	std::vector<std::vector<Mesh3DVertex*>> potential_edges;
	for (int j = 0; j < 3; ++j) {
		if (abs(trilinear[j]) < tolerance_) {
			potential_edges.push_back({verts[(j + 1) % 3], verts[(j + 2) % 3]});
		}
	}
	if (potential_edges.size() == 1) {
		GridMeshDegeneracy d = degen_info;
		d.tri_info.type = GridMeshDegeneracy::TriInfo::ObjectType::kEdge;
		d.tri_info.tri_edge = potential_edges[0];
		degeneracies.push_back(d);
	} else if (potential_edges.size() > 1) {
		std::map<Mesh3DVertex*, long long> vert_counts;
		for (const auto& potential_edge : potential_edges) {
			vert_counts[potential_edge[0]] += 1;
			vert_counts[potential_edge[1]] += 1;
		}

		for (const auto vert_count : vert_counts) {
			if (vert_count.second > 1) {
				GridMeshDegeneracy d = degen_info;
				d.tri_info.type = GridMeshDegeneracy::TriInfo::ObjectType::kVertex;
				d.tri_info.tri_vertex = vert_count.first;
				degeneracies.push_back(d);
			}
		}
	}
}

void GridMeshIntersectorNaive::add_two_close_intersections_degeneracies(
    std::vector<GridMeshDegeneracy>& result, const Grid3DInterface& grid,
    const Mesh3DInterface& mesh,
    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<long long>>& triangle_bounding_cells)
    const {
	const std::vector<GridLattice<GridEdgeMeshFaceIntersection, long long>> intersections =
	    intersectMeshWithGridEdges(grid, mesh, triangle_bounding_cells);

	for (const auto& lattice : intersections) {
		for (const auto& ray : lattice) {
			const auto& elements = ray.second;
			for (long long i = 1, n = elements.size(); i < n; ++i) {
				if (mag2(elements[i].element.getPosition() - elements[i - 1].element.getPosition()) <
				    tolerance_ * tolerance_) {
					GridMeshDegeneracy d;
					d.type = GridMeshDegeneracy::Type::kTwoCloseIntersections;
					d.intersection_pair = {elements[i].element, elements[i - 1].element};
				}
			}
		}
	}
}

Vec3d GridMeshIntersectorNaive::from_barycentric_to_trilinear(const Vec3d bary,
                                                              const Mesh3DInterface& mesh,
                                                              Mesh3DTriangle* triangle) const {
	std::vector<Mesh3DVertex*> tri_verts = triangle->getVerts();
	double area = triangle->getArea();
	Vec3d result = 2.0 * bary * area;

	for (int i = 0; i < 3; ++i) {
		result[i] /= mag(tri_verts[(i + 1) % 3]->getCoords() - tri_verts[(i + 2) % 3]->getCoords());
	}
	return result;
}

double GridMeshIntersectorNaive::get_distance_to_triangle_plane(const Vec3d coords,
                                                                const Mesh3DInterface& mesh,
                                                                Mesh3DTriangle* triangle) const {
	// Any point on the triangle works, so pick one.
	Mesh3DVertex* v0 = triangle->getHalfCorner()->getVertex();
	Vec3d normal = triangle->getNaiveNormal();
	normalize(normal);
	return dot(normal, coords - v0->getCoords());
}

Vec3d GridMeshIntersectorNaive::project_on_triangle_plane(const Vec3d coords,
                                                          const Mesh3DInterface& mesh,
                                                          Mesh3DTriangle* triangle) const {
	Vec3d normal = triangle->getNaiveNormal();
	normalize(normal);
	double distance = get_distance_to_triangle_plane(coords, mesh, triangle);
	return coords - distance * normal;
}

bool GridMeshIntersectorNaive::is_inside_triangle(Vec3d coords, const Mesh3DInterface& mesh,
                                                  Mesh3DTriangle* triangle) const {
	Vec3d barry = get_barycentric_coords(coords, mesh, triangle);
	return (barry[0] >= 0.0 && barry[0] <= 1.0) && (barry[1] >= 0.0 && barry[1] <= 1.0) &&
	       (barry[2] >= 0.0 && barry[2] <= 1.0);
}

Vec3d GridMeshIntersectorNaive::get_trilinear_coords(const Vec3d coords,
                                                     const Mesh3DInterface& mesh,
                                                     Mesh3DTriangle* triangle) const {
	return from_barycentric_to_trilinear(get_barycentric_coords(coords, mesh, triangle), mesh,
	                                     triangle);
}

Vec3d GridMeshIntersectorNaive::get_barycentric_coords(const Vec3d coords,
                                                       const Mesh3DInterface& mesh,
                                                       Mesh3DTriangle* triangle) const {
	std::vector<Mesh3DVertex*> tri_verts = triangle->getVerts();
	Vec3d v1 = tri_verts[0]->getCoords();
	Vec3d v2 = tri_verts[1]->getCoords();
	Vec3d v3 = tri_verts[2]->getCoords();
	Vec3d normal = cross(v2 - v1, v3 - v1);
	double magnitude = mag2(normal);

	double alpha = dot(cross(v3 - v2, coords - v2), normal);
	double beta = dot(cross(v1 - v3, coords - v3), normal);
	double gamma = dot(cross(v2 - v1, coords - v1), normal);
	return Vec3d(alpha, beta, gamma) / magnitude;
}

// Naive intersection algorithm, find intersection between a grid edge and a mesh triangle
// by triangle similarity. For (almost) coplanar edge and triangle, return a far away
// intersection point (meant as a point in infinity).
Vec3d GridMeshIntersectorNaive::intersect_edge_with_triangle_plane(
    const Grid3DInterface& grid, const long long edge_id, const Mesh3DInterface& mesh,
    Mesh3DTriangle* triangle, double& step, bool& is_normal_aligned) const {
	std::vector<long long> vert_ids = grid.get_verts_neighboring_edge(edge_id);
	std::vector<Vec3d> vert_coords(2);

	for (int i = 0; i < 2; ++i) {
		grid.getVertexPosition(vert_ids[i], vert_coords[i][0], vert_coords[i][1], vert_coords[i][2]);
	}

	// Any point on the triangle works, so pick one.
	Vec3d v1 = triangle->getHalfCorner()->getVertex()->getCoords();
	Vec3d normal = triangle->getNaiveNormal();
	Vec3d direction = vert_coords[1] - vert_coords[0];
	double normal_dot = dot(direction, normal);
	is_normal_aligned = normal_dot > 0;
	if (abs(normal_dot) < 1e-9) {
		step = 10.0;
	} else {
		step = dot(v1 - vert_coords[0], normal) / normal_dot;
	}
	Vec3d intersection = vert_coords[0] + step * direction;
	return intersection;
}

void GridMeshSoSIntersector::intersect_grid_edge_with_mesh_triangle(
    const Grid3DInterface& grid, const long long edge_id, const Mesh3DInterface& mesh,
    Mesh3DTriangle* triangle, std::vector<GridEdgeMeshFaceIntersection>& intersections) const {
	Mesh3DVertex* vp1;
	Mesh3DVertex* vp2;
	Mesh3DVertex* vp3;
	triangle->getVerts(&vp1, &vp2, &vp3);
	Vec3d v1 = vp1->getCoords();
	Vec3d v2 = vp2->getCoords();
	Vec3d v3 = vp3->getCoords();
	long long vid1 = reinterpret_cast<size_t>(vp1);
	long long vid2 = reinterpret_cast<size_t>(vp2);
	long long vid3 = reinterpret_cast<size_t>(vp3);

	long long x, y, z, orient;
	long long ev1, ev2;
	Vec3d e1;
	Vec3d e2;

	grid.get_edge_coords(edge_id, x, y, z, orient);
	grid.unsafeGetVertsNeighbouringEdge(x, y, z, orient, ev1, ev2);
	grid.getVertexPosition(ev1, e1[0], e1[1], e1[2]);
	grid.getVertexPosition(ev2, e2[0], e2[1], e2[2]);

	double alpha0, alpha1, alpha2, alpha3, alpha4;
	if (sos_simplex_intersection3d_unnormalized(/*k=*/2, ev1, e1.v, ev2, e2.v, -vid1, v1.v, -vid2,
	                                            v2.v, -vid3, v3.v, &alpha0, &alpha1, &alpha2, &alpha3,
	                                            &alpha4)) {
		// Unnormalized barycentric coordinates show the orientation sign of the opposite element.
		// Specifically, index 0 corresponds to the orientation of edge vertex with higher coordinates
		// (e2).
		bool is_normal_aligned = alpha0 > 0;
		double sum = alpha0 + alpha1;
		Vec3d intersection = e1;
		intersection[orient] = e1[orient] * (alpha0 / sum) + e2[orient] * (alpha1 / sum);
		intersections.emplace_back(triangle, edge_id, intersection,
		                           normalizeBaryCoords({alpha2, alpha3, alpha4}), is_normal_aligned);
	}
}

int GridMeshSoSIntersector::intersect_mesh_edge_with_grid_face_triangles(
    const Grid3DInterface& grid, const std::vector<Vec3ll>& face_triangles,
    const Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d& intersection,
    double& bary_coord) const {
	Vec3d c1 = v1->getCoords();
	Vec3d c2 = v2->getCoords();
	int vid1 = reinterpret_cast<size_t>(v1);
	int vid2 = reinterpret_cast<size_t>(v2);

	for (const Vec3ll ft : face_triangles) {
		std::vector<Vec3d> face_coords(3);
		for (size_t i = 0; i < 3; ++i) {
			grid.getVertexPosition(ft[i], face_coords[i][0], face_coords[i][1], face_coords[i][2]);
		}

		std::vector<double> intersection_coords(5);
		double* alphas = intersection_coords.data();
		int is_intersecting = sos_simplex_intersection3d(
		    /*k=*/2, -vid1, c1.v, -vid2, c2.v, ft[0], face_coords[0].v, ft[1], face_coords[1].v, ft[2],
		    face_coords[2].v, alphas, alphas + 1, alphas + 2, alphas + 3, alphas + 4);

		if (is_intersecting) {
			intersection = c1 * alphas[0] + c2 * alphas[1];
			bary_coord = alphas[1];
			return is_intersecting;
		}
	}
	return 0;
}

int GridMeshSoSIntersector::intersect_mesh_edge_with_grid_face_triangles_int_priorities(
    const Grid3DInterface& grid, const std::vector<Vec3ll>& face_triangles,
    const Mesh3DInterface& mesh, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d& intersection,
    double& bary_coord) const {
	Vec3d c1 = v1->getCoords();
	Vec3d c2 = v2->getCoords();
	int vid1 = mesh.getVertexIndex(v1);
	int vid2 = mesh.getVertexIndex(v2);

	for (const Vec3ll ft : face_triangles) {
		std::vector<Vec3d> face_coords(3);
		for (size_t i = 0; i < 3; ++i) {
			grid.getVertexPosition(ft[i], face_coords[i][0], face_coords[i][1], face_coords[i][2]);
		}

		std::vector<double> intersection_coords(5);
		double* alphas = intersection_coords.data();
		int is_intersecting = sos_simplex_intersection3d(
		    /*k=*/2, vid1, c1.v, vid2, c2.v, ft[0], face_coords[0].v, ft[1], face_coords[1].v, ft[2],
		    face_coords[2].v, alphas, alphas + 1, alphas + 2, alphas + 3, alphas + 4);

		if (is_intersecting) {
			intersection = c1 * alphas[0] + c2 * alphas[1];
			bary_coord = alphas[1];
			return is_intersecting;
		}
	}
	return 0;
}

long long GridMeshSoSIntersector::find_cell_id_for_mesh_vertex(const Grid3DInterface& grid,
                                                               const Mesh3DInterface& mesh,
                                                               Mesh3DVertex* vertex) const {
	Vec3d vertex_coords = vertex->getCoords();
	Vec3d non_rounded_cell_coords = (vertex_coords - grid.getOriginCoords()) / grid.get_cell_dx();
	Vec3ll cell_coords;
	for (unsigned int i = 0; i < 3; ++i) {
		cell_coords[i] = floor(non_rounded_cell_coords[i]);
	}
	double tolerance = grid.get_cell_dx() / 100.0;

	for (int idx = 0; idx < 3; ++idx) {
		// If the point is too close to a grid face, check properly that the rounded coordinates match
		// the orientation tests.
		if (non_rounded_cell_coords[idx] - cell_coords[idx] < tolerance) {
			// This face has normals pointing inside the cell.
			std::vector<Vec3ll> face_triangles = grid.get_face_triangles(
			    grid.get_face_id(cell_coords[0], cell_coords[1], cell_coords[2], idx));
			// If the vertex lies on the negative side of the face -> vertex belongs to another cell.
			if (orient_mesh_vertex_against_grid_face_triangle(grid, face_triangles[0], mesh, vertex) ==
			    0) {
				cell_coords[idx] -= 1;
			}
		} else if (non_rounded_cell_coords[idx] - cell_coords[idx] + 1 < tolerance) {
			Vec3ll neighbour_cell_coords = cell_coords;
			neighbour_cell_coords[idx] += 1;
			// This face has normals pointing outside the current cell and inside neighbouring cell.
			std::vector<Vec3ll> face_triangles = grid.get_face_triangles(grid.get_face_id(
			    neighbour_cell_coords[0], neighbour_cell_coords[1], neighbour_cell_coords[2], idx));
			// If the vertex lies on the positive side of the face of a neighbour -> vertex belongs to
			// another cell.
			if (orient_mesh_vertex_against_grid_face_triangle(grid, face_triangles[0], mesh, vertex) ==
			    1) {
				cell_coords[idx] += 1;
			}
		}
	}
	return grid.get_cell_id(cell_coords[0], cell_coords[1], cell_coords[2]);
}

double GridMeshSoSIntersector::orient_grid_vertex_against_mesh_triangle(
    const Grid3DInterface& grid, const long long vert_id, const Mesh3DInterface& mesh,
    Mesh3DTriangle* triangle) const {
	Vec3d grid_vert_pos;
	grid.getVertexPosition(vert_id, grid_vert_pos[0], grid_vert_pos[1], grid_vert_pos[2]);
	std::vector<Mesh3DVertex*> tri_verts = triangle->getVerts();
	Vec3d v1 = tri_verts[0]->getCoords();
	Vec3d v2 = tri_verts[1]->getCoords();
	Vec3d v3 = tri_verts[2]->getCoords();
	int vid1 = reinterpret_cast<size_t>(tri_verts[0]);
	int vid2 = reinterpret_cast<size_t>(tri_verts[1]);
	int vid3 = reinterpret_cast<size_t>(tri_verts[2]);
	return sos_orientation3d(vert_id, grid_vert_pos.v, -vid1, v1.v, -vid2, v2.v, -vid3, v3.v);
}

double GridMeshSoSIntersector::orient_mesh_vertex_against_grid_face_triangle(
    const Grid3DInterface& grid, const Vec3ll vertices, const Mesh3DInterface& mesh,
    Mesh3DVertex* vertex) const {
	Vec3d mesh_vert_pos = vertex->getCoords();
	int tid1 = reinterpret_cast<size_t>(vertex);

	Vec3d v1;
	Vec3d v2;
	Vec3d v3;
	grid.getVertexPosition(vertices[0], v1[0], v1[1], v1[2]);
	grid.getVertexPosition(vertices[1], v2[0], v2[1], v2[2]);
	grid.getVertexPosition(vertices[2], v3[0], v3[1], v3[2]);
	return sos_orientation3d(-tid1, mesh_vert_pos.v, vertices[0], v1.v, vertices[1], v2.v,
	                         vertices[2], v3.v);
}

Vec3d GridMeshSoSIntersector::normalizeBaryCoords(Vec3d bary) const {
	bary /= bary[0] + bary[1] + bary[2];
	bary[0] = bary[0] == 1 ? 0.9999999999999999 : bary[0];
	bary[1] = bary[1] == 1 ? 0.9999999999999999 : bary[1];
	bary[2] = bary[2] == 1 ? 0.9999999999999999 : bary[2];
	return bary;
}
