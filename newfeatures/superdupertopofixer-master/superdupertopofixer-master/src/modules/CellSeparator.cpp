/* CellSeparator.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2021
 *
 * This is the implementation file for the module that separates the triangles to be completely
 * inside or completely outside of the complex cell region.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "CellSeparator.h"

#include <algorithm>
#include <cstddef>
#include <limits>
#include <queue>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "../datastructures/Grid3DInterface.h"
#include "../datastructures/GridMeshIntersection.h"
#include "../datastructures/Mesh3DHalfCorner.h"
#include "../datastructures/Mesh3DInterface.h"
#include "../datastructures/Mesh3DTriangle.h"
#include "../datastructures/Mesh3DVertex.h"
#include "../datastructures/TriangleSubdivision.h"
#include "../submodules/GridMeshIntersector.h"
#include "../utilities/vec.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// function that coordinates the run of the cell separator module
int CellSeparator::run(Mesh3DInterface& mesh, Grid3DInterface& grid,
                       GridMeshIntersector& intersector, int orientation) {
	// initialize inside/outside partition sets
	inside_triangles_.clear();
	outside_triangles_.clear();

	// retrieve faces and cells on the interface between complex and simple regions
	std::vector<long long> front_faces =
	    grid.getFrontFacesVector();  // faces on complex region boundary
	std::vector<long long> front_cells =
	    grid.getComplexRegionFrontCellsVector();  // cells on complex region boundary
	std::vector<long long> complex_cells =
	    grid.getComplexCellsVector(Grid3DInterface::ComplexCellType::kBoth);  // all complex cells

	// fill in the map `tri_to_intersections` that assigns to each mesh triangle the intersections
	// with grid edges it participates in
	absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>
	    tri_to_intersections = aggregateIntersectionsOnTriangles(grid, front_faces);

	absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>
	    m_edge_to_intersections = aggregateIntersectionsOnMeshEdges(grid, front_faces);

	absl::flat_hash_map<SortedMeshEdge, std::vector<double>> edge_to_barys =
	    spreadMeshEdgeIntersections(m_edge_to_intersections);

	// Create all vertices for intersections on an edge.
	for (auto& [edge, intersections] : m_edge_to_intersections) {
		for (GridFaceMeshEdgeIntersection& intersection : intersections) {
			intersection.setVertex(mesh.makeNewVertex());
		}
	}

	for (auto& [tri, intersections] : tri_to_intersections) {
		for (GridEdgeMeshFaceIntersection& intersection : intersections) {
			intersection.setVertex(mesh.makeNewVertex());
		}
	}

	const absl::flat_hash_set<Mesh3DTriangle*> triangles =
	    getSubdivisionTriangles(mesh, tri_to_intersections, m_edge_to_intersections);
	subdivideTriangles(grid, mesh, intersector, triangles, tri_to_intersections,
	                   m_edge_to_intersections);

	restoreOriginalIntersectionPositions(m_edge_to_intersections, edge_to_barys);

	// Propagate the labels across all components to avoid false positives during separate component
	// detection step.
	absl::flat_hash_set<SortedMeshEdge> graph_edges = getGraphEdges(grid, front_faces);
	floodTriangles(mesh, inside_triangles_, /*is_start_inside=*/true, graph_edges);
	floodTriangles(mesh, outside_triangles_, /*is_start_inside=*/false, graph_edges);

	absl::flat_hash_set<Mesh3DTriangle*> new_insides =
	    markSeparateComponents(mesh, grid, intersector, complex_cells);
	floodTriangles(mesh, new_insides, /*is_start_inside=*/true, graph_edges);
	removeInternalMesh(mesh, grid, front_faces);

	if (settings->verbosity >= 1) {
		std::cout << "-cell separator finished with return value " << 0 << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return 0;
}

void CellSeparator::clearState() {
	failed_separation_faces_.clear();
	inside_triangles_.clear();
	outside_triangles_.clear();
}

void CellSeparator::addEdgesToGraphOnFace(Grid3DInterface& grid, Mesh3DInterface& mesh,
                                          Mesh3DVertex* v1, Mesh3DVertex* v2,
                                          long long face_id) const {
	Mesh3DHalfCorner* outside_hfc = nullptr;
	for (Mesh3DHalfCorner* hfc : mesh.getHalfCornersAroundEdge(v1, v2)) {
		if (outside_triangles_.contains(hfc->getTri())) {
			outside_hfc = hfc;
			break;
		}
	}
	assert(outside_hfc != nullptr);
	grid.add_graph_on_face(face_id, {std::min(v1, v2), std::max(v1, v2)}, outside_hfc->getTri());
}

void CellSeparator::floodTriangles(Mesh3DInterface& mesh,
                                   const absl::flat_hash_set<Mesh3DTriangle*>& start_triangles,
                                   bool is_start_inside,
                                   const absl::flat_hash_set<SortedMeshEdge>& graph_edges) {
	std::queue<std::pair<Mesh3DTriangle*, bool>> traversal_queue;
	for (Mesh3DTriangle* triangle : start_triangles) {
		traversal_queue.push({triangle, is_start_inside});
	}

	absl::flat_hash_set<Mesh3DTriangle*> visited_triangles;
	while (!traversal_queue.empty()) {
		auto [tri, is_inside] = traversal_queue.front();
		traversal_queue.pop();
		auto [it, is_inserted] = visited_triangles.insert(tri);
		// Skip already visited.
		if (!is_inserted) {
			continue;
		}
		if (is_inside) {
			inside_triangles_.insert(tri);
		} else {
			outside_triangles_.insert(tri);
		}

		Mesh3DHalfCorner* current_hc = tri->getHalfCorner();
		for (int i = 0; i < 3; ++i) {
			Mesh3DVertex* v1 = current_hc->getNext()->getVertex();
			Mesh3DVertex* v2 = current_hc->getPrev()->getVertex();
			bool new_is_inside = is_inside ^ graph_edges.contains({v1, v2});
			std::vector<Mesh3DHalfCorner*> neighbouring_hcs;
			mesh.walkAroundEdge(current_hc, neighbouring_hcs);
			for (Mesh3DHalfCorner* hfc : neighbouring_hcs) {
				Mesh3DTriangle* neigh_tri = hfc->getTri();
				bool visited = visited_triangles.contains(neigh_tri) ||
				               inside_triangles_.contains(neigh_tri) ||
				               outside_triangles_.contains(neigh_tri);
				if (!visited) {
					traversal_queue.push({tri, new_is_inside});
				}
			}
			current_hc = current_hc->getNext();
		}
	}
}

std::tuple<Mesh3DTriangle*, bool> CellSeparator::orientTripleLeaves(
    Grid3DInterface& grid, const std::vector<Mesh3DTriangle*>& triple_leaves,
    const absl::flat_hash_map<Mesh3DVertex*, long long>& edge_vertex_to_grid_edge) const {
	for (Mesh3DTriangle* tri : triple_leaves) {
		std::vector<Mesh3DVertex*> verts = tri->getVerts();
		std::vector<long long> grid_edge_ids;
		grid_edge_ids.reserve(3);
		for (Mesh3DVertex* vert : verts) {
			grid_edge_ids.push_back(edge_vertex_to_grid_edge.at(vert));
		}
		// We rely on flood-filling to sort out coplanar triple leaves.
		if (grid.are_edges_axis_coplanar(grid_edge_ids)) {
			continue;
		}

		for (size_t vert_idx = 0; vert_idx < verts.size(); ++vert_idx) {
			size_t next_vert_idx = (vert_idx + 1) % verts.size();
			size_t prev_vert_idx = (vert_idx + verts.size() - 1) % verts.size();
			std::vector<long long> grid_face_ids =
			    intersect_vectors(grid.get_faces_neighboring_edge(grid_edge_ids[vert_idx]),
			                      grid.get_faces_neighboring_edge(grid_edge_ids[next_vert_idx]));
			if (grid_face_ids.size() < 1) {
				continue;
			}
			assert(grid_face_ids.size() == 1);
			long long grid_face_id = grid_face_ids[0];
			if (!grid.isFaceInComplexFront(grid_face_id)) {
				continue;
			}
			long long orientation =
			    orient_grid_edge_against_grid_face(grid, grid_edge_ids[prev_vert_idx], grid_face_id);
			assert(orientation != 0);
			if (!isComplexCellOnIncreasingSideOfFrontFace(grid, grid_face_id)) {
				orientation *= -1;
			}
			return {tri, orientation > 0};
		}
	}
	return {nullptr, false};
}

absl::flat_hash_set<Mesh3DTriangle*> CellSeparator::markSeparateComponents(
    Mesh3DInterface& mesh, Grid3DInterface& grid, const GridMeshIntersector& intersector,
    const std::vector<long long>& complex_cells) {
	// Subdivisions register new triangles, so is enough to check for
	// registered triangles that are not marked anyhow.
	absl::flat_hash_set<Mesh3DTriangle*> new_inside_triangles;
	for (long long cell_id : complex_cells) {
		for (Mesh3DTriangle* tri : grid.getCellTriangles(cell_id)) {
			if (inside_triangles_.count(tri) || outside_triangles_.count(tri)) {
				continue;
			}

			// If any vertex is outside complex cell region, then triangle is outside.
			bool is_removed = true;
			for (Mesh3DVertex* vertex : tri->getVerts()) {
				long long v_cell_id = intersector.find_cell_id_for_mesh_vertex(grid, mesh, vertex);
				if (!grid.isCellMarkedComplex(v_cell_id, Grid3DInterface::ComplexCellType::kBoth)) {
					is_removed = false;
					break;
				}
			}
			if (is_removed) {
				new_inside_triangles.insert(tri);
				inside_triangles_.insert(tri);
			}
		}
	}
	return new_inside_triangles;
}

void CellSeparator::removeInternalMesh(Mesh3DInterface& mesh, Grid3DInterface& grid,
                                       const std::vector<long long>& complex_front_faces) const {
	absl::flat_hash_set<Mesh3DVertex*> vertices_to_keep;
	for (const long long face_id : complex_front_faces) {
		for (const auto& [edge, tri] : grid.getGraphOnFace(face_id)) {
			vertices_to_keep.insert(edge.first);
			vertices_to_keep.insert(edge.second);
		}
	}

	absl::flat_hash_set<Mesh3DVertex*> vertices_to_delete;
	for (Mesh3DTriangle* triangle : inside_triangles_) {
		std::vector<Mesh3DVertex*> verts(3, nullptr);
		triangle->getVerts(&verts[0], &verts[1], &verts[2]);
		for (Mesh3DVertex* vert : verts) {
			if (!vertices_to_keep.contains(vert)) {
				vertices_to_delete.insert(vert);
			}
		}
		mesh.deleteTriangle(triangle);
	}
	for (Mesh3DVertex* vert : vertices_to_delete) {
		mesh.deleteVertex(vert);
	}
};

// returns a map that to each mesh triangle assigns a vector of `GridEdgeMeshFaceIntersection`s
// that the triangle participates in
absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>
CellSeparator::aggregateIntersectionsOnTriangles(
    Grid3DInterface& grid, const std::vector<long long>& complex_front_faces) const {
	absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>
	    m_tri_to_intersection;
	absl::flat_hash_set<long long> visited_edges;
	for (const long long front_face : complex_front_faces) {
		for (const long long edge_id : grid.get_edges_neighboring_face(front_face)) {
			auto [it, is_inserted] = visited_edges.insert(edge_id);
			if (!is_inserted) {
				continue;
			}
			for (const GridEdgeMeshFaceIntersection& intersection :
			     grid.get_intersections_on_edge(edge_id)) {
				m_tri_to_intersection[intersection.getTriangle()].push_back(intersection);
			}
		}
	}
	return m_tri_to_intersection;
}

// returns a map that to each mesh edge assigns a vector of `GridEdgeMeshFaceIntersection`s that
// the edge participates in
absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>
CellSeparator::aggregateIntersectionsOnMeshEdges(
    Grid3DInterface& grid, const std::vector<long long>& complex_front_faces) const {
	absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>
	    m_edge_to_intersections;
	// iterate over `GridFaceMeshEdgeIntersection`s saved on front faces
	for (const long long front_face : complex_front_faces) {
		for (const GridFaceMeshEdgeIntersection& intersection :
		     grid.get_mesh_edge_intersections_on_face(front_face)) {
			// add `intersection` to `m_edge_to_intersections`, and set its internal ordering and flags
			addIntersectionToMeshEdge(grid, intersection, m_edge_to_intersections);
		}
	}

	// for every mesh edge, sort its intersections based on the grid face coordinates
	for (auto& [edge, intersections] : m_edge_to_intersections) {
		if (intersections.empty()) {
			continue;
		}
		GridFaceMeshEdgeCmp cmp_fn(grid, intersections[0].getEdgeFirst(),
		                           intersections[0].getEdgeSecond());
		std::sort(intersections.begin(), intersections.end(), cmp_fn);
	}

	// return the map from mesh edges to grid face-mesh edge intersections
	return m_edge_to_intersections;
}

// TODO: implement a proper adaptive precision normalization.
Vec3d CellSeparator::moveAwayFromTriEdge(Vec3d bary) const {
	bool changed = false;
	double min_float = kSnappingTolerance;
	if (bary[0] < min_float) {
		bary[0] = min_float;
		changed = true;
	}
	if (bary[1] < min_float) {
		bary[1] = min_float;
		changed = true;
	}
	if (bary[2] < min_float) {
		bary[2] = min_float;
		changed = true;
	}
	if (!changed) {
		return bary;
	}

	bary /= bary[0] + bary[1] + bary[2];
	bary[0] = bary[0] == 1 ? 0.9999999999999999 : bary[0];
	bary[1] = bary[1] == 1 ? 0.9999999999999999 : bary[1];
	bary[2] = bary[2] == 1 ? 0.9999999999999999 : bary[2];
	return bary;
}

Vec2d CellSeparator::moveAwayFromTriEdge(Vec2d bary) const {
	Vec3d full_bary = {bary[0], bary[1], 1.0 - bary[0] - bary[1]};
	full_bary = moveAwayFromTriEdge(full_bary);
	return {full_bary[0], full_bary[1]};
}

Vec2d CellSeparator::extractIndependentCoords(Vec3d bary) const { return {bary[1], bary[2]}; }

absl::flat_hash_set<Mesh3DTriangle*> CellSeparator::getSubdivisionTriangles(
    Mesh3DInterface& mesh,
    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
        face_intersections,
    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
        edge_to_intersections) const {
	absl::flat_hash_set<Mesh3DTriangle*> triangles;
	triangles.reserve(face_intersections.size());
	for (auto& [triangle, intesections] : face_intersections) {
		triangles.emplace(triangle);
	}

	for (auto& [edge, intersections] : edge_to_intersections) {
		for (Mesh3DTriangle* tri : mesh.getTrianglesAroundEdge(edge.getSmaller(), edge.getLarger())) {
			triangles.emplace(tri);
		}
	}
	return triangles;
}

std::vector<CellSeparator::MeshEdge> CellSeparator::extractTriangulationElements(
    Grid3DInterface& grid, Mesh3DTriangle* triangle,
    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
        face_intersections,
    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
        edge_to_intersections,
    absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint>& vertex_to_tri_point) const {
	std::vector<MeshEdge> segments;
	absl::flat_hash_map<long long, std::vector<Mesh3DVertex*>> face_to_vertices;

	// Process outline of the triangle.
	std::vector<Mesh3DVertex*> vertices = triangle->getVerts();
	std::vector<Vec2d> coords = {{0.0, 0.0}, {1.0, 0.0}, {0.0, 1.0}};
	for (int i = 0; i < 3; ++i) {
		Mesh3DVertex* v1 = vertices[i];
		Mesh3DVertex* v2 = vertices[(i + 1) % 3];
		Vec2d c1 = coords[i];
		Vec2d c2 = coords[(i + 1) % 3];
		vertex_to_tri_point[v1] = TriangulationPoint(c1, /*element_id=*/-1, /*is_internal=*/false);

		auto it = edge_to_intersections.find({v1, v2});
		if (it != edge_to_intersections.end()) {
			if (v1 != it->first.getSmaller()) {
				std::swap(v1, v2);
				std::swap(c1, c2);
			}
			for (GridFaceMeshEdgeIntersection inter : it->second) {
				Vec2d inter_coords = c1 + inter.getBaryCoord() * (c2 - c1);
				Mesh3DVertex* inter_vertex = inter.getVertex();
				vertex_to_tri_point[inter.getVertex()] =
				    TriangulationPoint(inter_coords, inter.getFaceId(), /*is_internal=*/false);
				face_to_vertices[inter.getFaceId()].push_back(inter_vertex);
				segments.push_back({v1, inter_vertex});
				v1 = inter_vertex;
			}
		}
		segments.push_back({v1, v2});
	}

	// Process inside segments.
	auto it = face_intersections.find(triangle);
	if (it != face_intersections.end()) {
		for (const GridEdgeMeshFaceIntersection& intersection : it->second) {
			for (const long long face_id : grid.get_faces_neighboring_edge(intersection.getEdgeId())) {
				if (!grid.isFaceInComplexFront(face_id)) {
					continue;
				}
				face_to_vertices[face_id].push_back(intersection.getVertex());
			}
			Vec2d inter_coords = extractIndependentCoords(intersection.getBary());
			vertex_to_tri_point[intersection.getVertex()] =
			    TriangulationPoint(inter_coords, intersection.getEdgeId(), /*is_internal=*/true);
		}
	}
	for (auto& [face_id, face_verts] : face_to_vertices) {
		// All faces must define correct segments on the face.
		assert(face_verts.size() == 2);
		segments.push_back({face_verts[0], face_verts[1]});
	}
	return segments;
}

void CellSeparator::addSegmentsToFaceGraph(
    Grid3DInterface& grid, Mesh3DInterface& mesh, Mesh3DTriangle* triangle,
    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
        face_intersections,
    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
        edge_to_intersections) const {
	absl::flat_hash_map<long long, std::vector<Mesh3DVertex*>> face_to_vertices;

	// Process T2s.
	std::vector<Mesh3DVertex*> vertices = triangle->getVerts();
	for (int i = 0; i < 3; ++i) {
		Mesh3DVertex* v1 = vertices[i];
		Mesh3DVertex* v2 = vertices[(i + 1) % 3];
		auto it = edge_to_intersections.find({v1, v2});
		if (it != edge_to_intersections.end()) {
			for (GridFaceMeshEdgeIntersection inter : it->second) {
				face_to_vertices[inter.getFaceId()].push_back(inter.getVertex());
			}
		}
	}

	// Process inside segments.
	auto it = face_intersections.find(triangle);
	if (it != face_intersections.end()) {
		for (const GridEdgeMeshFaceIntersection& intersection : it->second) {
			for (const long long face_id : grid.get_faces_neighboring_edge(intersection.getEdgeId())) {
				if (!grid.isFaceInComplexFront(face_id)) {
					continue;
				}
				face_to_vertices[face_id].push_back(intersection.getVertex());
			}
			grid.add_mesh_vertex_to_edge(intersection.getEdgeId(), intersection.getVertex());
		}
	}
	for (auto& [face_id, face_verts] : face_to_vertices) {
		// All faces must define correct segments on the face.
		assert(face_verts.size() == 2);
		addEdgesToGraphOnFace(grid, mesh, face_verts[0], face_verts[1], face_id);
	}
}

absl::flat_hash_map<SortedMeshEdge, std::vector<double>> CellSeparator::spreadMeshEdgeIntersections(
    absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
        edge_to_intersections) const {
	absl::flat_hash_map<SortedMeshEdge, std::vector<double>> modified_edges;
	for (auto& [mesh_edge, intersections] : edge_to_intersections) {
		if (intersections.empty()) {
			continue;
		}

		bool is_modified = false;
		std::vector<double> old_barys;
		old_barys.reserve(intersections.size());
		for (const GridFaceMeshEdgeIntersection& intersection : intersections) {
			old_barys.push_back(intersection.getBaryCoord());
		}

		double offset = 0.0;
		for (double bary : old_barys) {
			offset = std::max(offset + kSnappingTolerance, bary);
		}
		// Last point should be away from the mesh vertex, so add more to the offset.
		offset += kSnappingTolerance;

		// If the last point is too close to the mesh vertex, scale everything down a bit to make room
		// for overlap resolutions.
		if (offset > 1.0) {
			double shrink_factor = 1.0 / offset;
			for (size_t i = 0; i < intersections.size(); ++i) {
				intersections[i].setBaryCoord(shrink_factor * old_barys[i]);
			}
			is_modified = true;
		}

		// Check that no two intersections lie too close to each other. If so, push them apart.
		double cur_bary = 0.0;
		for (GridFaceMeshEdgeIntersection& cur_intersection : intersections) {
			double next_bary = cur_intersection.getBaryCoord();
			double bary_distance = next_bary - cur_bary;
			if (bary_distance < kSnappingTolerance) {
				cur_bary += kSnappingTolerance;
				cur_intersection.setBaryCoord(cur_bary);
				is_modified = true;
			} else {
				cur_bary = next_bary;
			}
		}

		if (is_modified) {
			modified_edges[mesh_edge] = old_barys;
			std::cout << "Move some points" << std::endl;
		}
	}
	return modified_edges;
}

void CellSeparator::spreadMeshFaceIntersections(
    Grid3DInterface& grid, Mesh3DTriangle* triangle,
    absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint>& vertex_to_tri_point) {
	std::vector<TriangulationPoint*> internal_points;
	for (auto& [vertex, tri_point] : vertex_to_tri_point) {
		if (tri_point.is_internal) {
			internal_points.push_back(&tri_point);
		}
	}

	if (internal_points.empty()) {
		return;
	}

	// Precompute triangle values.
	Vec3d tri_normal = triangle->getNaiveNormal();
	double tri_area = triangle->getArea();
	// Initialize distribution in case we need to use random directions.
	std::uniform_real_distribution<double> angle_dis(0, 2 * M_PI);

	std::vector<Vec2d> barys;
	barys.reserve(internal_points.size());

	// Triangle edge <-> grid edge degeneracy handling.
	for (const TriangulationPoint* tri_point : internal_points) {
		barys.emplace_back(moveAwayFromTriEdge(tri_point->coords));
	}

	// Triangle face <-> grid vertex degeneracy handling.
	std::vector<std::pair<int, int>> degeneracies;
	bool is_repulsion = false;
	do {
		degeneracies.clear();
		for (size_t i = 0; i < barys.size(); ++i) {
			for (size_t j = i + 1; j < barys.size(); ++j) {
				if (dist2(barys[i], barys[j]) < kSnappingTolerance * kSnappingTolerance) {
					degeneracies.emplace_back(i, j);
				}
			}
		}

		std::vector<Vec2d> spread_directions(barys.size());
		for (auto [i, j] : degeneracies) {
			Vec2d direction;
			if (tri_area > kSnappingTolerance * kSnappingTolerance && !is_repulsion) {
				direction =
				    findSpreadDirection(grid, internal_points[i], internal_points[j], triangle, tri_normal);
			} else {
				double angle = angle_dis(random_gen_);
				direction = {cos(angle), sin(angle)};
			}
			spread_directions[i] += direction;
			spread_directions[j] -= direction;
		}

		for (size_t i = 0; i < barys.size(); ++i) {
			if (mag2(spread_directions[i]) > 0.0) {
				normalize(spread_directions[i]);
				barys[i] = moveAwayFromTriEdge(barys[i] + 2 * kSnappingTolerance * spread_directions[i]);
			}
		}

		for (size_t i = 0; i < barys.size(); ++i) {
			internal_points[i]->coords = barys[i];
		}
		is_repulsion = true;
	} while (!degeneracies.empty());
}

Vec2d CellSeparator::findSpreadDirection(Grid3DInterface& grid,
                                         const TriangulationPoint* first_inter,
                                         const TriangulationPoint* second_inter,
                                         Mesh3DTriangle* triangle, Vec3d tri_normal) const {
	std::vector<long long> vs1 = grid.get_verts_neighboring_edge(first_inter->element_id);
	std::vector<long long> vs2 = grid.get_verts_neighboring_edge(second_inter->element_id);
	double max_dist2 = -1.0;
	long long maxv1 = -1;
	long long maxv2 = -1;
	for (long long v1 : vs1) {
		Vec3d pos1 = grid.getVertexPosition(v1);
		for (long long v2 : vs2) {
			Vec3d pos2 = grid.getVertexPosition(v2);
			double distance = dist2(pos1, pos2);
			if (distance > max_dist2) {
				max_dist2 = distance;
				maxv1 = v1;
				maxv2 = v2;
			}
		}
	}
	Vec2d proj1 = projectOnTriangle(grid.getVertexPosition(maxv1), triangle, tri_normal);
	Vec2d proj2 = projectOnTriangle(grid.getVertexPosition(maxv2), triangle, tri_normal);
	return proj1 - proj2;
}

Vec2d CellSeparator::projectOnTriangle(Vec3d point, Mesh3DTriangle* triangle,
                                       Vec3d tri_normal) const {
	// Any point on the triangle works, so pick one.
	const Mesh3DVertex* v0 = triangle->getHalfCorner()->getVertex();
	Vec3d normalized_normal = normalized(tri_normal);
	double distance = dot(normalized_normal, point - v0->getCoords());
	Vec3d projection = point - distance * normalized_normal;

	std::vector<Mesh3DVertex*> tri_verts = triangle->getVerts();
	Vec3d v1 = tri_verts[0]->getCoords();
	Vec3d v2 = tri_verts[1]->getCoords();
	Vec3d v3 = tri_verts[2]->getCoords();
	Vec3d normal = cross(v2 - v1, v3 - v1);
	double magnitude = mag2(normal);

	// double alpha = dot(cross(v3 - v2, projection - v2), normal);
	double beta = dot(cross(v1 - v3, projection - v3), normal);
	double gamma = dot(cross(v2 - v1, projection - v1), normal);
	return Vec2d(beta, gamma) / magnitude;
}

void CellSeparator::restoreOriginalIntersectionPositions(
    absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
        edge_to_intersections,
    const absl::flat_hash_map<SortedMeshEdge, std::vector<double>>& edge_to_barys) const {
	for (auto& [mesh_edge, barys] : edge_to_barys) {
		int counter = 0;
		for (GridFaceMeshEdgeIntersection& intersection : edge_to_intersections.at(mesh_edge)) {
			intersection.setBaryCoord(barys[counter]);
			counter++;
		}
	}
}

void CellSeparator::subdivideTriangles(
    Grid3DInterface& grid, Mesh3DInterface& mesh, const GridMeshIntersector& intersector,
    const absl::flat_hash_set<Mesh3DTriangle*>& triangles,
    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
        face_intersections,
    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
        edge_to_intersections) {
	absl::flat_hash_map<MeshEdge, std::vector<Mesh3DHalfCorner*>> all_edges_to_hfcs;
	absl::flat_hash_map<MeshEdge, absl::flat_hash_map<Mesh3DTriangle*, Mesh3DHalfCorner*>>
	    edge_to_original_tri_hfc;
	absl::flat_hash_map<Mesh3DTriangle*, Mesh3DTriangle*> new_to_old_triangles;
	for (Mesh3DTriangle* triangle : triangles) {
		// Unregister triangle from the grid.
		for (const long long cell_id : intersector.findBoundingCellsForTriangle(grid, mesh, triangle)) {
			grid.remove_triangle_from_cell(cell_id, triangle);
		}
		// Record what original half-corners correspond to which edges, so
		// it will be possible to find matching half-corners after subudivisions.
		absl::flat_hash_map<MeshEdge, Mesh3DHalfCorner*> edge_to_hfc =
		    mapEdgeToOriginalHfc(triangle, edge_to_intersections);
		for (const auto& [mesh_edge, hfc] : edge_to_hfc) {
			edge_to_original_tri_hfc[mesh_edge][triangle] = hfc;
		}

		absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint> vertex_to_tri_point;
		std::vector<MeshEdge> segments = extractTriangulationElements(
		    grid, triangle, face_intersections, edge_to_intersections, vertex_to_tri_point);
		std::vector<std::vector<Mesh3DVertex*>> triangle_verts =
		    triangulateTri(grid, triangle, vertex_to_tri_point, segments);
		std::vector<Mesh3DTriangle*> new_triangles = createMeshElements(mesh, triangle, triangle_verts);
		connectInnerHalfcorners(new_triangles, all_edges_to_hfcs);
		for (Mesh3DTriangle* new_tri : new_triangles) {
			new_to_old_triangles[new_tri] = triangle;
			for (const long long cell_id :
			     intersector.findBoundingCellsForTriangle(grid, mesh, new_tri)) {
				grid.addTriangleToCell(cell_id, new_tri);
			}
		}
		assignInsidesOutsides(grid, new_triangles, triangle, face_intersections, edge_to_intersections,
		                      segments);
		addSegmentsToFaceGraph(grid, mesh, triangle, face_intersections, edge_to_intersections);
	}
	connectOuterHalfcorners(new_to_old_triangles, all_edges_to_hfcs, edge_to_original_tri_hfc,
	                        triangles);
	for (Mesh3DTriangle* triangle : triangles) {
		mesh.deleteTriangle(triangle);
	}
}

std::vector<std::vector<Mesh3DVertex*>> CellSeparator::triangulateTri(
    Grid3DInterface& grid, Mesh3DTriangle* triangle,
    const absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint>& vertex_to_tri_point,
    const std::vector<MeshEdge>& segments) {
	// Compute mapping from vertex to consecutive indices.
	absl::flat_hash_map<Mesh3DVertex*, int> vertex_to_index =
	    assignIdxToVertices(vertex_to_tri_point);
	std::vector<Vec2i> segments_idx = convertSegmentsToIdx(segments, vertex_to_index);

	absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint> new_vertex_to_tri_point =
	    vertex_to_tri_point;
	spreadMeshFaceIntersections(grid, triangle, new_vertex_to_tri_point);
	std::vector<Vec2d> vert_coords = convertVerticesToIdx(new_vertex_to_tri_point, vertex_to_index);
	TriangleSubdivision subdivision(vert_coords, segments_idx);
	subdivision.subdivide();
	std::vector<Vec3i> triangles_idx = subdivision.getSubdivTriangles();
	std::vector<Vec2d> new_coords = subdivision.getSubdivPoints();
	if (new_coords.size() == vert_coords.size() + 1) {
		bool is_solvable =
		    solveIntersection(segments_idx, new_coords, subdivision.getSubdivEdges(), triangles_idx);
		std::cout << "ERROR: subdivision produced more vertices than expected." << std::endl;
		assert(is_solvable);
	} else if (new_coords.size() != vert_coords.size()) {
		// TODO: Implement critical exit and resampling if we cannot make any progress.
		std::cout << "ERROR: subdivision produced more vertices than expected." << std::endl;
		assert(false);
	}

	std::vector<Mesh3DVertex*> index_to_vertex = revertVertexMapping(vertex_to_index);
	return convertTriangleIdxToVertices(triangles_idx, index_to_vertex);
}

absl::flat_hash_map<Mesh3DVertex*, int> CellSeparator::assignIdxToVertices(
    const absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint>& vertex_to_tri_point) const {
	absl::flat_hash_map<Mesh3DVertex*, int> mapping;
	for (auto& [vertex, tri_point] : vertex_to_tri_point) {
		mapping.emplace(vertex, mapping.size());
	}
	return mapping;
}

std::vector<Vec2d> CellSeparator::convertVerticesToIdx(
    const absl::flat_hash_map<Mesh3DVertex*, TriangulationPoint>& vertex_to_tri_point,
    const absl::flat_hash_map<Mesh3DVertex*, int>& vertex_to_index) const {
	std::vector<Vec2d> vertices(vertex_to_tri_point.size());
	for (auto& [vertex, tri_point] : vertex_to_tri_point) {
		vertices[vertex_to_index.at(vertex)] = tri_point.coords;
	}
	return vertices;
}

std::vector<Vec2i> CellSeparator::convertSegmentsToIdx(
    const std::vector<MeshEdge>& segments,
    const absl::flat_hash_map<Mesh3DVertex*, int>& vertex_to_index) const {
	std::vector<Vec2i> segments_idx;
	segments_idx.reserve(segments.size());
	for (const MeshEdge& segment : segments) {
		segments_idx.emplace_back(vertex_to_index.at(segment.first),
		                          vertex_to_index.at(segment.second));
	}
	return segments_idx;
}

std::vector<Mesh3DVertex*> CellSeparator::revertVertexMapping(
    const absl::flat_hash_map<Mesh3DVertex*, int>& vertex_to_index) const {
	std::vector<Mesh3DVertex*> index_to_vertex(vertex_to_index.size());
	for (auto [vertex, index] : vertex_to_index) {
		index_to_vertex[index] = vertex;
	}
	return index_to_vertex;
}

std::vector<std::vector<Mesh3DVertex*>> CellSeparator::convertTriangleIdxToVertices(
    const std::vector<Vec3i>& triangles_idx,
    const std::vector<Mesh3DVertex*>& index_to_vertex) const {
	std::vector<std::vector<Mesh3DVertex*>> triangle_verts;
	triangle_verts.reserve(triangles_idx.size());
	for (Vec3i idxs : triangles_idx) {
		triangle_verts.push_back(
		    {index_to_vertex.at(idxs[0]), index_to_vertex.at(idxs[1]), index_to_vertex.at(idxs[2])});
	}
	return triangle_verts;
}

bool CellSeparator::solveIntersection(const std::vector<Vec2i>& segments,
                                      const std::vector<Vec2d>& new_coords,
                                      const std::vector<Vec2i>& new_segments,
                                      std::vector<Vec3i>& triangles_idx) const {
	// New points are added as the last ones in Triangle library.
	int middle_point = new_coords.size() - 1;

	// Find segments that are intersecting.
	absl::flat_hash_set<std::pair<int, int>> created_segments;
	for (Vec2i new_segment : new_segments) {
		created_segments.emplace(min(new_segment), max(new_segment));
	}

	std::vector<Vec2i> intersecting_segments;
	for (Vec2i segment : segments) {
		if (!created_segments.contains({min(segment), max(segment)})) {
			intersecting_segments.push_back(segment);
		}
	}
	assert(intersecting_segments.size() == 2);

	// Check that they are leaves. If not, the intersection is not solvable.
	// TODO: expand the number of cases that can be handled.
	absl::flat_hash_map<int, int> degrees;
	for (Vec2i segment : segments) {
		degrees[segment[0]]++;
		degrees[segment[1]]++;
	}
	std::vector<int> leaves;
	for (Vec2i segment : intersecting_segments) {
		if (degrees[segment[0]] == 1) {
			leaves.push_back(segment[0]);
		}
		if (degrees[segment[1]] == 1) {
			leaves.push_back(segment[1]);
		}
	}
	if (leaves.size() != 2) {
		return false;
	}

	// Swap endpoints in all triangles and
	// Replace the middle point with one of non-leaf segment vertices.
	// This corresponds to deleting all middle triangles and filling-in the hole with two triangles of
	// already correct orientation. We still need to delete the remaining two triangles. These two
	// triangles will be degenerate with two vertices repeating themselves.

	int non_leaf = segments[0][0];
	if (non_leaf == leaves[0] || non_leaf == leaves[1]) {
		non_leaf = segments[0][1];
	}

	std::vector<int> triangles_to_delete;
	for (size_t i = 0; i < triangles_idx.size(); ++i) {
		Vec3i& tri = triangles_idx[i];
		int num_non_leaf = 0;
		for (int c = 0; c < 3; ++c) {
			if (tri[c] == leaves[0]) {
				tri[c] = leaves[1];
			} else if (tri[c] == leaves[1]) {
				tri[c] = leaves[0];
			} else if (tri[c] == middle_point) {
				tri[c] = non_leaf;
			}

			if (tri[c] == non_leaf) {
				num_non_leaf++;
			}
		}
		if (num_non_leaf == 2) {
			triangles_to_delete.push_back(i);
		}
	}
	assert(triangles_to_delete.size() == 2);

	std::reverse(triangles_to_delete.begin(), triangles_to_delete.end());
	for (size_t i = 0; i < triangles_to_delete.size(); ++i) {
		std::swap(triangles_idx[triangles_to_delete[i]], triangles_idx[triangles_idx.size() - 1 - i]);
	}
	triangles_idx.resize(triangles_idx.size() - triangles_to_delete.size());
	return true;
}

absl::flat_hash_map<CellSeparator::MeshEdge, Mesh3DHalfCorner*> CellSeparator::mapEdgeToOriginalHfc(
    Mesh3DTriangle* triangle,
    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
        edge_to_intersections) const {
	Mesh3DHalfCorner* hfc = triangle->getHalfCorner();
	const std::vector<Mesh3DVertex*> vertices = {hfc->getNext()->getVertex(),
	                                             hfc->getPrev()->getVertex(), hfc->getVertex()};

	absl::flat_hash_map<MeshEdge, Mesh3DHalfCorner*> edge_to_original_hfc;
	for (size_t i = 0; i < vertices.size(); ++i) {
		Mesh3DVertex* v1 = vertices[i];
		Mesh3DVertex* v2 = vertices[(i + 1) % vertices.size()];
		Mesh3DVertex* min_v = std::min(v1, v2);
		Mesh3DVertex* max_v = std::max(v1, v2);
		std::vector<Mesh3DVertex*> vertices_on_edge;
		vertices_on_edge.push_back(min_v);
		auto inter_it = edge_to_intersections.find({min_v, max_v});
		if (inter_it != edge_to_intersections.end()) {
			for (const GridFaceMeshEdgeIntersection& intersection : inter_it->second) {
				vertices_on_edge.push_back(intersection.getVertex());
			}
		}
		vertices_on_edge.push_back(max_v);

		bool is_inverted = v1 != min_v;
		for (size_t vert_idx = 1; vert_idx < vertices_on_edge.size(); ++vert_idx) {
			Mesh3DVertex* next_vert = vertices_on_edge[vert_idx - 1];
			Mesh3DVertex* prev_vert = vertices_on_edge[vert_idx];

			if (is_inverted) {
				edge_to_original_hfc[{next_vert, prev_vert}] = hfc->getDual();
				edge_to_original_hfc[{prev_vert, next_vert}] = hfc;
			} else {
				edge_to_original_hfc[{next_vert, prev_vert}] = hfc;
				edge_to_original_hfc[{prev_vert, next_vert}] = hfc->getDual();
			}
		}
		hfc = hfc->getNext();
	}
	return edge_to_original_hfc;
}

std::vector<Mesh3DTriangle*> CellSeparator::createMeshElements(
    Mesh3DInterface& mesh, Mesh3DTriangle* triangle,
    const std::vector<std::vector<Mesh3DVertex*>>& new_triangle_verts) const {
	std::vector<Mesh3DTriangle*> created_triangles;
	Vec2i labels;
	triangle->getLabels(labels[0], labels[1]);
	for (const std::vector<Mesh3DVertex*>& verts : new_triangle_verts) {
		Mesh3DTriangle* new_tri = mesh.makeNewTriangle(verts[0], verts[1], verts[2], labels);
		created_triangles.push_back(new_tri);
	}
	return created_triangles;
}

void CellSeparator::connectInnerHalfcorners(
    const std::vector<Mesh3DTriangle*>& new_triangles,
    absl::flat_hash_map<MeshEdge, std::vector<Mesh3DHalfCorner*>>& all_edges_to_hfcs) const {
	absl::flat_hash_map<MeshEdge, std::vector<Mesh3DHalfCorner*>> current_edge_to_hfcs;
	for (Mesh3DTriangle* triangle : new_triangles) {
		Mesh3DHalfCorner* hfc = triangle->getHalfCorner();
		for (int side = 0; side < 2; ++side, hfc = hfc->getDual()) {
			for (int corner = 0; corner < 3; ++corner, hfc = hfc->getNext()) {
				Mesh3DVertex* v1 = hfc->getNext()->getVertex();
				Mesh3DVertex* v2 = hfc->getPrev()->getVertex();
				current_edge_to_hfcs[{v1, v2}].push_back(hfc);
			}
		}
	}

	for (auto& [mesh_edge, hfcs] : current_edge_to_hfcs) {
		// No non-manifold edges for subdivision of a single triangle.
		assert(hfcs.size() < 3);
		if (hfcs.size() == 1) {
			// This is an edge connected to external triangle. Just save
			// information about it.
			all_edges_to_hfcs[mesh_edge].push_back(hfcs[0]);
		} else if (hfcs.size() == 2) {
			assert(hfcs[0]->getLabel() == hfcs[1]->getDual()->getLabel());
			hfcs[0]->setOppos(hfcs[1]->getDual());
			hfcs[1]->getDual()->setOppos(hfcs[0]);
			hfcs[0]->getDual()->setOppos(hfcs[1]);
			hfcs[1]->setOppos(hfcs[0]->getDual());
		}
	}
}

void CellSeparator::connectOuterHalfcorners(
    const absl::flat_hash_map<Mesh3DTriangle*, Mesh3DTriangle*>& new_to_old_triangle,
    const absl::flat_hash_map<MeshEdge, std::vector<Mesh3DHalfCorner*>>& all_edges_to_hfcs,
    const absl::flat_hash_map<MeshEdge, absl::flat_hash_map<Mesh3DTriangle*, Mesh3DHalfCorner*>>&
        edge_to_original_tri_hfc,
    const absl::flat_hash_set<Mesh3DTriangle*>& subdivided_triangles) const {
	absl::flat_hash_set<MeshEdge> processed_edges;
	for (auto& [mesh_edge, hfcs] : all_edges_to_hfcs) {
		for (Mesh3DHalfCorner* current_hfc : hfcs) {
			Mesh3DTriangle* old_triangle = new_to_old_triangle.at(current_hfc->getTri());
			Mesh3DHalfCorner* original_hfc = edge_to_original_tri_hfc.at(mesh_edge).at(old_triangle);
			Mesh3DTriangle* target_old_tri = original_hfc->getOppos()->getTri();
			Mesh3DHalfCorner* target_hfc = nullptr;
			if (subdivided_triangles.count(target_old_tri) == 0) {
				target_hfc = original_hfc->getOppos();
			} else {
				for (Mesh3DHalfCorner* candidate_hfc :
				     all_edges_to_hfcs.at({mesh_edge.second, mesh_edge.first})) {
					if (new_to_old_triangle.at(candidate_hfc->getTri()) == target_old_tri) {
						target_hfc = candidate_hfc;
						break;
					}
				}
			}
			assert(target_hfc != nullptr);
			assert(current_hfc->getLabel() == target_hfc->getLabel());
			current_hfc->setOppos(target_hfc);
			target_hfc->setOppos(current_hfc);
		}
	}
}

void CellSeparator::assignInsidesOutsides(
    Grid3DInterface& grid, const std::vector<Mesh3DTriangle*>& new_triangles,
    Mesh3DTriangle* old_triangle,
    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
        face_intersections,
    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
        edge_to_intersections,
    const std::vector<MeshEdge>& segments) {
	// Build adjacency map over tri edges.
	absl::flat_hash_map<SortedMeshEdge, std::vector<Mesh3DTriangle*>> edge_to_tris;
	for (Mesh3DTriangle* tri : new_triangles) {
		std::vector<Mesh3DVertex*> verts = tri->getVerts();
		edge_to_tris[{verts[0], verts[1]}].push_back(tri);
		edge_to_tris[{verts[1], verts[2]}].push_back(tri);
		edge_to_tris[{verts[2], verts[0]}].push_back(tri);
	}

	// Find any boundary triangle.
	auto [tri, is_inside] = markBoundaryTriangle(old_triangle, edge_to_intersections, edge_to_tris);
	if (tri == nullptr) {
		std::tie(tri, is_inside) =
		    markTripleLeaf(grid, new_triangles, old_triangle, face_intersections);
	}
	assert(tri != nullptr);
	if (tri == nullptr) {
		std::cout << "Triangle " << old_triangle
		          << "cannot be decomposed into inside / outside components after subdivision."
		          << std::endl;
		return;
	}
	floodLabelForNewTriangles(new_triangles, tri, is_inside, segments);
}

std::tuple<Mesh3DTriangle*, bool> CellSeparator::markBoundaryTriangle(
    Mesh3DTriangle* old_triangle,
    const absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
        edge_to_intersections,
    const absl::flat_hash_map<SortedMeshEdge, std::vector<Mesh3DTriangle*>>& edge_to_tris) const {
	std::vector<Mesh3DVertex*> verts = old_triangle->getVerts();
	for (int i = 0; i < 3; ++i) {
		Mesh3DVertex* v1 = verts[i];
		Mesh3DVertex* v2 = verts[(i + 1) % 3];
		auto it = edge_to_intersections.find({v1, v2});
		if (it == edge_to_intersections.end()) {
			continue;
		}

		const GridFaceMeshEdgeIntersection& intersection = it->second[0];
		const std::vector<Mesh3DTriangle*>& tris =
		    edge_to_tris.at({intersection.getEdgeFirst(), intersection.getVertex()});
		assert(tris.size() == 1);
		return {tris[0], intersection.isFirstInside()};
	}
	return {nullptr, false};
}

std::tuple<Mesh3DTriangle*, bool> CellSeparator::markTripleLeaf(
    Grid3DInterface& grid, const std::vector<Mesh3DTriangle*>& new_triangles,
    Mesh3DTriangle* old_triangle,
    const absl::flat_hash_map<Mesh3DTriangle*, std::vector<GridEdgeMeshFaceIntersection>>&
        face_intersections) const {
	// 1. Extract T1 points
	auto it = face_intersections.find(old_triangle);
	if (it == face_intersections.end()) {
		// There cannot be any triple leaves if there are no T1 intersections.
		return {nullptr, false};
	}
	absl::flat_hash_map<Mesh3DVertex*, long long> t1_vert_to_grid_edge;
	t1_vert_to_grid_edge.reserve(it->second.size());
	for (const GridEdgeMeshFaceIntersection& intersection : it->second) {
		t1_vert_to_grid_edge[intersection.getVertex()] = intersection.getEdgeId();
	}

	// 2. Go through triangles detecting the leaves.
	std::vector<Mesh3DTriangle*> triple_leaves;
	for (Mesh3DTriangle* triangle : new_triangles) {
		bool is_triple = true;
		for (Mesh3DVertex* vertex : triangle->getVerts()) {
			if (!t1_vert_to_grid_edge.contains(vertex)) {
				is_triple = false;
				break;
			}
		}
		if (is_triple) {
			triple_leaves.push_back(triangle);
		}
	}

	// 3. Check orientation of the triple leaves.
	return orientTripleLeaves(grid, triple_leaves, t1_vert_to_grid_edge);
}

void CellSeparator::floodLabelForNewTriangles(const std::vector<Mesh3DTriangle*>& new_triangles,
                                              Mesh3DTriangle* start_tri, bool is_inside,
                                              const std::vector<MeshEdge>& segments) {
	absl::flat_hash_map<SortedMeshEdge, std::vector<Mesh3DTriangle*>> adjacency_map;
	for (Mesh3DTriangle* triangle : new_triangles) {
		std::vector<Mesh3DVertex*> verts = triangle->getVerts();
		for (int i = 0; i < 3; ++i) {
			adjacency_map[{verts[i], verts[(i + 1) % 3]}].push_back(triangle);
		}
	}
	absl::flat_hash_set<SortedMeshEdge> segments_map;
	for (const MeshEdge& segment : segments) {
		segments_map.emplace(segment.first, segment.second);
	}
	absl::flat_hash_set<Mesh3DTriangle*> visited_tris;
	std::queue<std::pair<Mesh3DTriangle*, bool>> processing_queue;
	processing_queue.push({start_tri, is_inside});
	while (!processing_queue.empty()) {
		auto [tri, is_inside] = processing_queue.front();
		processing_queue.pop();
		auto [it, is_inserted] = visited_tris.insert(tri);
		// Skip already visited.
		if (!is_inserted) {
			continue;
		}
		if (is_inside) {
			inside_triangles_.insert(tri);
		} else {
			outside_triangles_.insert(tri);
		}

		std::vector<Mesh3DVertex*> verts = tri->getVerts();
		for (int i = 0; i < 3; ++i) {
			SortedMeshEdge edge{verts[i], verts[(i + 1) % 3]};
			for (Mesh3DTriangle* neigh : adjacency_map.at(edge)) {
				if (visited_tris.contains(neigh)) {
					continue;
				}
				// If we cross the segment, then change the label.
				bool new_is_inside = is_inside ^ segments_map.contains(edge);
				processing_queue.push({neigh, new_is_inside});
			}
		}
	}
}

// given a front face, return true if grid coordinates of its complex cell are larger or equal to
// those of its non-complex cell
bool CellSeparator::isComplexCellOnIncreasingSideOfFrontFace(Grid3DInterface& grid,
                                                             long long face_id) const {
	Vec3ll complex_cell_coords;
	Vec3ll non_complex_cell_coords;
	// retrieve cell coordinates of the complex and non-complex cell
	// adjacent to input face ASK: can it happen that the non-complex cell
	// lives outside of the grid, and if yes, would that cause trouble? It
	// probably can happen, and it's ok if it does, the function should
	// return false.
	for (const long long cell_id : grid.get_cells_neighboring_face(face_id)) {
		if (grid.isCellMarkedComplex(cell_id, Grid3DInterface::ComplexCellType::kBoth)) {
			grid.get_cell_coords(cell_id, complex_cell_coords[0], complex_cell_coords[1],
			                     complex_cell_coords[2]);
		} else {
			grid.get_cell_coords(cell_id, non_complex_cell_coords[0], non_complex_cell_coords[1],
			                     non_complex_cell_coords[2]);
		}
	}
	// compare grid coordinates of the neighbor cells to a vector that's
	// positive in all directions
	return dot(complex_cell_coords - non_complex_cell_coords, Vec3ll{1, 1, 1}) > 0;
}

long long CellSeparator::get_common_cell(Grid3DInterface& grid, long long first_face_id,
                                         long long second_face_id) const {
	absl::flat_hash_map<long long, int> cell_count;
	for (const long long cell_id : grid.get_cells_neighboring_face(first_face_id)) {
		cell_count[cell_id]++;
	}

	for (const long long cell_id : grid.get_cells_neighboring_face(second_face_id)) {
		cell_count[cell_id]++;
	}

	for (const auto& [cell, count] : cell_count) {
		if (count == 2) {
			return cell;
		}
	}
	return -1;
}

long long CellSeparator::orient_grid_edge_against_grid_face(Grid3DInterface& grid,
                                                            long long grid_edge_id,
                                                            long long grid_face_id) const {
	Vec3ll fc;
	long long fo;
	grid.get_face_coords(grid_face_id, fc[0], fc[1], fc[2], fo);

	for (long long vert_id : grid.get_verts_neighboring_edge(grid_edge_id)) {
		Vec3ll vc;
		grid.get_vertex_coords(vert_id, vc[0], vc[1], vc[2]);

		if (vc[fo] > fc[fo]) {
			return 1;
		}

		if (vc[fo] < fc[fo]) {
			return -1;
		}
	}
	return 0;
}

std::vector<long long> CellSeparator::intersect_vectors(const std::vector<long long>& v1,
                                                        const std::vector<long long>& v2) {
	std::vector<long long> result;
	for (const long long e1 : v1) {
		for (const long long e2 : v2) {
			if (e1 == e2) {
				result.push_back(e1);
			}
		}
	}
	return result;
}

// adds the input `intersection` to the input map `mesh_edge_to_intersection`, correctly sets its
// `is_first_inside` and `is_second_inside` flags, and makes sure that the vertex saved as `first`
// has lower pointer value than `second`; this function is only meaningful to call on
// intersections that happen on front faces
void CellSeparator::addIntersectionToMeshEdge(
    Grid3DInterface& grid, const GridFaceMeshEdgeIntersection& intersection,
    absl::flat_hash_map<SortedMeshEdge, std::vector<GridFaceMeshEdgeIntersection>>&
        mesh_edge_to_intersections) const {
	// retrieve data from the input `intersection`
	long long face_id = intersection.getFaceId();
	bool is_first_inside = intersection.isFirstInside();
	bool is_second_inside = intersection.isSecondInside();
	Mesh3DVertex* first = intersection.getEdgeFirst();
	Mesh3DVertex* second = intersection.getEdgeSecond();
	double bary = intersection.getBaryCoord();

	// configure the `is_first_inside` and `is_second_inside` flags to
	// correctly represent whether a mesh vertex is inside the complex
	// region or outside of it; from the complex cell detector,
	// `is_first_inside` is set to true and `is_second_inside` is set to
	// false, while `first` is the mesh vertex that lies inside the cell
	// adjacent to `face_id` that has larger grid coordinates, and `second`
	// is the mesh vertex that lies inside the cell adjacent to `face_id`
	// that has smaller grid coordinates (product order-wise); therefore, we
	// test whether the cell that is adjacent to `face_id`  has larger
	// coordinates is the complex one (in which case we don't do anything),
	// or the non-complex one (in which case we flip the `is_first_inside`
	// and `is_second_inside` flags
	if (!isComplexCellOnIncreasingSideOfFrontFace(grid, face_id)) {
		std::swap(is_first_inside, is_second_inside);
	}

	// rearrange how the two mesh edge vertices are assigned to `first` and
	// `second`, so that the vertex assigned to `first` is the one with a
	// smaller poitner value; `is_first_inside` and `is_second_inside`, as
	// well as the barycentric coordinate, are flipped, and therefore remain
	// valid
	// POINTER: consider using mesh indices instead of pointer values
	if (first > second) {
		std::swap(is_first_inside, is_second_inside);
		std::swap(first, second);
		bary = 1.0 - bary;
	}
	// push the `GridFaceMeshEdgeIntersection` object into the return map
	mesh_edge_to_intersections[{first, second}].emplace_back(
	    face_id, first, is_first_inside, second, is_second_inside, bary, intersection.getVertex());
}

absl::flat_hash_set<SortedMeshEdge> CellSeparator::getGraphEdges(
    Grid3DInterface& grid, const std::vector<long long>& front_faces) const {
	absl::flat_hash_set<SortedMeshEdge> graph_edges;
	for (long long face_id : front_faces) {
		for (const auto& [edge, tri] : grid.getGraphOnFace(face_id)) {
			graph_edges.emplace(edge.first, edge.second);
		}
	}
	return graph_edges;
}

bool CellSeparator::markBadFaceGraph(Grid3DInterface& grid) {
	bool has_bad_faces = false;
	size_t num_failed = 0;
	for (long long face_id : grid.getFrontFacesVector()) {
		std::vector<Mesh3DVertex*> edge_vertices;
		for (long long edge_id : grid.get_edges_neighboring_face(face_id)) {
			std::vector<Mesh3DVertex*> vertices = grid.get_mesh_vertices_on_edge(edge_id);
			edge_vertices.insert(edge_vertices.end(), vertices.begin(), vertices.end());
		}

		absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DVertex*>> graph_edges;
		for (const auto& [edge, tri] : grid.getGraphOnFace(face_id)) {
			graph_edges[edge.first].insert(edge.second);
			graph_edges[edge.second].insert(edge.first);
		}

		absl::flat_hash_map<Mesh3DVertex*, int> vertex_to_component;
		for (size_t i = 0; i < edge_vertices.size(); ++i) {
			std::queue<std::pair<Mesh3DVertex*, int>> current_nodes;
			current_nodes.push({edge_vertices[i], i});
			while (!current_nodes.empty()) {
				auto [vertex, component] = current_nodes.front();
				current_nodes.pop();

				auto [it, is_inserted] = vertex_to_component.try_emplace(vertex, component);
				if (!is_inserted) {
					// Already visited the vertex.
					continue;
				}

				auto neigh_it = graph_edges.find(vertex);
				if (neigh_it == graph_edges.end()) {
					continue;
				}
				for (Mesh3DVertex* neighbour : neigh_it->second) {
					if (vertex_to_component.find(neighbour) == vertex_to_component.end()) {
						current_nodes.push({neighbour, component});
					}
				}
			}
		}

		absl::flat_hash_map<int, std::vector<Mesh3DVertex*>> components_to_ends;
		for (Mesh3DVertex* edge_vertex : edge_vertices) {
			components_to_ends[vertex_to_component.at(edge_vertex)].push_back(edge_vertex);
		}

		for (const auto& [component, verts] : components_to_ends) {
			if (verts.size() < 2) {
				failed_separation_faces_.insert(face_id);
				num_failed++;
				has_bad_faces = true;
				break;
			}
		}
	}
	if (num_failed > 0) {
		std::cout << "No closed components found on " << num_failed
		          << " faces. Marking them as complex." << std::endl;
	}
	return has_bad_faces;
}

bool CellSeparator::check_grid_graph(Grid3DInterface& grid) const {
	absl::flat_hash_map<Mesh3DVertex*, int> vertex_degree;
	for (long long face_id : grid.getFrontFacesVector()) {
		for (const auto& [edge, tri] : grid.getGraphOnFace(face_id)) {
			if (tri == nullptr) {
				return false;
			}

			if (inside_triangles_.count(tri)) {
				return false;
			}

			if (outside_triangles_.count(tri) == 0) {
				return false;
			}

			vertex_degree[edge.first] += 1;
			vertex_degree[edge.second] += 1;
		}
	}

	// Check that the graph has no leaves. Graph must form a collection of
	// loops. It does not have to be Eulerian, though, because non-manifold
	// edges can cross complex faces.
	for (auto [vert, degree] : vertex_degree) {
		if (degree < 2) {
			return false;
		}
	}
	return true;
}
