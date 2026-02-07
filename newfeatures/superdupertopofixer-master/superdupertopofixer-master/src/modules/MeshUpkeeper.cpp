/* MeshUpkeeper.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the implementation file for the module that performs mesh upkeep.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "MeshUpkeeper.h"

#include <cmath>
#include <limits>
#include <queue>
#include <unordered_map>
#include <unordered_set>

#include "../datastructures/Mesh3DHalfCorner.h"
#include "../datastructures/Mesh3DTriangle.h"
#include "../utilities/QueueSet.h"
#include "../utilities/util.h"
#include "absl/container/flat_hash_set.h"

//------------------------------------------------------------
// constructors
//------------------------------------------------------------

// default constructor
MeshUpkeeper::MeshUpkeeper(const TopoFixerSettings& settings)
    : settings(&settings),
      t1_resolver_(settings),
      improve_only_mcs_(settings.improve_only_mc_tris),
      min_edge_length_(settings.min_edge_length_rel_to_grid),
      max_edge_length_(settings.max_edge_length_rel_to_grid),
      kSlimTriangleTolerance(settings.slim_triangle_tolerance),
      kMaxAngleSizeRad(settings.max_angle_size_deg / 180.0 * M_PI),
      kCosMaxAngleSize(cos(settings.max_angle_size_deg / 180.0 * M_PI)) {}

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// function that coordinates the run of the mesh upkeeper module

int MeshUpkeeper::run(Mesh3DInterface& mesh, Grid3DInterface& grid,
                      GridMeshIntersector& intersector, int orientation) {
	int return_value = 0;

	assert(mesh.runMeshConsistencyChecks() == 0);
	t1_resolver_.resolveVertices(mesh, grid, mesh.ListVertices());
	assert(mesh.runMeshConsistencyChecks() == 0);

	// smooth mesh in complex region
	if (settings->run_smoothing) {
		absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DVertex*>> vertex_adjacency_map =
		    buildComplexRegionMeshVertexAdjacency(mesh, grid);
		std::vector<Mesh3DVertex*> smoothed_verts;
		smoothed_verts.reserve(vertex_adjacency_map.size());
		for (auto& [vert, neighs] : vertex_adjacency_map) {
			smoothed_verts.push_back(vert);
		}
		nc_smoother_.smooth(mesh, smoothed_verts, kNumSmoothingIters / 2);
		for (auto& [vert, neighs] : nc_smoother_.buildCurves(mesh, smoothed_verts)) {
			vertex_adjacency_map.erase(vert);
		}
		smoother_.smooth(vertex_adjacency_map, kNumSmoothingIters);
	}

	mesh.clearEdgeCollapseCounters();

	absl::flat_hash_set<Mesh3DVertex*> candidates;
	if (improve_only_mcs_) {
		absl::flat_hash_set<Mesh3DTriangle*> mc_tris = createdTriangles(mesh);
		for (Mesh3DTriangle* tri : mc_tris) {
			for (Mesh3DVertex* v : tri->getVerts()) {
				candidates.insert(v);
			}
		}
		setMCImprovementBoundary(mesh, mc_tris);
	} else {
		candidates = mesh.ListVertices();
	}

	absl::flat_hash_set<Mesh3DVertex*> next_candidates;
	absl::flat_hash_set<Mesh3DVertex*> op_candidates;
	for (int i = 0; i < 5; ++i) {
		op_candidates = removeValenceThreeVerts(mesh, candidates);
		candidates.insert(op_candidates.begin(), op_candidates.end());
		next_candidates.insert(op_candidates.begin(), op_candidates.end());
		removeNonexistentVertices(mesh, candidates);

		op_candidates = splitEdges(mesh, candidates);
		candidates.insert(op_candidates.begin(), op_candidates.end());
		next_candidates.insert(op_candidates.begin(), op_candidates.end());
		removeNonexistentVertices(mesh, candidates);

		op_candidates = flipEdges(mesh, candidates);
		candidates.insert(op_candidates.begin(), op_candidates.end());
		next_candidates.insert(op_candidates.begin(), op_candidates.end());
		removeNonexistentVertices(mesh, candidates);
		if (settings->verbosity >= 2) {
			std::cout << "Flips done" << std::endl;
		}

		op_candidates = collapseSlimTriangles(mesh, candidates);
		candidates.insert(op_candidates.begin(), op_candidates.end());
		next_candidates.insert(op_candidates.begin(), op_candidates.end());
		removeNonexistentVertices(mesh, candidates);
		if (settings->verbosity >= 2) {
			std::cout << "Slim done" << std::endl;
		}

		t1_resolver_.resolveVertices(mesh, grid, candidates);
		candidates = next_candidates;
		next_candidates.clear();
		removeNonexistentVertices(mesh, candidates);

		assert(mesh.runMeshConsistencyChecks() == 0);

		if (candidates.empty()) {
			break;
		}
	}

	auto consistency_check_type = settings->run_input_mesh_consistency_tests;
	if (consistency_check_type == TopoFixerSettings::InputMeshConsistencyTests::All ||
	    consistency_check_type == TopoFixerSettings::InputMeshConsistencyTests::Critical) {
		mesh.runMeshConsistencyChecks();
	}

	std::cout << "-edge collapses canceled due to T1 retraction: "
	          << mesh.getT1RetractionEdgeCollapseCancel() << '\n';
	std::cout << "-edge collapses canceled due to tetrahedron configuration: "
	          << mesh.getTetrahedronEdgeCollapseCancel() << '\n';
	std::cout << "-edge collapses canceled due to in plane flip: "
	          << mesh.getInPlaneFlipEdgeCollapseCancel() << '\n';
	std::cout << "-edge collapses canceled due to violating Hoppe's criterion: "
	          << mesh.getHoppeCriterionEdgeCollapseCancel() << '\n';
	std::cout << "-edge collapses canceled due to touching two region valence 4 vertices: "
	          << mesh.getDoubleFourValenceEdgeCollapseCancel() << '\n';
	std::cout << "-edge collapses canceled due to candidate edge not being covered: "
	          << mesh.getCandidateCoveringEdgeCollapseCancel() << '\n';

	if (settings->verbosity >= 2) {
		std::cout << "Min and max mesh edge lengths: " << mesh.getMinEdgeLength() << " "
		          << mesh.getMaxEdgeLength() << std::endl;
		std::cout << "Requested min and max mesh edge lengths: " << min_edge_length_ << " "
		          << max_edge_length_ << std::endl;
		std::cout << "Num vertices: " << mesh.ListVertices().size() << std::endl;
		std::cout << "Num triangles: " << mesh.ListTriangles().size() << std::endl;
	}
	if (settings->verbosity >= 1) {
		std::cout << "-mesh upkeeper finished with return value " << return_value << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return return_value;
}

int MeshUpkeeper::runPreprocess(Mesh3DInterface& mesh, Grid3DInterface& grid) const {
	int return_value = 0;
	t1_resolver_.resolveVertices(mesh, grid, mesh.ListVertices());

	absl::flat_hash_set<Mesh3DVertex*> candidates = mesh.ListVertices();
	absl::flat_hash_set<Mesh3DVertex*> next_candidates;
	absl::flat_hash_set<Mesh3DVertex*> op_candidates;
	for (int i = 0; i < 5; ++i) {
		candidates = splitEdges(mesh, candidates);
		removeNonexistentVertices(mesh, candidates);
		if (candidates.empty()) {
			break;
		}
	}

	auto consistency_check_type = settings->run_input_mesh_consistency_tests;
	if (consistency_check_type == TopoFixerSettings::InputMeshConsistencyTests::All ||
	    consistency_check_type == TopoFixerSettings::InputMeshConsistencyTests::Critical) {
		mesh.runMeshConsistencyChecks();
	}

	if (settings->verbosity >= 2) {
		std::cout << "Min and max mesh edge lengths: " << mesh.getMinEdgeLength() << " "
		          << mesh.getMaxEdgeLength() << std::endl;
		std::cout << "Requested min and max mesh edge lengths: " << min_edge_length_ << " "
		          << max_edge_length_ << std::endl;
	}
	if (settings->verbosity >= 1) {
		std::cout << "-mesh preprocessing finished with return value " << return_value << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	return return_value;
}

absl::flat_hash_set<Mesh3DVertex*> MeshUpkeeper::removeValenceThreeVerts(
    Mesh3DInterface& mesh, const absl::flat_hash_set<Mesh3DVertex*>& candidates) const {
	absl::flat_hash_set<Mesh3DVertex*> local_candidates = candidates;
	absl::flat_hash_set<Mesh3DVertex*> all_changed_verts;
	bool is_progress_made = false;
	do {
		std::vector<std::pair<Mesh3DTriangle*, std::pair<Mesh3DVertex*, Mesh3DVertex*>>>
		    edges_to_collapse;
		for (Mesh3DVertex* vertex : local_candidates) {
			if (!mesh.isVertexInMesh(vertex)) {
				continue;
			}
			absl::flat_hash_set<Mesh3DTriangle*> tris = mesh.getTrianglesAroundVertex(vertex);
			if (tris.size() != 3) {
				continue;
			}
			// Does not matter which one gets collapsed, choose any edge.
			Mesh3DTriangle* tri = *tris.begin();
			Mesh3DVertex* neigh_vert = tri->getHalfCorner()->getVertex();
			if (neigh_vert == vertex) {
				neigh_vert = tri->getHalfCorner()->getNext()->getVertex();
			}
			edges_to_collapse.push_back({tri, {neigh_vert, vertex}});
		}
		local_candidates.clear();

		std::cout << "Valence three verts: " << edges_to_collapse.size() << std::endl;
		int counter = 0;
		for (auto [tri, edge] : edges_to_collapse) {
			absl::flat_hash_set<Mesh3DVertex*> updated_verts =
			    mesh.edgeCollapseWithUpdatedVerts(tri, edge.first, edge.second, edge.first->getCoords());
			local_candidates.insert(updated_verts.begin(), updated_verts.end());
			all_changed_verts.insert(updated_verts.begin(), updated_verts.end());
			counter += !updated_verts.empty();
		}
		std::cout << "Collapsed valence three vertices: " << counter << std::endl;
		is_progress_made = !local_candidates.empty();
	} while (is_progress_made);
	removeNonexistentVertices(mesh, all_changed_verts);
	return all_changed_verts;
}

absl::flat_hash_set<Mesh3DVertex*> MeshUpkeeper::collapseSlimTriangles(
    Mesh3DInterface& mesh, const absl::flat_hash_set<Mesh3DVertex*>& candidates) const {
	absl::flat_hash_set<Mesh3DVertex*> local_candidates = candidates;
	absl::flat_hash_set<Mesh3DVertex*> all_changed_vertices;
	bool is_progress_made = false;
	do {
		// Find new slim edges that can still be collapsed.
		std::vector<ImprovementMeshEdge> collapse_candidates;
		for (auto& [edge, hfc] : candidateEdges(mesh, local_candidates)) {
			if (shouldBeCollapsed(mesh, hfc)) {
				collapse_candidates.push_back(
				    {edge, hfc, dist2(edge.getSmaller()->getCoords(), edge.getLarger()->getCoords())});
			}
		}
		local_candidates.clear();

		std::sort(collapse_candidates.begin(), collapse_candidates.end());

		// Remove short edges.
		int successes = 0;
		int failures = 0;
		for (ImprovementMeshEdge& candidate : collapse_candidates) {
			Mesh3DHalfCorner* hfc = candidate.getHalfCorner();
			if (!mesh.isHalfCornerInMesh(hfc)) {
				continue;
			}
			if (!shouldBeCollapsed(mesh, hfc)) {
				continue;
			}
			// After this point candidate `edge` might have wrong vertices. Half-corner, on the other
			// hand, should be pointing to the correct mesh element.
			Mesh3DVertex* v1 = hfc->getNext()->getVertex();
			Mesh3DVertex* v2 = hfc->getPrev()->getVertex();
			Mesh3DTriangle* triangle = hfc->getTri();
			absl::flat_hash_set<Mesh3DVertex*> updated_verts =
			    mesh.edgeCollapseWithUpdatedVerts(triangle, v1, v2, getCollapseCoords(mesh, v1, v2));
			local_candidates.insert(updated_verts.begin(), updated_verts.end());
			all_changed_vertices.insert(updated_verts.begin(), updated_verts.end());
			successes += !updated_verts.empty();
			failures += updated_verts.empty();
		}
		removeNonexistentVertices(mesh, local_candidates);
		std::cout << "Edges collapse successes: " << successes << "\n";
		std::cout << "Edges collapse failures: " << failures << std::endl;
		is_progress_made = !local_candidates.empty();
	} while (is_progress_made);
	removeNonexistentVertices(mesh, all_changed_vertices);
	return all_changed_vertices;
}

absl::flat_hash_set<Mesh3DVertex*> MeshUpkeeper::splitEdges(
    Mesh3DInterface& mesh, const absl::flat_hash_set<Mesh3DVertex*>& candidates) const {
	absl::flat_hash_set<Mesh3DVertex*> local_candidates = candidates;
	absl::flat_hash_set<Mesh3DVertex*> all_changed_vertices;
	bool is_progress_made = false;
	int num_iters = 0;
	do {
		std::vector<ImprovementMeshEdge> split_candidates;
		for (const auto& [edge, hfc] : candidateEdges(mesh, local_candidates)) {
			if (shouldSplitEdge(mesh, hfc)) {
				split_candidates.push_back(
				    {edge, hfc, dist2(edge.getSmaller()->getCoords(), edge.getLarger()->getCoords())});
			}
		}
		local_candidates.clear();

		// Sort in reverse order of lengths.
		std::sort(split_candidates.begin(), split_candidates.end(), std::greater<>());

		for (ImprovementMeshEdge& candidate : split_candidates) {
			candidate.fixHalfCorner(mesh);

			Mesh3DHalfCorner* hfc = candidate.getHalfCorner();
			SortedMeshEdge edge = candidate.getEdge();
			if (!shouldSplitEdge(mesh, hfc)) {
				continue;
			}
			absl::flat_hash_set<Mesh3DVertex*> updated_verts = mesh.edgeSubdivisionWithUpdatedVerts(
			    hfc->getTri(), edge.getSmaller(), edge.getLarger(),
			    mesh.pVertCoords(edge.getSmaller(), edge.getLarger(), 0.5));
			local_candidates.insert(updated_verts.begin(), updated_verts.end());
			all_changed_vertices.insert(updated_verts.begin(), updated_verts.begin());
		}
		std::cout << "Subdivided triangles count: " << local_candidates.size() << std::endl;
		is_progress_made = !local_candidates.empty();
		num_iters += 1;
	} while (is_progress_made && num_iters < 10);
	removeNonexistentVertices(mesh, all_changed_vertices);
	return all_changed_vertices;
}

absl::flat_hash_set<Mesh3DVertex*> MeshUpkeeper::flipEdges(
    Mesh3DInterface& mesh, const absl::flat_hash_set<Mesh3DVertex*>& candidates) const {
	absl::flat_hash_set<Mesh3DVertex*> all_changed_vertices;
	QueueSet<Mesh3DVertex*> verts_to_process;
	for (Mesh3DVertex* candidate : candidates) {
		verts_to_process.insert(candidate);
	}

	while (!verts_to_process.empty()) {
		Mesh3DVertex* vert = verts_to_process.front();
		verts_to_process.pop();

		Mesh3DHalfCorner* flip_hfc = nullptr;
		for (Mesh3DHalfCorner* hfc : mesh.getHalfCornersAtVertex(vert)) {
			if (shouldBeFlipped(mesh, hfc)) {
				flip_hfc = hfc;
				break;
			}
		}
		if (flip_hfc == nullptr) {
			continue;
		}

		absl::flat_hash_set<Mesh3DVertex*> updated_verts = mesh.edgeFlipWithUpdatedVerts(
		    flip_hfc->getTri(), flip_hfc->getNext()->getVertex(), flip_hfc->getPrev()->getVertex());

		for (Mesh3DVertex* uv : updated_verts) {
			verts_to_process.insert(uv);
		}

		all_changed_vertices.insert(updated_verts.begin(), updated_verts.end());
	}
	removeNonexistentVertices(mesh, all_changed_vertices);
	return all_changed_vertices;
}

bool MeshUpkeeper::shouldBeFlipped(Mesh3DInterface& mesh, Mesh3DHalfCorner* hfc) const {
	if (mesh.isEdgeNonmanifold(hfc)) {
		return false;
	}
	double cos1 = mesh.getAngleCos(hfc);
	// Degenerate case, do not flip.
	if (cos1 == -2) {
		return false;
	}

	Mesh3DHalfCorner* oppos_hfc = hfc->getOppos();
	assert(oppos_hfc);

	double cos2 = mesh.getAngleCos(oppos_hfc);
	// Degenerate case, do not flip.
	if (cos2 == -2) {
		return false;
	}

	// Angles less than 90 degrees each.
	if (cos1 >= 0 && cos2 >= 0) {
		return false;
	}

	// The sum of angles is less than 180 degrees.
	if (cos1 * cos2 <= 0 && (cos1 == cos2 || cos1 + cos2 >= 0)) {
		return false;
	}

	const Mesh3DTriangle* common_tri =
	    mesh.getCommonTriangle(hfc->getVertex(), oppos_hfc->getVertex());

	// If there is a common triangle, then its an ear case, do not flip.
	return common_tri == nullptr;
}

void MeshUpkeeper::clearState() { t1_resolver_ = T1Resolver(*settings); }

void MeshUpkeeper::removeNonexistentVertices(Mesh3DInterface& mesh,
                                             absl::flat_hash_set<Mesh3DVertex*>& vertices) const {
	auto it = vertices.begin();
	while (it != vertices.end()) {
		if (mesh.isVertexInMesh(*it)) {
			++it;
		} else {
			vertices.erase(it++);
		}
	}
}

absl::flat_hash_set<Mesh3DTriangle*> MeshUpkeeper::createdTriangles(Mesh3DInterface& mesh) const {
	absl::flat_hash_set<Mesh3DTriangle*> result = mesh.getMCTriangles();
	absl::flat_hash_set<Mesh3DTriangle*> t1s = mesh.getT1Triangles();
	result.insert(t1s.begin(), t1s.end());
	t1s = mesh.getT1HFTriangles();
	result.insert(t1s.begin(), t1s.end());
	absl::erase_if(result,
	               [&mesh](const auto& triangle) { return !mesh.isTriangleInMesh(triangle); });
	return result;
}

void MeshUpkeeper::setMCImprovementBoundary(Mesh3DInterface& mesh,
                                            const absl::flat_hash_set<Mesh3DTriangle*>& mc_tris) {
	absl::flat_hash_set<Mesh3DTriangle*> allowed_tris;
	std::queue<Mesh3DTriangle*> tri_front;

	// We save MC triangles and their immediate triangle neighbours for processing. This allows
	// to improve the triangle quality around the complex front faces where its most needed. All other
	// triangles will be disallowed.
	for (Mesh3DTriangle* tri : mc_tris) {
		for (Mesh3DVertex* v : tri->getVerts()) {
			for (Mesh3DTriangle* neigh_tri : mesh.getTrianglesAroundVertex(v)) {
				allowed_tris.insert(neigh_tri);
				if (!mc_tris.contains(neigh_tri)) {
					tri_front.push(neigh_tri);
				}
			}
		}
	}

	while (!tri_front.empty()) {
		Mesh3DTriangle* tri = tri_front.front();
		tri_front.pop();
		for (Mesh3DVertex* v : tri->getVerts()) {
			for (Mesh3DTriangle* neigh_tri : mesh.getTrianglesAroundVertex(v)) {
				if (!allowed_tris.contains(neigh_tri)) {
					tris_to_avoid_.insert(neigh_tri);
				}
			}
		}
	}
}

bool MeshUpkeeper::isEdgeAllowed(Mesh3DInterface& mesh, Mesh3DHalfCorner* hfc) const {
	std::vector<Mesh3DHalfCorner*> around_corners;
	mesh.walkAroundEdge(hfc, around_corners);
	for (Mesh3DHalfCorner* around_corner : around_corners) {
		if (tris_to_avoid_.contains(around_corner->getTri())) {
			return false;
		}
	}
	return true;
}

absl::flat_hash_map<SortedMeshEdge, Mesh3DHalfCorner*> MeshUpkeeper::candidateEdges(
    Mesh3DInterface& mesh, const absl::flat_hash_set<Mesh3DVertex*>& candidate_vertices) const {
	absl::flat_hash_map<SortedMeshEdge, Mesh3DHalfCorner*> candidate_edges;
	for (Mesh3DVertex* vertex : candidate_vertices) {
		for (Mesh3DHalfCorner* hfc : mesh.getEdgesAroundVertex(vertex)) {
			if (improve_only_mcs_ && !isEdgeAllowed(mesh, hfc)) {
				continue;
			}
			candidate_edges.try_emplace({hfc->getPrev()->getVertex(), hfc->getNext()->getVertex()}, hfc);
		}
	}
	return candidate_edges;
}

bool MeshUpkeeper::shouldSplitEdge(Mesh3DInterface& mesh, Mesh3DHalfCorner* hfc) const {
	const Mesh3DVertex* v1 = hfc->getNext()->getVertex();
	const Mesh3DVertex* v2 = hfc->getPrev()->getVertex();
	Vec3d c1 = v1->getCoords();
	Vec3d c2 = v2->getCoords();
	double cur_len = dist(c1, c2);
	if (cur_len < 2 * min_edge_length_) {
		return false;
	}

	if (cur_len > max_edge_length_) {
		return true;
	}

	double min_cos = 2.0;
	double min_len = cur_len;
	std::vector<Mesh3DHalfCorner*> around_hfcs;
	mesh.walkAroundEdge(hfc, around_hfcs);
	for (Mesh3DHalfCorner* around_hfc : around_hfcs) {
		if (around_hfc->getTri()->getArea() < 1e-10) {
			return false;
		}
		const Mesh3DVertex* v3 = around_hfc->getVertex();
		min_len = std::min(min_len, dist(v3->getCoords(), c1));
		min_len = std::min(min_len, dist(v3->getCoords(), c2));
		min_cos = std::min(mesh.getAngleCos(around_hfc), min_cos);
	}
	return cur_len > 3 * min_len || (min_cos < kCosMaxAngleSize && min_cos > -2);
}

bool MeshUpkeeper::shouldBeCollapsed(Mesh3DInterface& mesh, Mesh3DHalfCorner* hfc) const {
	Mesh3DVertex* v1 = hfc->getNext()->getVertex();
	Mesh3DVertex* v2 = hfc->getPrev()->getVertex();
	double current_len = dist(v1->getCoords(), v2->getCoords());
	return current_len < min_edge_length_;
}

Vec3d MeshUpkeeper::getCollapseCoords(Mesh3DInterface& mesh, Mesh3DVertex* v1,
                                      Mesh3DVertex* v2) const {
	bool is_v1_manifold = mesh.areEdgesAroundManifold(v1);
	bool is_v2_manifold = mesh.areEdgesAroundManifold(v2);
	if (!is_v1_manifold && is_v2_manifold) {
		return v1->getCoords();
	}
	if (is_v1_manifold && !is_v2_manifold) {
		return v2->getCoords();
	}
	return mesh.pVertCoords(v1, v2, 0.5);
}

absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DVertex*>>
MeshUpkeeper::buildComplexRegionMeshVertexAdjacency(Mesh3DInterface& mesh,
                                                    Grid3DInterface& grid) const {
	absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DVertex*>> vertex_adjacency_map;
	// iterate over MC triangles, for each of its vertices save the other two vertices as its
	// neighbors
	for (const Mesh3DTriangle* triangle : createdTriangles(mesh)) {
		std::vector<Mesh3DVertex*> verts = triangle->getVerts();
		for (int i = 0; i < 3; ++i) {
			vertex_adjacency_map[verts[i]].insert(verts[(i + 1) % 3]);
			vertex_adjacency_map[verts[i]].insert(verts[(i + 2) % 3]);
		}
	}

	for (const long long& face : grid.getFrontFacesSet()) {
		const auto& graph_on_face = grid.getGraphOnFace(face);
		for (const auto& [edge, triangle] : graph_on_face) {
			vertex_adjacency_map.erase(edge.first);
			vertex_adjacency_map.erase(edge.second);
		}
	}

	return vertex_adjacency_map;
}

ImprovementMeshEdge::ImprovementMeshEdge(SortedMeshEdge edge, Mesh3DHalfCorner* hfc, double length)
    : edge_(edge), hfc_(hfc), length_(length) {}

void ImprovementMeshEdge::fixHalfCorner(Mesh3DInterface& mesh) {
	SortedMeshEdge current_edge{hfc_->getNext()->getVertex(), hfc_->getPrev()->getVertex()};
	// If the half-corner points to correct edge, nothing needs to be done.
	if (current_edge == edge_) {
		return;
	}

	// Find half-corner in the new triangle that contains this edge.
	Mesh3DTriangle* common_tri = mesh.getCommonTriangle(edge_.getSmaller(), edge_.getLarger());
	assert(common_tri && "Candidate mesh edge does not have a common triangle.");
	hfc_ = common_tri->getHalfCorner();
	while (hfc_->getVertex() == edge_.getSmaller() || hfc_->getVertex() == edge_.getLarger()) {
		hfc_ = hfc_->getNext();
	}
}