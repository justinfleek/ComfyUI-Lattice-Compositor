/* Grid3DSparseCubical.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov 2021
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "Grid3DSparseCubical.h"

#include <algorithm>
#include <unordered_set>

//------------------------------------------------------------
// constructors
//------------------------------------------------------------

// default constructor
Grid3DSparseCubical::Grid3DSparseCubical()
    : is_complex_cell_front_updated_(false),
      material_encoder({{0, 0}}),
      lowest_non_used_material(1),
      material_decoder({{0, 0}}),
      sparse_rays_(3),
      is_sparse_rays_lattice_updated(3, false) {}

//------------------------------------------------------------
// functions
//------------------------------------------------------------
void Grid3DSparseCubical::setVertexMaterial(const long long vertex_id, SparseVector<int> material) {
	per_vertex_material_labels_[vertex_id] = material;
}

SparseVector<int> Grid3DSparseCubical::getVertexMaterial(const long long vertex_id) {
	if (per_vertex_material_labels_.empty()) {
		SparseVector<int> result;
		result.assign(0, 1);
		return result;
	}
	// If material is explicitly assigned, use it.
	const auto find_it = per_vertex_material_labels_.find(vertex_id);
	if (find_it != per_vertex_material_labels_.end()) {
		return find_it->second;
	}

	// Pick arbitrary direction for the ray, since the labels should not depend on direction.
	const SparseRaysContainer& sparse_rays = getSparseRays(/*orientation=*/0);
	// If the ray is empty, we're in the global outside.
	auto ray_it = sparse_rays.find_ray(vertex_id);
	if (ray_it == sparse_rays.end()) {
		SparseVector<int> result;
		result.assign(0, 1);
		return result;
	}

	// Find the closest neighbour towards the ray origin to borrow its material.
	auto ray_begin_it = ray_it->second.begin();
	auto ray_end_it = ray_it->second.end();
	int orientation = sparse_rays.get_orientation();
	auto comp = [orientation](const Vec3ll vertex_coords, const SparseRaysContainer::Point& point) {
		return vertex_coords[orientation] < point.coord_on_ray;
	};
	Vec3ll vertex_coords;
	get_vertex_coords(vertex_id, vertex_coords[0], vertex_coords[1], vertex_coords[2]);
	auto ray_pos_it = std::upper_bound(ray_begin_it, ray_end_it, vertex_coords, comp);

	// No neighbours on the way to ray origin. We are in the global outside.
	if (ray_pos_it == ray_begin_it) {
		SparseVector<int> result;
		result.assign(0, 1);
		return result;
	}
	ray_pos_it--;
	return per_vertex_material_labels_.at(ray_pos_it->element);
}

void Grid3DSparseCubical::setVertexMaterialVectors(
    absl::flat_hash_map<long long, SparseVector<int>> per_vertex_materials) {
	per_vertex_material_labels_ = std::move(per_vertex_materials);
}

// returns a unit vector corresponding to `orientation`
Vec3d Grid3DSparseCubical::getRayDirection(long long orientation) {
	Vec3d direction(0.0);
	direction[orientation] = 1.0;
	return direction;
}

//-----------------------------------------------------------------------
// mesh label <-> grid label conversion functions
//-----------------------------------------------------------------------

// transforms a Vec2i of mesh labels to a Vec2i of grid labels using `material_encoder`, if new mesh
// labels are encountered, inserts them into `material_encoder`
Vec2i Grid3DSparseCubical::convertMeshLabelsToGridLabels(Vec2i mesh_labels) {
	Vec2i result;
	for (int i = 0; i < 2; ++i) {
		// attempt to insert into `material_encoder` the pair {mesh label,lowest non used material}
		auto insert_result = material_encoder.insert({mesh_labels[i], lowest_non_used_material});
		// if the pair was indeed inserted, i.e. there was no grid label assigned to this mesh label...
		if (insert_result.second == true) {
			lowest_non_used_material++;
		}
		// assign to `result[i]` the value associated to `mesh_labels[i]` in `material_encoder`
		result[i] = insert_result.first->second;
	}
	return result;
}

// constructs `material_decoder` (transforms grid labels to mesh labels), by inverting
// `material_encoder`
void Grid3DSparseCubical::constructMaterialDecoder() {
	for (const auto& it : material_encoder) {
		material_decoder[it.second] = it.first;
	}
}

// converts a grid label to a mesh label using `material_decoder`
int Grid3DSparseCubical::convertGridLabelToMeshLabel(int grid_label) {
	auto find_it = material_decoder.find(grid_label);
	if (find_it == material_decoder.end()) {
		std::cerr << "Material id: " << grid_label << " cannot be decoded into a mesh label."
		          << std::endl;
		return -1;
	}
	return find_it->second;
};

// converts a grid label pair to a mesh label pair using `material_decoder`
Vec2i Grid3DSparseCubical::convertGridLabelToMeshLabel(Vec2i grid_labels) {
	return Vec2i(convertGridLabelToMeshLabel(grid_labels[0]),
	             convertGridLabelToMeshLabel(grid_labels[1]));
};

//-----------------------------------------------------------------------

// registers input `triangle` as potentially intersecting the cell with input `cell_id`
void Grid3DSparseCubical::addTriangleToCellWithoutFlaggingRays(const long long cell_id,
                                                               Mesh3DTriangle* triangle_id) {
	per_cell_triangles_[cell_id].insert(triangle_id);
}

// registers input `triangle` as potentially intersecting the cell with input `cell_id` and sets
// `is_sparse_rays_lattice_updated` flags to false
void Grid3DSparseCubical::addTriangleToCell(const long long cell_id, Mesh3DTriangle* triangle) {
	per_cell_triangles_[cell_id].insert(triangle);
	setRaysUpdatedValue(false);
}

// set the `is_sparse_rays_lattice_updated` flags to input `value`
void Grid3DSparseCubical::setRaysUpdatedValue(bool value) {
	for (int i = 0; i < 3; ++i) {
		is_sparse_rays_lattice_updated[i] = value;
	}
}

void Grid3DSparseCubical::remove_triangle_from_cell(const long long cell_id,
                                                    Mesh3DTriangle* triangle_id) {
	per_cell_triangles_[cell_id].erase(triangle_id);
}

std::vector<Mesh3DTriangle*> Grid3DSparseCubical::getCellTriangles(const long long cell_id) const {
	auto result = per_cell_triangles_.find(cell_id);
	if (result == per_cell_triangles_.end()) {
		return {};
	}
	return std::vector<Mesh3DTriangle*>(result->second.begin(), result->second.end());
}

absl::flat_hash_set<Mesh3DTriangle*> Grid3DSparseCubical::get_cell_triangles_set(
    const long long cell_id) {
	auto result = per_cell_triangles_.find(cell_id);
	if (result == per_cell_triangles_.end()) {
		return {};
	}
	return per_cell_triangles_.at(cell_id);
}

// collect and return all grid cells with triangles registered on them
std::vector<long long> Grid3DSparseCubical::getCellsWithTriangles() {
	std::vector<long long> result;
	result.reserve(per_cell_triangles_.size());
	for (const auto& element : per_cell_triangles_) {
		result.push_back(element.first);
	}
	return result;
}

// save the input `intersection` on its grid edge
// NOTE: this function previously also took the edge id as an input parameter; this was redundant,
// so I removed it. The only use case where this would be useful to keep is if we would want to save
// the intersection on an edge with a different id than the one saved in the intersection object
// itself. However, if this would ever come up, I suggest that we write another function where we in
// its name and description explicitly state that this somewhat unintuitive operation is being
// performed.
void Grid3DSparseCubical::addIntersectionToEdge(GridEdgeMeshFaceIntersection intersection) {
	per_edge_intersections_[intersection.getEdgeId()].push_back(intersection);
}

std::vector<GridEdgeMeshFaceIntersection> Grid3DSparseCubical::get_intersections_on_edge(
    const long long edge_id) {
	auto find_it = per_edge_intersections_.find(edge_id);
	if (find_it == per_edge_intersections_.end()) {
		return {};
	}
	return find_it->second;
}

// SparseRaysContainer is a typedef for GridLattice<int,int>
const Grid3DSparseCubical::SparseRaysContainer& Grid3DSparseCubical::getSparseRays(
    long long orientation) {
	if (!is_sparse_rays_lattice_updated[orientation]) {
		sparse_rays_[orientation] = constructLatticeForCells(getCellsWithTriangles(), orientation);
		is_sparse_rays_lattice_updated[orientation] = true;
	}
	return sparse_rays_[orientation];
};

Grid3DSparseCubical::SparseRaysContainer Grid3DSparseCubical::constructLatticeForCells(
    const std::vector<long long>& cell_ids, long long orientation) const {
	absl::flat_hash_set<long long> unique_vertex_ids;

	// collect vertices on input cells into a set
	for (const long long cell_id : cell_ids) {
		const std::vector<long long> vertex_ids = get_verts_neighboring_cell(cell_id);
		for (const long long vertex_id : vertex_ids) {
			unique_vertex_ids.insert(vertex_id);
		}
	}

	// cast the set of grid vertices into a vector
	std::vector<long long> vertex_ids(unique_vertex_ids.begin(), unique_vertex_ids.end());

	// lambda function that converts a vertex id into its discrete i,j,k coordinates
	auto coord_extractor = [this](long long vert_id) {
		Vec3ll coords;
		this->get_vertex_coords(vert_id, coords[0], coords[1], coords[2]);
		return coords;
	};

	// return the grid lattice
	return Grid3DSparseCubical::SparseRaysContainer{vertex_ids, orientation, coord_extractor};
}

//------------------------------------------------------------
// manipulating complex vertices
//------------------------------------------------------------

bool Grid3DSparseCubical::isVertexMarkedComplex(const long long vertex_id) {
	return complex_vertices_.count(vertex_id);
}

void Grid3DSparseCubical::markVertexAsComplex(const long long vertex_id) {
	complex_vertices_.insert(vertex_id);
}

//------------------------------------------------------------
// manipulating complex edges
//------------------------------------------------------------

bool Grid3DSparseCubical::isEdgeMarkedTopoComplex(const long long edge_id) {
	return topo_complex_edges_.count(edge_id) > 0;
}

void Grid3DSparseCubical::markEdgeAsTopoComplex(const long long edge_id) {
	topo_complex_edges_.insert(edge_id);
}

bool Grid3DSparseCubical::isEdgeMarkedGeomComplex(const long long edge_id) {
	return geom_complex_edges_.count(edge_id) > 0;
}

void Grid3DSparseCubical::markEdgeAsGeomComplex(const long long edge_id) {
	geom_complex_edges_.insert(edge_id);
}

bool Grid3DSparseCubical::doesEdgeHaveFixedComplexNeighbors(const long long edge_id) {
	for (long long cell_id : get_cells_neighboring_edge(edge_id)) {
		if (isCellMarkedComplex(cell_id, ComplexCellType::kFixed)) {
			return true;
		}
	}
	return false;
}

bool Grid3DSparseCubical::isFrontEdge(const long long edge_id) {
	for (long long face : get_faces_neighboring_edge(edge_id)) {
		if (isFaceInComplexFront(face)) {
			return true;
		}
	}
	return false;
}

absl::flat_hash_set<long long> Grid3DSparseCubical::getTopoComplexGeomSimpleEdges() {
	absl::flat_hash_set<long long> return_set;
	for (long long edge_id : topo_complex_edges_) {
		if (!geom_complex_edges_.count(edge_id)) {
			return_set.insert(edge_id);
		}
	}
	return return_set;
}

absl::flat_hash_set<long long> Grid3DSparseCubical::getGeomComplexEdges() {
	return geom_complex_edges_;
}

//------------------------------------------------------------
// manipulating complex faces
//------------------------------------------------------------

bool Grid3DSparseCubical::isFaceMarkedTopoSimple(const long long face_id) {
	return topo_simple_faces_.count(face_id) > 0;
}

bool Grid3DSparseCubical::isFaceMarkedTopoComplex(const long long face_id) {
	return topo_complex_faces_.count(face_id) > 0;
}

bool Grid3DSparseCubical::isFaceMarkedTopoSuspicious(const long long face_id) {
	return topo_suspicious_faces_.count(face_id) > 0;
}

bool Grid3DSparseCubical::isFaceMarkedGeomComplex(const long long face_id) {
	return geom_complex_faces_.count(face_id) > 0;
}

void Grid3DSparseCubical::markFaceAsTopoSimple(const long long face_id) {
	topo_simple_faces_.insert(face_id);
}

void Grid3DSparseCubical::unmarkFaceAsTopoSimple(const long long face_id) {
	topo_simple_faces_.erase(face_id);
}

void Grid3DSparseCubical::markFaceAsTopoComplex(const long long face_id) {
	topo_complex_faces_.insert(face_id);
}

void Grid3DSparseCubical::markFaceAsTopoSuspicious(const long long face_id) {
	topo_suspicious_faces_.insert(face_id);
}

void Grid3DSparseCubical::markFaceAsGeomComplex(const long long face_id) {
	geom_complex_faces_.insert(face_id);
}

//------------------------------------------------------------
// manipulating complex cells
//------------------------------------------------------------

bool Grid3DSparseCubical::isCellMarkedComplex(const long long cell_id, ComplexCellType type) const {
	switch (type) {
		case ComplexCellType::kFixed:
			return fixed_complex_cells_.count(cell_id) > 0;
		case ComplexCellType::kFlexible:
			return flexible_complex_cells_.count(cell_id) > 0;
		case ComplexCellType::kBoth:
			return (fixed_complex_cells_.count(cell_id) > 0 ||
			        flexible_complex_cells_.count(cell_id) > 0);
		case ComplexCellType::kNumOfTypes:
			assert(false && "A dummy type is used to mark complexity.");
			return {};
	}
	return {};
}

void Grid3DSparseCubical::markCellAsComplex(const long long cell_id, ComplexCellType type) {
	switch (type) {
		case ComplexCellType::kFixed:
			fixed_complex_cells_.insert(cell_id);
			flexible_complex_cells_.erase(cell_id);
			break;
		case ComplexCellType::kFlexible:
			flexible_complex_cells_.insert(cell_id);
			fixed_complex_cells_.erase(cell_id);
			break;
		case ComplexCellType::kBoth:
			assert(false && "Cell can only be marked as one type of complex cell.");
			break;
		case ComplexCellType::kNumOfTypes:
			assert(false && "A dummy type is used to mark complexity.");
			break;
	}
	is_complex_cell_front_updated_ = false;
}

void Grid3DSparseCubical::unmarkCellAsComplex(const long long cell_id, ComplexCellType type) {
	switch (type) {
		case ComplexCellType::kFixed:
			fixed_complex_cells_.erase(cell_id);
			break;
		case ComplexCellType::kFlexible:
			flexible_complex_cells_.erase(cell_id);
			break;
		case ComplexCellType::kBoth:
			assert(false && "Cell can only be marked as one type of complex cell.");
			break;
		case ComplexCellType::kNumOfTypes:
			assert(false && "A dummy type is used to mark complexity.");
			break;
	}
	is_complex_cell_front_updated_ = false;
}

void Grid3DSparseCubical::markCellAsEdgeDeep(const long long cell_id) {
	edge_deep_cells_.insert(cell_id);
}

void Grid3DSparseCubical::markCellAsEdgeShallow(const long long cell_id) {
	edge_shallow_cells_.insert(cell_id);
}

std::vector<long long> Grid3DSparseCubical::getComplexCellsVector(ComplexCellType type) const {
	switch (type) {
		case ComplexCellType::kFixed:
			return std::vector<long long>(fixed_complex_cells_.begin(), fixed_complex_cells_.end());
		case ComplexCellType::kFlexible:
			return std::vector<long long>(flexible_complex_cells_.begin(), flexible_complex_cells_.end());
		case ComplexCellType::kBoth: {
			std::vector<long long> fixed_and_flexible = getComplexCellsVector(ComplexCellType::kFixed);
			std::vector<long long> flexible = getComplexCellsVector(ComplexCellType::kFlexible);
			fixed_and_flexible.insert(fixed_and_flexible.end(), flexible.begin(), flexible.end());
			return fixed_and_flexible;
		}
		case ComplexCellType::kNumOfTypes:
			assert(false);
			break;
	}
	return {};
}

absl::flat_hash_set<long long> Grid3DSparseCubical::getComplexCellsSet(ComplexCellType type) const {
	switch (type) {
		case ComplexCellType::kFixed:
			return fixed_complex_cells_;
		case ComplexCellType::kFlexible:
			return flexible_complex_cells_;
		case ComplexCellType::kBoth: {
			absl::flat_hash_set<long long> fixed_and_flexible =
			    getComplexCellsSet(ComplexCellType::kFixed);
			absl::flat_hash_set<long long> flexible = getComplexCellsSet(ComplexCellType::kFlexible);
			fixed_and_flexible.merge(flexible);
			return fixed_and_flexible;
		}
		case ComplexCellType::kNumOfTypes:
			assert(false);
			break;
	}
	return {};
}

absl::flat_hash_set<long long> Grid3DSparseCubical::getEdgeDeepCells() const {
	return edge_deep_cells_;
}

absl::flat_hash_set<long long> Grid3DSparseCubical::getEdgeShallowCells() const {
	return edge_shallow_cells_;
}

std::vector<long long> Grid3DSparseCubical::getFrontFacesVector() const {
	if (is_complex_cell_front_updated_) {
		return complex_cell_front_faces_;
	}
	absl::flat_hash_set<long long> visited_faces;
	std::vector<long long> front;
	for (const long long cell_id : getComplexCellsSet(ComplexCellType::kBoth)) {
		for (const long long face_id : get_faces_neighboring_cell(cell_id)) {
			if (visited_faces.count(face_id) > 0) {
				continue;
			}
			visited_faces.insert(face_id);
			if (isFaceInComplexFront(face_id)) {
				front.push_back(face_id);
			}
		}
	}
	complex_cell_front_faces_ = front;
	is_complex_cell_front_updated_ = true;
	return complex_cell_front_faces_;
}

absl::flat_hash_set<long long> Grid3DSparseCubical::getFrontFacesSet() const {
	std::vector<long long> front_faces = getFrontFacesVector();
	return absl::flat_hash_set<long long>(front_faces.begin(), front_faces.end());
}

absl::flat_hash_set<long long> Grid3DSparseCubical::getTopoComplexFaces() const {
	return topo_complex_faces_;
}

absl::flat_hash_set<long long> Grid3DSparseCubical::getComplexRegionFrontCellsSet() const {
	std::vector<long long> front_faces = getFrontFacesVector();
	absl::flat_hash_set<long long> front_cells;
	for (const long long front_face_id : front_faces) {
		for (const long long cell_id : get_cells_neighboring_face(front_face_id)) {
			if (isCellMarkedComplex(cell_id, ComplexCellType::kBoth)) {
				front_cells.insert(cell_id);
			}
		}
	}
	return front_cells;
}

std::vector<long long> Grid3DSparseCubical::getComplexRegionFrontCellsVector() const {
	std::vector<long long> front_faces = getFrontFacesVector();
	absl::flat_hash_set<long long> front_cells;
	for (const long long front_face_id : front_faces) {
		for (const long long cell_id : get_cells_neighboring_face(front_face_id)) {
			if (isCellMarkedComplex(cell_id, ComplexCellType::kBoth)) {
				front_cells.insert(cell_id);
			}
		}
	}
	return std::vector<long long>(front_cells.begin(), front_cells.end());
}

std::vector<long long> Grid3DSparseCubical::getSimpleRegionFrontCellsVector() const {
	std::vector<long long> front_faces = getFrontFacesVector();
	absl::flat_hash_set<long long> front_cells;
	for (const long long front_face_id : front_faces) {
		for (const long long cell_id : get_cells_neighboring_face(front_face_id)) {
			if (!isCellMarkedComplex(cell_id, ComplexCellType::kBoth)) {
				front_cells.insert(cell_id);
			}
		}
	}
	return std::vector<long long>(front_cells.begin(), front_cells.end());
}

absl::flat_hash_set<long long> Grid3DSparseCubical::getSimpleRegionFrontCellsSet() const {
	std::vector<long long> front_faces = getFrontFacesVector();
	absl::flat_hash_set<long long> front_cells;
	for (const long long front_face_id : front_faces) {
		for (const long long cell_id : get_cells_neighboring_face(front_face_id)) {
			if (!isCellMarkedComplex(cell_id, ComplexCellType::kBoth)) {
				front_cells.insert(cell_id);
			}
		}
	}
	return front_cells;
}

bool Grid3DSparseCubical::isFaceInComplexFront(long long face_id) const {
	bool has_complex = false;
	bool has_non_complex = false;
	for (const long long cell_id : get_cells_neighboring_face(face_id)) {
		if (isCellMarkedComplex(cell_id, ComplexCellType::kBoth)) {
			has_complex = true;
		} else {
			has_non_complex = true;
		}
	}
	return has_complex && has_non_complex;
}

void Grid3DSparseCubical::add_mesh_vertex_to_edge(const long long edge_id, Mesh3DVertex* v1) {
	per_edge_mesh_vertices_[edge_id].push_back(v1);
}

std::vector<Mesh3DVertex*> Grid3DSparseCubical::get_mesh_vertices_on_edge(const long long edge_id) {
	auto find_it = per_edge_mesh_vertices_.find(edge_id);
	if (find_it == per_edge_mesh_vertices_.end()) {
		return {};
	}
	return find_it->second;
}

void Grid3DSparseCubical::add_mesh_edge_intersection_to_grid_face(
    const long long face_id, GridFaceMeshEdgeIntersection intersection) {
	per_face_mesh_edges_[face_id].push_back(intersection);
}

std::vector<GridFaceMeshEdgeIntersection> Grid3DSparseCubical::get_mesh_edge_intersections_on_face(
    const long long face_id) {
	auto find_it = per_face_mesh_edges_.find(face_id);
	if (find_it == per_face_mesh_edges_.end()) {
		return {};
	}
	return find_it->second;
}

void Grid3DSparseCubical::clear_mesh_edge_intersections() { per_face_mesh_edges_.clear(); }

void Grid3DSparseCubical::add_graph_on_face(const long long face_id,
                                            const std::pair<Mesh3DVertex*, Mesh3DVertex*>& edge,
                                            Mesh3DTriangle* outside_triangle) {
	graph_on_faces[face_id][edge] = outside_triangle;
}

absl::flat_hash_map<std::pair<Mesh3DVertex*, Mesh3DVertex*>, Mesh3DTriangle*>
Grid3DSparseCubical::getGraphOnFace(const long long face_id) const {
	auto it = graph_on_faces.find(face_id);
	if (it != graph_on_faces.end()) {
		return it->second;
	}
	return {};
}

void Grid3DSparseCubical::update_mesh_pointers(const Mesh3DSaveState& idx_converters) {
	// Update mesh triangle pointers in instances of GridMeshIntersection.
	for (auto& intersections : per_edge_intersections_) {
		for (auto& intersection : intersections.second) {
			intersection = GridEdgeMeshFaceIntersection{
			    idx_converters.triangles_indices.at(intersection.getTriangle()), intersection.getEdgeId(),
			    intersection.getPosition(), intersection.getBary(),
			    intersection.isTriNormalEdgeAligned()};
		}
	}

	// Update mesh vertex pointers saved on grid edges.
	for (auto& mesh_vertices : per_edge_mesh_vertices_) {
		for (auto& mesh_vertex : mesh_vertices.second) {
			mesh_vertex = idx_converters.vertices_indices.at(mesh_vertex);
		}
	}

	// Update mesh edge, i.e. pairs of mesh vertex pointers, saved on grid faces.
	for (auto& mesh_edges : per_face_mesh_edges_) {
		for (auto& mesh_edge : mesh_edges.second) {
			Mesh3DVertex* inter_vert = mesh_edge.getVertex();
			if (inter_vert != nullptr) {
				inter_vert = idx_converters.vertices_indices.at(inter_vert);
			}
			mesh_edge = {mesh_edge.getFaceId(),
			             idx_converters.vertices_indices.at(mesh_edge.getEdgeFirst()),
			             mesh_edge.isFirstInside(),
			             idx_converters.vertices_indices.at(mesh_edge.getEdgeSecond()),
			             mesh_edge.isSecondInside(),
			             mesh_edge.getBaryCoord(),
			             inter_vert};
		}
	}

	// Update mesh triangle pointers saved on grid cells.
	for (auto& triangles : per_cell_triangles_) {
		absl::flat_hash_set<Mesh3DTriangle*> updated_triangles;
		for (Mesh3DTriangle* triangle : triangles.second) {
			updated_triangles.insert(idx_converters.triangles_indices.at(triangle));
		}
		triangles.second = updated_triangles;
	}

	// Update the pointers comprising graphs on grid faces.
	for (auto& face_graph : graph_on_faces) {
		absl::flat_hash_map<std::pair<Mesh3DVertex*, Mesh3DVertex*>, Mesh3DTriangle*> graph;
		for (auto& edge : face_graph.second) {
			graph.try_emplace({idx_converters.vertices_indices.at(edge.first.first),
			                   idx_converters.vertices_indices.at(edge.first.second)},
			                  idx_converters.triangles_indices.at(edge.second));
		}
		face_graph.second = graph;
	}
};

void Grid3DSparseCubical::addInterpolatedVertPropsOnVertex(long long vertex_id,
                                                           VertexProperties vert_props) {
	interpolated_vert_props_on_vertices_[vertex_id] = vert_props;
}

VertexProperties Grid3DSparseCubical::getInterpolatedVertPropsFromVertex(long long vertex_id) {
	return interpolated_vert_props_on_vertices_[vertex_id];
}

bool Grid3DSparseCubical::isMeshVertexInGridCellNaive(Mesh3DVertex* mesh_vertex,
                                                      long long cell_id) {
	Vec3d cell_min_pos = getCellMinPosition(cell_id);
	Vec3d cell_max_pos = getCellMaxPosition(cell_id);
	if (mesh_vertex->getXCoord() >= cell_min_pos[0] && mesh_vertex->getXCoord() <= cell_max_pos[0] &&
	    mesh_vertex->getYCoord() >= cell_min_pos[1] && mesh_vertex->getYCoord() <= cell_max_pos[1] &&
	    mesh_vertex->getZCoord() >= cell_min_pos[2] && mesh_vertex->getZCoord() <= cell_max_pos[2]) {
		return true;
	}
	return false;
}

int Grid3DSparseCubical::getLabelFromUniqueMaterialVector(long long grid_vertex) {
	SparseVector<int>& material = per_vertex_material_labels_.at(grid_vertex);
	assert(material.getNNZ() == 1);
	return material.getKey(0);
}

bool Grid3DSparseCubical::isVertexInComplexRegion(long long grid_vertex) {
	for (long long grid_cell : get_cells_neighboring_vertex(grid_vertex)) {
		if (isCellMarkedComplex(grid_cell, ComplexCellType::kBoth)) {
			return true;
		}
	}
	return false;
};

void Grid3DSparseCubical::addUniqueLabeling(long long grid_vertex, int label) {
	unique_labeling[grid_vertex] = label;
}

absl::flat_hash_map<long long, int>::iterator Grid3DSparseCubical::getUniqueLabeling(
    long long grid_vertex) {
	return unique_labeling.find(grid_vertex);
};

bool Grid3DSparseCubical::hasUniqueLabeling(long long grid_vertex) {
	return unique_labeling.count(grid_vertex) > 0;
};

absl::flat_hash_map<long long, int>& Grid3DSparseCubical::getUniqueLabelingMap() {
	return unique_labeling;
}

void Grid3DSparseCubical::addOptimizedMCEdgePoint(long long grid_edge, Vec3d optimized_point) {
	optimizedMCEdgeVertices[grid_edge] = optimized_point;
}

absl::flat_hash_map<long long, Vec3d>::iterator Grid3DSparseCubical::getOptimizedMCEdgePoint(
    long long grid_edge) {
	return optimizedMCEdgeVertices.find(grid_edge);
};

bool Grid3DSparseCubical::hasOptimizedMCEdgePoint(long long grid_edge) {
	return optimizedMCEdgeVertices.count(grid_edge) > 0;
};