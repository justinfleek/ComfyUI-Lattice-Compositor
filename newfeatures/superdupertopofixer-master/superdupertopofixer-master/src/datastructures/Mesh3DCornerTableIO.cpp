/* Mesh3DCornerTableIO.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2021
 *
 * This is the implementation file for the mesh corner table input/output functions.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <queue>
#include <unordered_map>

#include "Mesh3DCornerTable.h"
#include "Mesh3DHalfCorner.h"
#include "Mesh3DVertex.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// reads corner table data in Mesh3DSaveState format from a binary file into memory
// TODO: implement mesh consistency checking
int Mesh3DCornerTable::loadBinary(std::string_view binary_file) {
	// clear all currently saved mesh elements and release the associated memory
	clear();

	std::ifstream bin_file(binary_file.data(), std::ios::binary);
	int vert_count = 0, tri_count = 0, hfc_count = 0;

	// read number of verts, tris, hfcs:
	bin_file.read((char*)&vert_count, sizeof(int));
	bin_file.read((char*)&tri_count, sizeof(int));
	bin_file.read((char*)&hfc_count, sizeof(int));

	Mesh3DSaveState save_state;
	save_state.vertices.resize(vert_count);
	save_state.triangles.resize(tri_count);
	save_state.half_corners.resize(hfc_count);

	// Read elements into the save state.
	for (int i = 0; i < vert_count; i++) {
		bin_file.read((char*)&(save_state.vertices[i]), sizeof(Mesh3DVertex));
	}
	for (int i = 0; i < tri_count; i++) {
		bin_file.read((char*)&(save_state.triangles[i]), sizeof(Mesh3DTriangle));
	}
	for (int i = 0; i < hfc_count; i++) {
		bin_file.read((char*)&(save_state.half_corners[i]), sizeof(Mesh3DHalfCorner));
	}
	bin_file.close();

	// Recreate the corner table by restoring pointers between elements.
	restoreFromSaveState(save_state);

	if (settings->verbosity >= 1) {
		std::cout << "-corner table read from \"" << binary_file << "\"" << std::endl;
		std::cout << "==========================================================================="
		             "=========="
		          << std::endl;
	}
	if (settings->verbosity >= 2) {
		std::cout << "vertex count after loading: " << mesh_vertices_list.size() << std::endl;
		std::cout << "triangle count after loading: " << mesh_triangles_list.size() << std::endl;
		std::cout << "half-corner count after loading: " << mesh_half_corners_list.size() << std::endl;
	}

	return 0;
}

// writes the mesh into a binary file in Mesh3DSaveState format
void Mesh3DCornerTable::writeInBin(const std::string& output_file) {
	Mesh3DSaveState save_state = getCurrentSaveState();

	std::ofstream ofile(output_file, std::ios::binary);

	int num_all_verts = save_state.vertices.size();
	int num_all_tris = save_state.triangles.size();
	int num_all_hfcs = save_state.half_corners.size();

	// write number of verts, tris, hfcs:
	ofile.write((char*)(&num_all_verts), sizeof(int));
	ofile.write((char*)(&num_all_tris), sizeof(int));
	ofile.write((char*)(&num_all_hfcs), sizeof(int));

	// write verts
	for (Mesh3DVertex vert : save_state.vertices) {
		ofile.write((char*)(&vert), sizeof(Mesh3DVertex));
	}

	// write tris
	for (Mesh3DTriangle triangle : save_state.triangles) {
		ofile.write((char*)(&triangle), sizeof(Mesh3DTriangle));
	}

	// write hfcs
	for (Mesh3DHalfCorner hfc : save_state.half_corners) {
		ofile.write((char*)(&hfc), sizeof(Mesh3DHalfCorner));
	}

	ofile.close();

	if (settings->verbosity >= 1) {
		std::cout << "-corner table saved in \"" << output_file << "\"" << std::endl;
		std::cout
		    << "====================================================================================="
		    << std::endl;
	}
	if (settings->verbosity >= 2) {
		std::cout << "number of saved vertices: " << num_all_verts << std::endl;
	}
}

// writes the mesh into an easiely readable text file for debugging
void Mesh3DCornerTable::writeInText(const std::string& output_file) {
	std::ofstream corner_table_file;
	corner_table_file.open(output_file);

	// maps that assign indices to elements; indices are used as reference between elements in order
	// to make analyzing the output file easier
	std::map<Mesh3DVertex*, int> vert_index_map;
	std::map<Mesh3DTriangle*, int> tri_index_map;
	std::map<Mesh3DHalfCorner*, int> hfc_index_map;
	int vert_index = 0, tri_index = 0, hfc_index = 0;

	// assign indices to vertices, triangles, and half-corners, all starting from 0
	for (Mesh3DVertex* vertex : mesh_vertices_list) {
		vert_index_map.insert({vertex, vert_index});
		vert_index++;
	}
	for (Mesh3DTriangle* triangle : mesh_triangles_list) {
		tri_index_map.insert({triangle, tri_index});
		tri_index++;
	}
	for (Mesh3DHalfCorner* hfc : mesh_half_corners_list) {
		hfc_index_map.insert({hfc, hfc_index});
		hfc_index++;
	}

	// write vertices into text file
	for (Mesh3DVertex* vertex : mesh_vertices_list) {
		corner_table_file << "vertex: " << vert_index_map.at(vertex) << ' ' << vertex->getCoord(0)
		                  << ' ' << vertex->getCoord(1) << ' ' << vertex->getCoord(2) << '\n';
	}
	// write triangles into text file
	for (Mesh3DTriangle* triangle : mesh_triangles_list) {
		corner_table_file << "triangle: " << tri_index_map.at(triangle)
		                  << "; vertices = " << vert_index_map.at(triangle->getVertex(0)) << ' '
		                  << vert_index_map.at(triangle->getVertex(1)) << ' '
		                  << vert_index_map.at(triangle->getVertex(2))
		                  << "; hfc = " << hfc_index_map.at(triangle->getHalfCorner())
		                  << "; labels = " << (triangle->getLabel(0)) << ' ' << (triangle->getLabel(1))
		                  << '\n';
	}
	// write half-corners into text file
	for (Mesh3DHalfCorner* hfc : mesh_half_corners_list) {
		corner_table_file << "half-corner: " << hfc_index_map.at(hfc)
		                  << "; triangle = " << tri_index_map.at(hfc->getTri())
		                  << "; vertex = " << vert_index_map.at(hfc->getVertex())
		                  << "; next = " << hfc_index_map.at(hfc->getNext())
		                  << ", previous = " << hfc_index_map.at(hfc->getPrev())
		                  << ", opposite = " << hfc_index_map.at(hfc->getOppos())
		                  << ", twin = " << hfc_index_map.at(hfc->getDual())
		                  << "; labelside = " << hfc->getLabelSide() << ", label = " << hfc->getLabel()
		                  << '\n';
	}
}

//------------------------------------------------------------
// save state manipulation
//------------------------------------------------------------

// takes a snapshot of the mesh in the form of a Mesh3DSaveState object
Mesh3DSaveState Mesh3DCornerTable::getCurrentSaveState() {
	Mesh3DSaveState save_state;

	save_state.vertices.reserve(mesh_vertices_list.size());
	save_state.triangles.reserve(mesh_triangles_list.size());
	save_state.half_corners.reserve(mesh_half_corners_list.size());

	// Fill in vectors of elements and index conversion maps.
	size_t v_count = 0;
	for (Mesh3DVertex* vert : mesh_vertices_list) {
		save_state.vertices_indices[vert] = reinterpret_cast<Mesh3DVertex*>(v_count);
		save_state.vertices.push_back(*vert);
		v_count++;
	}

	size_t tri_count = 0;
	for (Mesh3DTriangle* tri : mesh_triangles_list) {
		save_state.triangles_indices[tri] = reinterpret_cast<Mesh3DTriangle*>(tri_count);
		save_state.triangles.push_back(*tri);
		tri_count++;
	}

	size_t hfc_count = 0;
	for (Mesh3DHalfCorner* hfc : mesh_half_corners_list) {
		save_state.hfc_indices[hfc] = reinterpret_cast<Mesh3DHalfCorner*>(hfc_count);
		save_state.half_corners.push_back(*hfc);
		hfc_count++;
	}

	// Convert pointers to indices (still typed as pointers, in order to reuse allocated
	// memory).
	for (Mesh3DTriangle& tri : save_state.triangles) {
		tri.setHalfCorner(save_state.hfc_indices.at(tri.getHalfCorner()));
	}

	for (Mesh3DHalfCorner& hfc : save_state.half_corners) {
		hfc.setVertex(save_state.vertices_indices.at(hfc.getVertex()));
		hfc.setTri(save_state.triangles_indices.at(hfc.getTri()));
		hfc.setNext(save_state.hfc_indices.at(hfc.getNext()));
		hfc.setPrev(save_state.hfc_indices.at(hfc.getPrev()));
		hfc.setOppos(save_state.hfc_indices.at(hfc.getOppos()));
		hfc.setDual(save_state.hfc_indices.at(hfc.getDual()));
	}
	return save_state;
}

// restore mesh from a Mesh3DSaveState object into the corner table
Mesh3DSaveState Mesh3DCornerTable::restoreFromSaveState(const Mesh3DSaveState& save_state) {
	// Clear all currently saved mesh elements and release the associated memory.
	clear();
	return appendFromSaveState(save_state);
}

// restore mesh from a Mesh3DSaveState object into the corner table
Mesh3DSaveState Mesh3DCornerTable::appendFromSaveState(const Mesh3DSaveState& save_state) {
	// Define a new save state that will be used for reconstructing the corner table.
	Mesh3DSaveState output_state;

	// Allocate memory for new mesh elements and set up inverse index conversion maps.
	absl::flat_hash_map<Mesh3DVertex*, size_t> vert_to_idx;
	for (size_t i = 0; i < save_state.vertices.size(); i++) {
		Mesh3DVertex* new_v = makeNewVertex();
		output_state.vertices_indices[reinterpret_cast<Mesh3DVertex*>(i)] = new_v;
		vert_to_idx[new_v] = i;
	}
	absl::flat_hash_map<Mesh3DTriangle*, size_t> tri_to_idx;
	for (size_t i = 0; i < save_state.triangles.size(); i++) {
		Mesh3DTriangle* new_tri = new Mesh3DTriangle();
		output_state.triangles_indices[reinterpret_cast<Mesh3DTriangle*>(i)] = new_tri;
		mesh_triangles_list.insert(new_tri);
		tri_to_idx[new_tri] = i;
	}
	absl::flat_hash_map<Mesh3DHalfCorner*, size_t> hfc_to_idx;
	for (size_t i = 0; i < save_state.half_corners.size(); i++) {
		Mesh3DHalfCorner* new_hfc = new Mesh3DHalfCorner();
		output_state.hfc_indices[reinterpret_cast<Mesh3DHalfCorner*>(i)] = new_hfc;
		mesh_half_corners_list.insert(new_hfc);
		hfc_to_idx[new_hfc] = i;
	}

	// Copy elements from the input save state to the corner table, and restore correct pointers
	// by making use of the saved indices.
	for (Mesh3DVertex* vert : mesh_vertices_list) {
		if (!vert_to_idx.contains(vert)) {
			continue;
		}
		*vert = save_state.vertices[vert_to_idx.at(vert)];
	}

	for (Mesh3DTriangle* triangle : mesh_triangles_list) {
		if (!tri_to_idx.contains(triangle)) {
			continue;
		}
		*triangle = save_state.triangles[tri_to_idx.at(triangle)];
		triangle->setHalfCorner(output_state.hfc_indices[triangle->getHalfCorner()]);
	}

	for (Mesh3DHalfCorner* hfc : mesh_half_corners_list) {
		if (!hfc_to_idx.contains(hfc)) {
			continue;
		}
		*hfc = save_state.half_corners[hfc_to_idx.at(hfc)];
		hfc->setVertex(output_state.vertices_indices[hfc->getVertex()]);
		hfc->setTri(output_state.triangles_indices[hfc->getTri()]);
		hfc->setNext(output_state.hfc_indices[hfc->getNext()]);
		hfc->setPrev(output_state.hfc_indices[hfc->getPrev()]);
		hfc->setOppos(output_state.hfc_indices[hfc->getOppos()]);
		hfc->setDual(output_state.hfc_indices[hfc->getDual()]);
		vertex_to_hfc_map[hfc->getVertex()].insert(hfc);
	}
	return output_state;
}

// loads vectors of vertex positions, vertex velocities, triangle vertex indices, and material label
// pairs into the corner table
int Mesh3DCornerTable::restoreFromGeometry(const std::vector<Vec3i>& triangle_vertices,
                                           const std::vector<Vec3d>& vertex_positions,
                                           const std::vector<VertexProperties>& vertex_properties,
                                           const std::vector<Vec2i>& material_labels,
                                           const int add_to_existing, const int offset_materials) {
	// warn if there aren't enough material labels, i.e. if there are fewer material label pairs than
	// triangles
	if (triangle_vertices.size() > material_labels.size()) {
		if (settings->verbosity >= 1) {
			std::cout << "-WARNING: fewer triangles than material label pairs, only first "
			          << material_labels.size() << " triangles will be loaded\n";
		}
	}

	// warn if there are more material pairs than triangles
	if (material_labels.size() != triangle_vertices.size()) {
		if (settings->verbosity >= 2) {
			std::cout << "-WARNING: more input material pairs than triangles, only first: "
			          << triangle_vertices.size() << " material pairs will be loaded\n";
		}
	}

	// determine the number of triangles to load - each triangle has to have an associated material
	// label pair, we therefore use the minimum of the number of triangles and material pairs
	const size_t tris_to_load = std::min(triangle_vertices.size(), material_labels.size());

	// if the adding flag is false, clear the corner table
	if (!add_to_existing) {
		clear();
	}

	// if materials in the input file are to be offset by the existing materials, find the size of the
	// offset (the largest currently assigned material label)
	int max_mat = -1;
	if (offset_materials) {
		for (Mesh3DTriangle* triangle : mesh_triangles_list) {
			if (max_mat < triangle->getLabel(0)) {
				max_mat = triangle->getLabel(0);
			}
			if (max_mat < triangle->getLabel(1)) {
				max_mat = triangle->getLabel(1);
			}
		}
	}

	// helper vectors for loading primitives, they map indices induced by the order of reading from an
	// input file to pointers to elements
	std::vector<Mesh3DTriangle*> mesh_triangles_vec;
	std::vector<Mesh3DVertex*> mesh_vertices_vec;
	// helper vertex indices of a triangle
	int v0, v1, v2;
	// map, where the key is a pair of triangle vertices (x,y) in ascending order of indices, that
	// defines a triangle edge, and the value is a vector of extending HCs of this edge, one (of two
	// dual choices) per each triangle (x,y,z) containing (x,y); an extending HC of edge (x,y) is a HC
	// at z; this map is used to assign HC opposites
	std::map<std::pair<int, int>, std::vector<Mesh3DHalfCorner*>> extending_corners;

	// load vertices into the corner table
	std::vector<Vec3d>::const_iterator v_pos = vertex_positions.begin();
	std::vector<VertexProperties>::const_iterator v_props = vertex_properties.begin();
	if (vertex_properties.size() <= vertex_positions.size()) {
		for (; v_props != vertex_properties.end(); ++v_props, ++v_pos) {
			// create a new vertex at position `v_pos` with properties `v_props`, and push it into the
			// list (long term storage)
			Mesh3DVertex* mvert = makeNewVertexAtCoords(*v_pos, *v_props);
			// push the new vertex into a vector (local storage used for assigning pointers)
			mesh_vertices_vec.push_back(mvert);
		}
		for (; v_pos != vertex_positions.end(); ++v_pos) {
			// create a new vertex at position `v_pos` with default properties, and push it into the list
			// (long term storage)
			Mesh3DVertex* mvert = makeNewVertexAtCoords(*v_pos);
			// push the new vertex into a vector (local storage used for assigning pointers)
			mesh_vertices_vec.push_back(mvert);
		}
	} else {
		for (; v_pos != vertex_positions.end(); ++v_pos) {
			// create a new vertex at position `v_pos` with default properties, and push it into the list
			// (long term storage)
			Mesh3DVertex* mvert = makeNewVertexAtCoords(*v_pos);
			// push the new vertex into a vector (local storage used for assigning pointers)
			mesh_vertices_vec.push_back(mvert);
		}
	}

	// load triangles and material label pairs into the corner table
	for (size_t it = 0; it < tris_to_load; ++it) {
		v0 = triangle_vertices[it][0];
		v1 = triangle_vertices[it][1];
		v2 = triangle_vertices[it][2];

		// if triangle is combinatorially degenerate, skip it (we also ignore its corresponding
		// material pair)
		bool is_degenerate = v0 == v1 || v1 == v2 || v2 == v0;
		if (is_degenerate) {
			if (settings->verbosity >= 2) {
				std::cout << "-degenerate triangle: " << v0 << " " << v1 << " " << v2 << " not loaded\n";
			}
			continue;
		}

		// based on input flag, offset materials by the largest material index
		Vec2i material_pair = material_labels[it];
		if (offset_materials) {
			material_pair += max_mat;
		}

		Mesh3DVertex* vp0 = mesh_vertices_vec.at(v0);
		Mesh3DVertex* vp1 = mesh_vertices_vec.at(v1);
		Mesh3DVertex* vp2 = mesh_vertices_vec.at(v2);
		Mesh3DTriangle* mtri = makeNewTriangle(vp0, vp1, vp2, material_pair);
		std::vector<Mesh3DHalfCorner*> hfcs = mtri->getHalfCorners();

		// fill in `extending_corners` map, where the key is a pair of triangle vertices (x,y) in
		// ascending order of indices, that defines a triangle edge, and the value is a vector of
		// extending HCs of this edge, one (of two dual choices) per each triangle (x,y,z) containing
		// (x,y); an extending HC of edge (x,y) is a HC at z; of the two dual choices, we pick the
		// one, such that using the triangle orientation given by (x,y), the extending HC is on the
		// side into which right hand normal points
		if (v0 < v1) {
			extending_corners[{v0, v1}].push_back(hfcs[2]);
		} else {
			extending_corners[{v1, v0}].push_back(hfcs[4]);
		}
		if (v0 < v2) {
			extending_corners[{v0, v2}].push_back(hfcs[5]);
		} else {
			extending_corners[{v2, v0}].push_back(hfcs[1]);
		}
		if (v1 < v2) {
			extending_corners[{v1, v2}].push_back(hfcs[0]);
		} else {
			extending_corners[{v2, v1}].push_back(hfcs[3]);
		}
		// push the new triangle into local storage used for assigning pointers
		mesh_triangles_vec.push_back(mtri);
	}

	int result = 0;
	if (settings->opposite_reconstruction_type ==
	    TopoFixerSettings::OppositeReconstructionType::Geometry) {
		result = restoreOppositesGeometrically(extending_corners, mesh_vertices_vec);
	} else if (settings->opposite_reconstruction_type ==
	           TopoFixerSettings::OppositeReconstructionType::Labels) {
		result = restoreOppositesByLabels(extending_corners);
	}
	if (result != 0) {
		return result;
	}

	// run mesh consistency checks, if any critical tests fail, terminate
	if (settings->run_input_mesh_consistency_tests ==
	        TopoFixerSettings::InputMeshConsistencyTests::All ||
	    settings->run_input_mesh_consistency_tests ==
	        TopoFixerSettings::InputMeshConsistencyTests::Critical) {
		int mesh_consistency = runMeshConsistencyChecks();
		if (mesh_consistency == 0 && settings->verbosity >= 2) {
			std::cout << "-all mesh consistency checks passed\n";
		}
		if (mesh_consistency == 1 && settings->verbosity >= 1) {
			std::cout << "-some optional mesh consistency checks failed, algorithm will continue\n";
		}
		if (mesh_consistency == 2 && settings->verbosity >= 1) {
			std::cout << "-some critical mesh consistency checks failed, algorithm will terminate\n";
			return 1;
		}
	}
	return 0;
}

int Mesh3DCornerTable::restoreOppositesGeometrically(
    const std::map<std::pair<int, int>, std::vector<Mesh3DHalfCorner*>>& extending_corners,
    const std::vector<Mesh3DVertex*>& mesh_vertices_vec) {
	for (auto& edge : extending_corners) {
		if (edge.second.size() == 2) {
			// manifold case, there are exactly 2 extending corners for the edge
			// assign opposite pointers
			edge.second.at(0)->setOppos(edge.second.at(1)->getDual());
			edge.second.at(1)->getDual()->setOppos(edge.second.at(0));
			edge.second.at(0)->getDual()->setOppos(edge.second.at(1));
			edge.second.at(1)->setOppos(edge.second.at(0)->getDual());
		} else if (edge.second.size() > 2) {
			// non-manifold case, there are more than 2 extending corners for the edge
			// reference for the vector of extending HCs
			const std::vector<Mesh3DHalfCorner*>& ext_hfcs = edge.second;
			// for each extending HC, we store the set of HCs that lie to its left, and to its right
			std::vector<std::set<Mesh3DHalfCorner*>> left_neighbors(ext_hfcs.size(),
			                                                        std::set<Mesh3DHalfCorner*>());
			std::vector<std::set<Mesh3DHalfCorner*>> right_neighbors(ext_hfcs.size(),
			                                                         std::set<Mesh3DHalfCorner*>());
			// retrieve coordinates of the edge vertices
			Vec3d edge_v0_coords = mesh_vertices_vec.at(edge.first.first)->getCoords();
			Vec3d edge_v1_coords = mesh_vertices_vec.at(edge.first.second)->getCoords();

			// iterate over extending HCs of `edge`, iterated extending HC is referred to as base HC
			// fill in `left_neighbors` and `right_neighbors` sets
			for (size_t base = 0; base < ext_hfcs.size(); ++base) {
				// retrieve coordinates of base HC
				Vec3d base_ext_coords = ext_hfcs.at(base)->getVertex()->getCoords();

				// references for left and right sets of base HC
				std::set<Mesh3DHalfCorner*>&left_of_current_hfc = left_neighbors.at(base),
				&right_of_current_hfc = right_neighbors.at(base);

				// iterate over extending HCs of `edge`, iterated extending HC is refered to as current HC
				// sort current HCs into left and right sets of base HC
				for (size_t curr = 0; curr < ext_hfcs.size(); ++curr) {
					// skip if base and current HCs are the same
					if (base == curr) {
						continue;
					}
					// retrieve coordinates of current HC
					Vec3d curr_ext_coords = ext_hfcs.at(curr)->getVertex()->getCoords();

					// assign current HC into left or right set of base HC
					if (intersector.orient3d(edge_v0_coords.v, edge_v1_coords.v, base_ext_coords.v,
					                         curr_ext_coords.v) > 0) {
						left_of_current_hfc.insert(ext_hfcs.at(curr));
					} else {
						right_of_current_hfc.insert(ext_hfcs.at(curr));
					}
				}
			}

			// iterate over extending HCs of `edge`, iterated extending HC is referred to as base HC
			// find opposite HC candidate pairs, and if no error occurs, set their opposite pointers
			for (size_t i = 0; i < ext_hfcs.size(); ++i) {
				Mesh3DHalfCorner* oppos_candidate = nullptr;
				// reference for base HC right set
				std::set<Mesh3DHalfCorner*>& base_right_neighbors = right_neighbors.at(i);

				if (base_right_neighbors.empty()) {
					// if there are no right neighbors of base, find the extending HC with no left neighbors
					// (there should be exactly one)
					for (size_t j = 0; j < ext_hfcs.size(); ++j) {
						if (left_neighbors.at(j).empty()) {
							// found an opposite candidate
							oppos_candidate = ext_hfcs.at(j);
							break;
						}
					}
				} else {
					// if there are some right neighbors of base, iterate over extending HCs of `edge`,
					// iterated extending HC is refered to as current HC; find the current extending HC that
					// is in the right set of base, and the intersection of right set of base and left set
					// of current is empty
					for (size_t j = 0; j < ext_hfcs.size(); ++j) {
						// skip if base == current
						if (i == j) {
							continue;
						}
						if (base_right_neighbors.count(ext_hfcs.at(j))) {
							std::set<Mesh3DHalfCorner*>& curr_left_neighbors = left_neighbors.at(j);
							std::vector<Mesh3DHalfCorner*> intersect_set;
							std::set_intersection(base_right_neighbors.begin(), base_right_neighbors.end(),
							                      curr_left_neighbors.begin(), curr_left_neighbors.end(),
							                      inserter(intersect_set, intersect_set.begin()));
							if (intersect_set.size() == 0) {
								// found an opposite candidate
								oppos_candidate = ext_hfcs.at(j);
								break;
							}
						}
					}
				}
				if (oppos_candidate != nullptr) {
					// assign the opposite pointers of base HC and of dual of opposite candidate; we take
					// dual of the opposite candidate, because we consistently chose to store those
					// extending HCs that are on the same side of triangles with respect to the orientation
					// imposed by following `edge` (namely all extending HC are on the side into which right
					// hand normal points)
					ext_hfcs.at(i)->setOppos(oppos_candidate->getDual());
					oppos_candidate->getDual()->setOppos(ext_hfcs.at(i));
				} else {
					// if the HC has no opposite candidate, quit
					if (settings->verbosity >= 1) {
						std::cout << "-CRITICAL: half-corner " << ext_hfcs.at(i)
						          << " has no opposite half-corner, quitting\n";
						return 1;
					}
				}
			}
		} else if (edge.second.size() < 2) {
			// critical error, less than 2 extending corners, mesh is not closed
			if (settings->verbosity >= 1) {
				std::cout << "-CRITICAL: edge between vertices " << edge.first.first << " and "
				          << edge.first.second << " has only one adjacent triangle, quitting\n";
				return 1;
			}
		}
	}
	return 0;
}

int Mesh3DCornerTable::restoreOppositesByLabels(
    const std::map<std::pair<int, int>, std::vector<Mesh3DHalfCorner*>>& extending_corners) {
	for (const auto& [edge, hfcs] : extending_corners) {
		absl::flat_hash_map<int, std::vector<Mesh3DHalfCorner*>> label_to_hfcs;
		for (Mesh3DHalfCorner* hfc : hfcs) {
			label_to_hfcs[hfc->getLabel()].push_back(hfc);
			label_to_hfcs[hfc->getDual()->getLabel()].push_back(hfc->getDual());
		}

		// Assign half-corners.
		for (const auto& [label, hfcs] : label_to_hfcs) {
			if (hfcs.size() != 2) {
				if (settings->verbosity >= 1) {
					std::cout << "-CRITICAL: hfcs with label " << label << " around " << edge.first << " and "
					          << edge.second << " are not paired. There are " << hfcs.size()
					          << " half-corners around this edge instead. Quitting\n";
					return 1;
				}
			}
			hfcs[0]->setOppos(hfcs[1]);
			hfcs[1]->setOppos(hfcs[0]);
		}
	}
	return 0;
}