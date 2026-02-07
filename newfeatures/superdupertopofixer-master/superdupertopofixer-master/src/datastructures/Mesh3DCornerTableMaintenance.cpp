/* Mesh3DCornerTableMaintenance.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru
 *
 * This is the implementation file for the mesh corner table, containing implementations of
 * functions related to performing mesh maintenance operations.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <algorithm>

#include "Mesh3DCornerTable.h"
#include "Mesh3DHalfCorner.h"
#include "Mesh3DTriangle.h"
#include "Mesh3DVertex.h"
#include "absl/container/flat_hash_set.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

//------------------------------------------------------------
// adding vertices
//------------------------------------------------------------

// make a new mesh vertex without specifying its coordinates, add it to list of vertices, assign it
// an integer label, and return a pointer to it
Mesh3DVertex* Mesh3DCornerTable::makeNewVertex() {
	Mesh3DVertex* new_v = new Mesh3DVertex();
	mesh_vertices_list.insert(new_v);
	vertex_index_map[new_v] = vertex_index_to_assign;
	vertex_index_to_assign--;
	vertex_to_hfc_map[new_v] = {};
	return new_v;
}

// make a new mesh vertex at input coordinates, add it to list of vertices, assign it an integer
// label, and return a pointer to it
Mesh3DVertex* Mesh3DCornerTable::makeNewVertexAtCoords(Vec3d vert_coords, VertexProperties vert_props) {
	Mesh3DVertex* new_v = makeNewVertex();
	new_v->setCoords(vert_coords);
	new_v->setProperties(vert_props);
	return new_v;
}

Mesh3DVertex* Mesh3DCornerTable::makeNewVertexAtCoords(Vec3d vert_coords) {
	return makeNewVertexAtCoords(vert_coords, VertexProperties());
}

// make a new mesh vertex at the center of mass of the input triangle, add it to list of vertices,
// assign it an integer label, and return a pointer to it
Mesh3DVertex* Mesh3DCornerTable::makeNewVertexAtTriangleMassCenter(Mesh3DTriangle* triangle) {
	Mesh3DVertex *v1, *v2, *v3;
	triangle->getVerts(&v1, &v2, &v3);
	Vec3d c1 = v1->getCoords();
	Vec3d c2 = v2->getCoords();
	Vec3d c3 = v3->getCoords();
	return makeNewVertexAtCoords((c1 + c2 + c3) / 3.0);
}

// make a new mesh vertex at the center of the input edge, add it to list of vertices, assign it an
// integer label, and return a pointer to it
Mesh3DVertex* Mesh3DCornerTable::makeNewVertexAtEdgeMidpoint(Mesh3DVertex* v1, Mesh3DVertex* v2) {
	Vec3d c1 = v1->getCoords();
	Vec3d c2 = v2->getCoords();
	return makeNewVertexAtCoords((c1 + c2) / 2.0);
}

//------------------------------------------------------------
// adding half-corners
//------------------------------------------------------------

Mesh3DHalfCorner* Mesh3DCornerTable::makeNewHalfCorner(Mesh3DVertex* v, Mesh3DTriangle* t,
                                                       bool label_side) {
	Mesh3DHalfCorner* hfc = new Mesh3DHalfCorner(v, t, label_side);
	mesh_half_corners_list.insert(hfc);
	vertex_to_hfc_map[v].insert(hfc);
	return hfc;
}

//------------------------------------------------------------
// adding triangles
//------------------------------------------------------------

// make a new mesh triangle between the three input vertices, with the input labels; also make its 6
// new half-corners, define their `next`, `prev`, `dual` pointers (oppos pointers have to be set
// externally); check if each input vertex has a half-corner assigned, if not, assign it a newly
// generated half-corner on the 0-label side of the newly generated triangle; return a pointer to
// the new triangle
Mesh3DTriangle* Mesh3DCornerTable::makeNewTriangle(Mesh3DVertex* v0, Mesh3DVertex* v1,
                                                   Mesh3DVertex* v2, Vec2i labels) {
	Mesh3DTriangle* triangle = new Mesh3DTriangle(labels);
	// add the new triangle to the list of triangles
	mesh_triangles_list.insert(triangle);

	// generate the 6 half-corners of the new triangle
	Mesh3DHalfCorner* c0 = makeNewHalfCorner(v0, triangle, false);
	Mesh3DHalfCorner* c1 = makeNewHalfCorner(v1, triangle, false);
	Mesh3DHalfCorner* c2 = makeNewHalfCorner(v2, triangle, false);
	Mesh3DHalfCorner* c3 = makeNewHalfCorner(v0, triangle, true);
	Mesh3DHalfCorner* c4 = makeNewHalfCorner(v2, triangle, true);
	Mesh3DHalfCorner* c5 = makeNewHalfCorner(v1, triangle, true);

	// set the local connectivity pointers (next,prev,dual) of the 6 new half-corners
	c0->setLocalConnectivity(c1, c2, c3);
	c1->setLocalConnectivity(c2, c0, c5);
	c2->setLocalConnectivity(c0, c1, c4);
	c3->setLocalConnectivity(c4, c5, c0);
	c4->setLocalConnectivity(c5, c3, c2);
	c5->setLocalConnectivity(c3, c4, c1);

	// set a reference half corner for the new triangle (at `v0`, on label side 0)
	triangle->setHalfCorner(c0);
	return triangle;
}

//------------------------------------------------------------
// updating HFC info
//------------------------------------------------------------

void Mesh3DCornerTable::setHFCVertex(Mesh3DHalfCorner* hfc, Mesh3DVertex* v) {
	Mesh3DVertex* prev_vertex = hfc->getVertex();
	if (prev_vertex != nullptr) {
		vertex_to_hfc_map[prev_vertex].erase(hfc);
	}
	hfc->setVertex(v);
	if (v != nullptr) {
		vertex_to_hfc_map[v].insert(hfc);
	}
}

//------------------------------------------------------------
// removing elements
//------------------------------------------------------------

// deletes all saved vertices, triangles, and half-corners
void Mesh3DCornerTable::clear() {
	for (Mesh3DVertex* vertex : mesh_vertices_list) {
		delete vertex;
	}
	for (Mesh3DTriangle* triangle : mesh_triangles_list) {
		delete triangle;
	}
	for (Mesh3DHalfCorner* hfc : mesh_half_corners_list) {
		delete hfc;
	}

	mesh_vertices_list.clear();
	mesh_triangles_list.clear();
	mesh_half_corners_list.clear();
	vertex_to_hfc_map.clear();
}

//------------------------------------------------------------
// delete triangles
//------------------------------------------------------------

// deletes input triangle, and its 6 HCs, and adjusts all relevant pointers
void Mesh3DCornerTable::deleteTriangle(const Mesh3DTriangle* triangle) {
	// retrieve the 6 HCs of the triangle
	Mesh3DHalfCorner* hfc1 = triangle->getHalfCorner();
	std::vector<Mesh3DHalfCorner*> hfcs = {hfc1,
	                                       hfc1->getNext(),
	                                       hfc1->getPrev(),
	                                       hfc1->getDual(),
	                                       hfc1->getNext()->getDual(),
	                                       hfc1->getPrev()->getDual()};

	for (Mesh3DHalfCorner* hfc : hfcs) {
		if (hfc->getOppos() != nullptr && hfc->getOppos()->getOppos() == hfc) {
			hfc->getOppos()->setOppos(nullptr);
		}
		deleteHalfCorner(hfc);
	}
	// delete triangle:
	mesh_triangles_list.erase(triangle);
	delete triangle;
}

//------------------------------------------------------------
// delete vertices
//------------------------------------------------------------

// deletes input vertex
void Mesh3DCornerTable::deleteVertex(Mesh3DVertex* vertex) {
	delete vertex;
	mesh_vertices_list.erase(vertex);
	vertex_index_map.erase(vertex);
	for (Mesh3DHalfCorner* hfc : vertex_to_hfc_map[vertex]) {
		hfc->setVertex(nullptr);
	}
	vertex_to_hfc_map.erase(vertex);
}

//------------------------------------------------------------
// delete half-corners
//------------------------------------------------------------

void Mesh3DCornerTable::deleteHalfCorner(Mesh3DHalfCorner* hfc) {
	mesh_half_corners_list.erase(hfc);
	Mesh3DVertex* v = hfc->getVertex();
	if (v != nullptr) {
		vertex_to_hfc_map[v].erase(hfc);
	}
	delete hfc;
}

//------------------------------------------------------------
// integer indices for deterministic intersections
//------------------------------------------------------------

// clears `vertex_index_map`, and assigns negative integer indices to all mesh vertices from scratch
void Mesh3DCornerTable::assignVertexIndexMap() {
	vertex_index_map.clear();
	int vertex_index = -1;
	for (Mesh3DVertex* vertex : mesh_vertices_list) {
		vertex_index_map[vertex] = vertex_index;
		--vertex_index;
	}
	vertex_index_to_assign = vertex_index;
}

// returns the integer index of input `vertex`
int Mesh3DCornerTable::getVertexIndex(Mesh3DVertex* vertex) const {
	return vertex_index_map.at(vertex);
}

//------------------------------------------------------------
// mesh test functions
//------------------------------------------------------------

// performs mesh consistency checks, returns 0 is all tests passed, 1 if critical tests passed, some
// optional failed, 2 if some critical tests failed
// TODO: add more tests
int Mesh3DCornerTable::runMeshConsistencyChecks() {
	int return_value = 0;

	// OPTIONAL: check if all vertices have a reference half-corner
	if (settings->run_input_mesh_consistency_tests == TopoFixerSettings::InputMeshConsistencyTests::All) {
		size_t it = 0;
		for (Mesh3DVertex* vert : mesh_vertices_list) {
			auto hfc_it = vertex_to_hfc_map.find(vert);
			if (hfc_it == vertex_to_hfc_map.end() || hfc_it->second.empty()) {
				if (settings->verbosity >= 1) {
					std::cout << "-WARNING: vertex " << it << " at memory address " << vert
					          << " doesn't have any associated half-corners, it is not part of any triangle, "
					             "unexpected behavior might occur\n";
				}
				return_value = 1;
			}
			it++;
		}
	}

	// OPTIONAL: check if all materials are non-negative integers
	if (settings->run_input_mesh_consistency_tests ==
	    TopoFixerSettings::InputMeshConsistencyTests::All) {
		size_t it = 0;
		for (Mesh3DTriangle* tri : mesh_triangles_list) {
			if (tri->getLabel(0) < 0 || tri->getLabel(1) < 0) {
				if (settings->verbosity >= 1) {
					std::cout << "-WARNING: triangle " << it << " at address " << tri
					          << " has negative material label(s) (" << tri->getLabel(0) << ","
					          << tri->getLabel(1) << "), unexpected behavior might occur\n ";
				}
				return_value = 1;
			}
			it++;
		}
	}

	// CRITICAL: check if all half-corners have a vertex assigned
	if (settings->run_input_mesh_consistency_tests ==
	    TopoFixerSettings::InputMeshConsistencyTests::All) {
		for (Mesh3DHalfCorner* hfc : mesh_half_corners_list) {
			if (hfc->getVertex() == nullptr) {
				if (settings->verbosity >= 1) {
					std::cout << "-CRITICAL: half corner " << hfc << " has no vertex assigned, quitting\n";
				}
				return_value = 2;
				return return_value;
			}
		}
	}

	// CRITICAL: check if all triangles have two distinct material labels
	if (settings->run_input_mesh_consistency_tests ==
	    TopoFixerSettings::InputMeshConsistencyTests::All) {
		size_t it = 0;
		for (Mesh3DTriangle* tri : mesh_triangles_list) {
			if (tri->getLabel(0) == tri->getLabel(1)) {
				if (settings->verbosity >= 1) {
					std::cout << "-CRITICAL: triangle " << it << " at address " << tri
					          << " has the same material label " << tri->getLabel(0)
					          << "on both its sides, quitting\n";
				}
				return_value = 2;
				return return_value;
			}
			it++;
		}
	}

	// CRITICAL: check if all half-corners have an opposite assigned
	// only useful when loading from a binary file, unnecessary when loading from an obj file, since
	// this check is performed during opposites assignment
	for (auto hc : mesh_half_corners_list) {
		if (hc->getOppos() == nullptr) {
			if (settings->verbosity >= 1) {
				std::cout << "-CRITICAL: half-corner " << hc << " has no opposite assigned";
			}
			return_value = 2;
			return return_value;
		}
	}

	// CRITICAL: check that mutually opposite half-corners are consistently pointing to each other
	for (auto& hc : mesh_half_corners_list) {
		if (hc->getOppos()->getOppos() != hc) {
			if (settings->verbosity >= 1) {
				std::cout
				    << "-CRITICAL: half-corner " << hc << " has the assigned opposite hfc "
				    << hc->getOppos()
				    << ", but the opposite of the latter is not the original half-corner, instead it's "
				    << hc->getOppos()->getOppos();
			}
			return_value = 2;
			return return_value;
		}
	}

	// CRITICAL: check that mutually opposite half-corners are extending the same edge
	for (auto& hc : mesh_half_corners_list) {
		Mesh3DHalfCorner* oppos = hc->getOppos();
		if (hc->getNext()->getVertex() != oppos->getPrev()->getVertex()) {
			if (settings->verbosity >= 1) {
				std::cout << "-CRITICAL: half-corner " << hc << " has the vertex at next half-corner "
				          << hc->getNext()->getVertex()
				          << ", but the opposite of this half-corner has a different vertex at its "
				             "previous half-corner: "
				          << oppos->getPrev()->getVertex();
			}
			return_value = 2;
			return return_value;
		}
		if (hc->getPrev()->getVertex() != oppos->getNext()->getVertex()) {
			if (settings->verbosity >= 1) {
				std::cout << "-CRITICAL: half-corner " << hc << " has the vertex at prev half-corner "
				          << hc->getPrev()->getVertex()
				          << ", but the opposite of this half-corner has a different vertex at its next "
				             "half-corner: "
				          << oppos->getNext()->getVertex();
			}
			return_value = 2;
			return return_value;
		}
	}

	// CRITICAL: check if all opposites have the same material
	for (Mesh3DTriangle* tri : mesh_triangles_list) {
		for (Mesh3DHalfCorner* hc : tri->getHalfCorners()) {
			if (hc->getOppos() != nullptr) {
				if (hc->getLabel() != hc->getOppos()->getLabel()) {
					if (settings->verbosity >= 1) {
						std::cout << "-CRITICAL: half-corner at address " << hc << " at vertex "
						          << hc->getVertex() << " of triangle " << tri << " has material label "
						          << hc->getLabel() << " but its opposite half-corner at address "
						          << hc->getOppos() << " has material label " << hc->getOppos()->getLabel()
						          << ", quitting\n";
					}
					return_value = 2;
					return return_value;
				}
			}
		}
	}

	// CRITICAL: check that opposite half-corners do not share the same vertex
	for (auto& hc : mesh_half_corners_list) {
		if (hc->getOppos()->getVertex() == hc->getVertex()) {
			if (settings->verbosity >= 1) {
				std::cout << "-CRITICAL: half-corner " << hc << " has the assigned opposite hfc "
				          << hc->getOppos() << "and they both have the same vertex " << hc->getVertex()
				          << std::endl;
			}
			return_value = 2;
			return return_value;
		}
	}

	// return 0 if all tests passed, or 1 if some optional tests failed (if a critical test
	// failed, we can't reach this point)
	return return_value;
}

void Mesh3DCornerTable::clearNonPersistentState() {
	mc_triangles.clear();
	t1_triangles.clear();
	t1_hf_triangles.clear();
	no_collapse_edges.clear();
	clearEdgeCollapseCounters();
}

void Mesh3DCornerTable::defragmentMesh() {
	std::vector<Mesh3DTriangle*> temp_triangles(mesh_triangles_list.begin(),
	                                            mesh_triangles_list.end());
	std::vector<Mesh3DVertex*> temp_vertices(mesh_vertices_list.begin(), mesh_vertices_list.end());
	std::vector<Mesh3DHalfCorner*> temp_halfcorners(mesh_half_corners_list.begin(),
	                                                mesh_half_corners_list.end());

	std::vector<std::pair<Mesh3DVertex*, std::vector<Mesh3DHalfCorner*>>> temp_vertex_to_hfc;
	for (auto& [vertex, hfcs] : vertex_to_hfc_map) {
		std::vector<Mesh3DHalfCorner*> hfc_vec(hfcs.begin(), hfcs.end());
		temp_vertex_to_hfc.emplace_back(vertex, hfc_vec);
	}

	mesh_triangles_list.clear();
	mesh_vertices_list.clear();
	mesh_half_corners_list.clear();
	vertex_to_hfc_map.clear();

	mesh_triangles_list.insert(temp_triangles.begin(), temp_triangles.end());
	mesh_vertices_list.insert(temp_vertices.begin(), temp_vertices.end());
	mesh_half_corners_list.insert(temp_halfcorners.begin(), temp_halfcorners.end());

	for (auto& [vertex, hfcs] : temp_vertex_to_hfc) {
		vertex_to_hfc_map[vertex] = {hfcs.begin(), hfcs.end()};
	}
}
