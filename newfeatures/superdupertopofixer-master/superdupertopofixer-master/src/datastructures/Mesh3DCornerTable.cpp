/* Mesh3DCornerTable.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the implementation file for the corner table mesh implementation.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "Mesh3DCornerTable.h"

#include <chrono>
#include <limits>
#include <memory>
#include <unordered_set>

#include "../utilities/vec.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"
//------------------------------------------------------------
// constructors
//------------------------------------------------------------

// default constructor
Mesh3DCornerTable::Mesh3DCornerTable(const TopoFixerSettings& settings)
    : settings(&settings),
      vertex_index_to_assign(-1),
      kShortEdgeThreshold(settings.mesh_short_edge_threshold) {}

//------------------------------------------------------------
// functions
//------------------------------------------------------------

//------------------------------------------------------------
// retrieve mesh information functions
//------------------------------------------------------------

// number of materials in use
int Mesh3DCornerTable::getNumberLabels() const {
	absl::flat_hash_set<int> materials;
	for (auto triangle : mesh_triangles_list) {
		int lr, ll;
		triangle->getLabels(lr, ll);
		materials.insert(lr);
		materials.insert(ll);
	}
	return materials.size();
}

//------------------------------------------------------------
// functions for retrieving drawing information
//------------------------------------------------------------

// fill in a vector of vertex positions for drawing
void Mesh3DCornerTable::getVertexPositions(std::vector<Vec3d>& vertex_positions) {
	vertex_positions.clear();
	vertex_positions.reserve(mesh_vertices_list.size());
	for (auto it = mesh_vertices_list.begin(); it != mesh_vertices_list.end(); it++) {
		vertex_positions.push_back((*it)->getCoords());
	}
}

Vec3d Mesh3DCornerTable::getMeshCenter() {
	Vec3d center(0.0);
	if (mesh_vertices_list.empty()) {
		return center;
	}
	for (auto& v : mesh_vertices_list) {
		center += v->getCoords();
	}
	return center / mesh_vertices_list.size();
}

bool Mesh3DCornerTable::isPointInTri(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3,
                                     Mesh3DVertex* vert) const {
	Vec3d vert_coords = vert->getCoords();
	Vec3d v1_coords = v1->getCoords();
	Vec3d v2_coords = v2->getCoords();
	Vec3d v3_coords = v3->getCoords();
	Vec3d ab = v2_coords - v1_coords, ac = v3_coords - v1_coords, ap = vert_coords - v1_coords;
	double ac2 = dot(ac, ac), ab2 = dot(ab, ab), abac = dot(ab, ac), acap = dot(ac, ap),
	       abap = dot(ab, ap), inv_denom = 1 / (ac2 * ab2 - abac * abac), u, v;
	u = (ab2 * acap - abac * abap) * inv_denom;
	v = (ac2 * abap - abac * acap) * inv_denom;
	return u >= 0 && v >= 0 && (u + v < 1);
}

//--------------------------------------------------------------
// other stuff for getting mesh elements
//--------------------------------------------------------------

// go through manifold loop around center_vertex, starting from given start_halfcorner (no switching
// to duals), output_corners returns a vector which contains a halfcorner for each vertex in the
// link of the center vertex NOTE: does the halfcorner need to be at the center vertex?
void Mesh3DCornerTable::walkManifoldLoop(Mesh3DVertex* center, Mesh3DHalfCorner* start_halfcorner,
                                         std::vector<Mesh3DHalfCorner*>& output_corners) {
	start_halfcorner = start_halfcorner->getNext();
	Mesh3DHalfCorner* current_halfcorner = start_halfcorner;

	// walk around center vertex by calling at halfcorner pointers at each encountered halfcorner:
	do {
		output_corners.push_back(current_halfcorner);
		current_halfcorner = current_halfcorner->getNext()->getOppos();

	} while (current_halfcorner != start_halfcorner);
}

// get a vector of all hfc extending an edge:
std::vector<Mesh3DHalfCorner*> Mesh3DCornerTable::hfcsAroundEdge(
    Mesh3DHalfCorner* start_halfcorner) const {
	Mesh3DHalfCorner* current_halfcorner = start_halfcorner;
	std::vector<Mesh3DHalfCorner*> hfcs_around_edge;
	do {
		hfcs_around_edge.push_back(current_halfcorner);

		current_halfcorner = current_halfcorner->getOppos()->getDual();

	} while (current_halfcorner != start_halfcorner);
	return hfcs_around_edge;
}

//--------------------------------------------------------------
// Mesh Operations
//--------------------------------------------------------------

// does segment intersect mesh?
int Mesh3DCornerTable::lineIntersectsMesh(Mesh3DVertex* v1, Mesh3DVertex* v2) {
	for (auto tri = mesh_triangles_list.begin(); tri != mesh_triangles_list.end(); tri++) {
		if (intersectTriSegmentNoVerts((*tri), v1, v2))
			return 1;
	}
	return 0;
}

// returns coords of point v on edge v1, v2, such that v = p*v1 + (1-p)*v2:
Vec3d Mesh3DCornerTable::pVertCoords(Mesh3DVertex* v1, Mesh3DVertex* v2, double p) {
	return p * v1->getCoords() + (1 - p) * v2->getCoords();
}

Mesh3DVertex* Mesh3DCornerTable::triangleSubdivFixedPoint(Mesh3DTriangle*& main_triangle,
                                                          Mesh3DTriangle*& second_triangle,
                                                          Mesh3DTriangle*& third_triangle,
                                                          Vec3d vert_coords) {
	Mesh3DVertex *center_v = makeNewVertexAtCoords(vert_coords), *v1, *v2, *v3;
	main_triangle->getVerts(&v1, &v2, &v3);
	int label_rh, label_lh;
	main_triangle->getLabels(label_rh, label_lh);

	Mesh3DTriangle *tri_c23 = new Mesh3DTriangle(), *tri_c31 = new Mesh3DTriangle();
	mesh_triangles_list.insert(tri_c23);
	mesh_triangles_list.insert(tri_c31);

	Mesh3DHalfCorner *hfc1 = main_triangle->getHalfCornerAtVertex(v1), *hfc2, *hfc3, *hfc1_back,
	                 *hfc2_back, *hfc3_back, *hf_1c2, *hf_2c3, *hf_3c1, *hf_1c2_back, *hf_2c3_back,
	                 *hf_3c1_back, *hfc1_left, *hfc2_left, *hfc3_left, *hfc1_left_back,
	                 *hfc2_left_back, *hfc3_left_back;
	if (hfc1->getLabelSide())
		hfc1 = hfc1->getDual();
	// now hfc1 = hfc at v1, on side 0
	hfc2 = hfc1->getNext();
	hfc3 = hfc1->getPrev();
	hfc1_back = hfc1->getDual();
	hfc2_back = hfc2->getDual();
	hfc3_back = hfc3->getDual();

	// set triangle for hfc1, 2, 3:
	hfc1->setTri(tri_c31);
	hfc1_back->setTri(tri_c31);
	hfc3->setTri(tri_c23);
	hfc3_back->setTri(tri_c23);

	// new corners at the center:
	hf_1c2 = makeNewHalfCorner(center_v, main_triangle, 0);
	hf_2c3 = makeNewHalfCorner(center_v, tri_c23, 0);
	hf_3c1 = makeNewHalfCorner(center_v, tri_c31, 0);
	// corners at the center backside:
	hf_1c2_back = makeNewHalfCorner(center_v, main_triangle, 1);
	hf_2c3_back = makeNewHalfCorner(center_v, tri_c23, 1);
	hf_3c1_back = makeNewHalfCorner(center_v, tri_c31, 1);
	// new corners at v1, v2, v3:
	hfc1_left = makeNewHalfCorner(v1, main_triangle, 0);
	hfc2_left = makeNewHalfCorner(v2, tri_c23, 0);
	hfc3_left = makeNewHalfCorner(v3, tri_c31, 0);
	hfc1_left_back = makeNewHalfCorner(v1, main_triangle, 1);
	hfc2_left_back = makeNewHalfCorner(v2, tri_c23, 1);
	hfc3_left_back = makeNewHalfCorner(v3, tri_c31, 1);

	// set connectivity center verts:
	hf_1c2->setLocalConnectivity(hfc1_left, hfc2, hf_1c2_back);
	hf_1c2->setOppos(hfc3->getOppos());
	hfc3->getOppos()->setOppos(hf_1c2);
	hf_1c2_back->setLocalConnectivity(hfc2_back, hfc1_left_back, hf_1c2);
	hf_1c2_back->setOppos(hfc3_back->getOppos());
	hfc3_back->getOppos()->setOppos(hf_1c2_back);

	hf_2c3->setLocalConnectivity(hfc2_left, hfc3, hf_2c3_back);
	hf_2c3->setOppos(hfc1->getOppos());
	hfc1->getOppos()->setOppos(hf_2c3);
	hf_2c3_back->setLocalConnectivity(hfc3_back, hfc2_left_back, hf_2c3);
	hf_2c3_back->setOppos(hfc1_back->getOppos());
	hfc1_back->getOppos()->setOppos(hf_2c3_back);

	hf_3c1->setLocalConnectivity(hfc3_left, hfc1, hf_3c1_back);
	hf_3c1->setOppos(hfc2->getOppos());
	hfc2->getOppos()->setOppos(hf_3c1);
	hf_3c1_back->setLocalConnectivity(hfc1_back, hfc3_left_back, hf_3c1);
	hf_3c1_back->setOppos(hfc2_back->getOppos());
	hfc2_back->getOppos()->setOppos(hf_3c1_back);

	// set connectivity for hfcs at v1:
	hfc1_left->setLocalConnectivity(hfc2, hf_1c2, hfc1_left_back);
	hfc1_left->setOppos(hfc3);
	hfc3->setOppos(hfc1_left);
	hfc1_left_back->setLocalConnectivity(hf_1c2_back, hfc2_back, hfc1_left);
	hfc1_left_back->setOppos(hfc3_back);
	hfc3_back->setOppos(hfc1_left_back);

	hfc1->setNext(hf_3c1);
	hfc1->setPrev(hfc3_left);
	hfc1_back->setNext(hfc3_left_back);
	hfc1_back->setPrev(hf_3c1_back);

	// set connectivity for hfcs at v2:
	hfc2_left->setLocalConnectivity(hfc3, hf_2c3, hfc2_left_back);
	hfc2_left->setOppos(hfc1);
	hfc1->setOppos(hfc2_left);
	hfc2_left_back->setLocalConnectivity(hf_2c3_back, hfc3_back, hfc2_left);
	hfc2_left_back->setOppos(hfc1_back);
	hfc1_back->setOppos(hfc2_left_back);

	hfc2->setNext(hf_1c2);
	hfc2->setPrev(hfc1_left);
	hfc2_back->setNext(hfc1_left_back);
	hfc2_back->setPrev(hf_1c2_back);

	// set connectivity for hfcs at v3:

	hfc3_left->setLocalConnectivity(hfc1, hf_3c1, hfc3_left_back);
	hfc3_left->setOppos(hfc2);
	hfc2->setOppos(hfc3_left);
	hfc3_left_back->setLocalConnectivity(hf_3c1_back, hfc1_back, hfc3_left);
	hfc3_left_back->setOppos(hfc2_back);
	hfc2_back->setOppos(hfc3_left_back);

	hfc3->setNext(hf_2c3);
	hfc3->setPrev(hfc2_left);
	hfc3_back->setNext(hfc2_left_back);
	hfc3_back->setPrev(hf_2c3_back);

	// set tris for hfc1, 2, 3:
	hfc1->setTri(tri_c31);
	hfc3->setTri(tri_c23);

	// assign verts and hfc for new triangles:
	tri_c23->setHalfCorner(hf_2c3);
	tri_c23->setLabels(label_rh, label_lh);
	tri_c31->setHalfCorner(hf_3c1);
	tri_c31->setLabels(label_rh, label_lh);
	main_triangle->setHalfCorner(hfc1_left);

	second_triangle = tri_c23;
	third_triangle = tri_c31;
	return center_v;
}

Mesh3DVertex* Mesh3DCornerTable::EdgeSubdivisionFixedPoint(
    Mesh3DTriangle* triangle, Mesh3DVertex* v1, Mesh3DVertex* v2, Vec3d vert_coords,
    std::vector<Mesh3DTriangle*>& created_triangles) {
	// create v3 on subdiv edge:
	Mesh3DVertex* new_vertex = makeNewVertexAtCoords(vert_coords);
	transferValuesEdgeSubdivision(v1, v2, new_vertex);

	// get a halfcorner extending over (v1, v2)
	Mesh3DHalfCorner* first_halfcorner;
	first_halfcorner = triangle->getHalfCorner();
	// printf("v1, v2, new_v: %p, %p, %p\n", v1, v2, new_vertex);
	while (first_halfcorner->getVertex() == v1 || first_halfcorner->getVertex() == v2) {
		first_halfcorner = first_halfcorner->getNext();
	}
	if (first_halfcorner->getNext()->getVertex() == v2)
		first_halfcorner = first_halfcorner->getDual();
	// in triangle, first_halfcorner is now an opposite hafcorner to edge(v1, v2), on a side where the
	// rhs goes: v1->v2

	Mesh3DHalfCorner *first2_back = nullptr, *oppos2_back = nullptr, *current_hfc1 = first_halfcorner,
	                 *current_hfc1_back, *current_hfc2, *current_hfc2_back, *v1_hfc, *v1_hfc_back,
	                 *v2_hfc, *v2_hfc_back, *newv_hfc1 = nullptr, *newv_hfc1_back, *newv_hfc2,
	                 *newv_hfc2_back;
	Mesh3DTriangle *triangle1 = triangle, *triangle2;
	int hfc_count = 0, label_rh, label_lh, current_label_side;

	Mesh3DVertex* v3;
	while (hfc_count == 0 || current_hfc1 != first_halfcorner) {
		// printf("hfc count: %d \n", hfc_count);
		v3 = current_hfc1->getVertex();
		current_label_side = current_hfc1->getLabelSide();
		triangle1 = current_hfc1->getTri();
		triangle1->getLabels(label_rh, label_lh);
		triangle2 = new Mesh3DTriangle();
		mesh_triangles_list.insert(triangle2);
		current_hfc1_back = current_hfc1->getDual();
		v1_hfc = current_hfc1->getNext();
		v2_hfc = current_hfc1->getPrev();
		v1_hfc_back = v1_hfc->getDual();
		v2_hfc_back = v2_hfc->getDual();
		// v2_hfc and v2_hfc_back are now part of triangle2:
		v2_hfc->setTri(triangle2);
		v2_hfc_back->setTri(triangle2);

		created_triangles.push_back(triangle1);
		created_triangles.push_back(triangle2);

		// new halfcorners:
		current_hfc2 = makeNewHalfCorner(v3, triangle2, current_label_side);
		current_hfc2_back = makeNewHalfCorner(v3, triangle2, !current_label_side);
		newv_hfc1 = makeNewHalfCorner(new_vertex, triangle1, current_label_side);
		newv_hfc1_back = makeNewHalfCorner(new_vertex, triangle1, !current_label_side);
		newv_hfc2 = makeNewHalfCorner(new_vertex, triangle2, current_label_side);
		newv_hfc2_back = makeNewHalfCorner(new_vertex, triangle2, !current_label_side);

		// set hfc for new triangle:
		triangle2->setLabels(label_rh, label_lh);
		if (current_label_side == 0) {
			triangle1->setHalfCorner(current_hfc1);
			triangle2->setHalfCorner(current_hfc2);
		} else {
			triangle1->setHalfCorner(current_hfc1_back);
			triangle2->setHalfCorner(current_hfc2_back);
		}

		/*printf("tri1 hfc v: %p\t\t tri2 hfc v: %p\n", triangle1->getHalfCorner()->getVertex(),
		       triangle2->getHalfCorner()->getVertex());*/

		// set connectivity for new halfcorners:
		newv_hfc1->setLocalConnectivity(current_hfc1, v1_hfc, newv_hfc1_back);
		newv_hfc1_back->setLocalConnectivity(v1_hfc_back, current_hfc1_back, newv_hfc1);
		newv_hfc2->setLocalConnectivity(v2_hfc, current_hfc2, newv_hfc2_back);
		newv_hfc2_back->setLocalConnectivity(current_hfc2_back, v2_hfc_back, newv_hfc2);
		current_hfc2->setLocalConnectivity(newv_hfc2, v2_hfc, current_hfc2_back);
		current_hfc2_back->setLocalConnectivity(v2_hfc_back, newv_hfc2_back, current_hfc2);

		// set next and prev for v1, v2, current hfc1:
		current_hfc1->setPrev(newv_hfc1);
		current_hfc1_back->setNext(newv_hfc1_back);
		v1_hfc->setNext(newv_hfc1);
		v1_hfc_back->setPrev(newv_hfc1_back);
		v2_hfc->setNext(current_hfc2);
		v2_hfc->setPrev(newv_hfc2);
		v2_hfc_back->setNext(newv_hfc2_back);
		v2_hfc_back->setPrev(current_hfc2_back);

		// set opposites:
		newv_hfc1->setOppos(v2_hfc->getOppos());
		if (v2_hfc->getOppos() != nullptr)
			v2_hfc->getOppos()->setOppos(newv_hfc1);
		newv_hfc1_back->setOppos(v2_hfc_back->getOppos());
		if (v2_hfc_back->getOppos() != nullptr)
			v2_hfc_back->getOppos()->setOppos(newv_hfc1_back);

		newv_hfc2->setOppos(v1_hfc->getOppos());
		if (v1_hfc->getOppos() != nullptr)
			v1_hfc->getOppos()->setOppos(newv_hfc2);
		newv_hfc2_back->setOppos(v1_hfc_back->getOppos());
		if (v1_hfc_back->getOppos() != nullptr)
			v1_hfc_back->getOppos()->setOppos(newv_hfc2_back);

		v1_hfc->setOppos(v2_hfc);
		v2_hfc->setOppos(v1_hfc);
		v1_hfc_back->setOppos(v2_hfc_back);
		v2_hfc_back->setOppos(v1_hfc_back);

		// if this is the first corner, save its back corner2 to pair it with the last current corner2
		// in the loop:
		if (hfc_count == 0) {
			first2_back = current_hfc2_back;
		}
		// if it's not the firsthfc, pair its back hfc2 to the previous hfc2:
		else {
			current_hfc2_back->setOppos(oppos2_back);
			oppos2_back->setOppos(current_hfc2_back);
		}

		// make the current hfc2 the new pair for the next back hfc2:
		oppos2_back = current_hfc2;
		current_hfc1 = current_hfc1->getOppos()->getDual();
		hfc_count++;
	}

	// the first corner doesn't have an opposite for back2; we pair it with the last current_hfc2:
	first2_back->setOppos(oppos2_back);
	oppos2_back->setOppos(first2_back);
	return new_vertex;
}

void Mesh3DCornerTable::transferValuesEdgeSubdivision(Mesh3DVertex* v1, Mesh3DVertex* v2,
                                                      Mesh3DVertex* new_vertex) {
	Vec3d v1_coords = v1->getCoords();
	Vec3d v2_coords = v2->getCoords();
	Vec3d new_coords = new_vertex->getCoords();
	Vec3d diff = v2_coords - v1_coords;
	double diff_sq = mag2(diff);
	// Interpolate linearly if points are a bit apart. Otherwise, just take the average to avoid
	// numerical problems.
	double alpha = 0.5;
	if (diff_sq > 1e-200) {
		alpha = dot(new_coords - v1_coords, diff) / diff_sq;
	}
	new_vertex->setProperties(
	    VertexProperties::linearInterpolation(v1->getProperties(), v2->getProperties(), alpha));
};

// for manifold edges:
// flips the edge (v1, v2) in triangle:
// Does NOT fully check for the criterion of target edge (v3, v4) not already existing in the mesh.
// Only rejects tetrahedrhon cases.
// Not fully debugged. On a stress case (flipping an edge in each triangle, it messes up the
// geometry. Similarly to the edge collapse case, a check of the order of the halfcorners around an
// edge might help
bool Mesh3DCornerTable::EdgeFlipFast(Mesh3DTriangle* main_triangle, Mesh3DVertex* v1,
                                     Mesh3DVertex* v2) {
	Mesh3DTriangle* triangle = main_triangle;
	Mesh3DVertex *v3, *v4;
	Mesh3DHalfCorner *hfc1_3 = triangle->getHalfCornerAtVertex(v1), *hfc1_4, *hfc2_3, *hfc2_4, *hfc3,
	                 *hfc4, *hfc1_3_back, *hfc1_4_back, *hfc2_3_back, *hfc2_4_back, *hfc3_back,
	                 *hfc4_back;
	if (hfc1_3->getNext()->getVertex() != v2) {
		hfc1_3 = hfc1_3->getDual();
	}

	hfc2_3 = hfc1_3->getNext();
	hfc3 = hfc1_3->getPrev();
	hfc4 = hfc3->getOppos();
	hfc2_4 = hfc4->getNext();
	hfc1_4 = hfc4->getPrev();

	hfc1_3_back = hfc1_3->getDual();
	hfc1_4_back = hfc1_4->getDual();
	hfc2_3_back = hfc2_3->getDual();
	hfc2_4_back = hfc2_4->getDual();
	hfc3_back = hfc3->getDual();
	hfc4_back = hfc4->getDual();

	if (isEdgeNonmanifold(hfc3)) {
		return false;
	}

	// forbid tetrahedron case:
	if ((hfc3->getNext()->getOppos()->getVertex() == hfc3->getPrev()->getOppos()->getVertex()) ||
	    (hfc3->getDual()->getNext()->getOppos()->getVertex() ==
	     hfc3->getDual()->getPrev()->getOppos()->getVertex())) {
		if (settings->verbosity >= 3) {
			std::cout << "tetrahedron->not valid" << std::endl;
			return false;
		}
	}
	if ((hfc4->getNext()->getOppos()->getVertex() == hfc4->getPrev()->getOppos()->getVertex()) ||
	    (hfc4->getDual()->getNext()->getOppos()->getVertex() ==
	     hfc4->getDual()->getPrev()->getOppos()->getVertex())) {
		if (settings->verbosity >= 3) {
			std::cout << "tetrahedron->not valid" << std::endl;
			return false;
		}
	}

	if (hfc1_3->getOppos()->getTri() == hfc1_4->getOppos()->getTri() ||
	    hfc2_3->getOppos()->getTri() == hfc2_4->getOppos()->getTri()) {
		std::cout << "not flipped because double tri" << std::endl;
		return false;
	}
	//
	v3 = hfc3->getVertex();
	v4 = hfc4->getVertex();
	Vec3d pos1 = v1->getCoords();
	Vec3d pos2 = v2->getCoords();
	Vec3d pos3 = v3->getCoords();
	Vec3d pos4 = v4->getCoords();

	// don't flip if triangles overlap
	if (intersector.orient3d(pos1.v, pos2.v, pos3.v, pos4.v) == 0) {
		if (isPointInTri(v3, v4, v1, v2) || isPointInTri(v3, v4, v2, v1)) {
			std::cout << "not flipped because overlapping triangles" << std::endl;
			return false;
		}
	}
	// // don't flip if the new edge would intersect mesh:
	// else if (lineIntersectsMesh(v3, v4)) {
	// 	std::cout << "not flipped because line intersects mesh" << std::endl;
	// 	return false;
	// }

	// Mesh3DVertex *vopp13 = hfc1_3->getVertex(), *vopp14 = hfc1_4->getVertex(),
	//             *vopp23 = hfc2_3->getVertex(), *vopp24 = hfc2_4->getVertex();
	// double* posopp13[3], posopp14[3], posopp23[3], posopp24[3];
	// vopp13->getCoordsArray(posopp13);
	// vopp14->getCoordsArray(posopp14);
	// vopp23->getCoordsArray(posopp23);
	// vopp24->getCoordsArray(posopp24);
	// if (intersector.orient3d(pos3, pos4, pos1, posopp23) == 0 ||
	//    intersector.orient3d(pos3, pos4, pos1, posopp24) == 0 ||
	//    intersector.orient3d(pos3, pos4, pos2, posopp13) == 0 ||
	//    intersector.orient3d(pos3, pos4, pos1, posopp14) == 0) {
	//	printf("not flipped, coplanar tris\n");
	//	return;
	//}

	int label_side_3 = hfc1_3->getLabelSide(), label_side_4 = hfc4->getLabelSide();
	Mesh3DTriangle* second_triangle = hfc4->getTri();

	// hfc2_4 ->triangle, hfc1_3 ->second_triangle
	hfc2_4->setTri(triangle);
	hfc1_3->setTri(second_triangle);
	hfc2_4_back->setTri(triangle);
	hfc1_3_back->setTri(second_triangle);

	// hfc1_3 ->v3, hfc2_4 ->v4
	setHFCVertex(hfc1_3, v3);
	setHFCVertex(hfc1_3_back, v3);
	setHFCVertex(hfc2_4, v4);
	setHFCVertex(hfc2_4_back, v4);

	// set hfc for triangles:
	if (label_side_3 == 0)
		triangle->setHalfCorner(hfc3);
	else
		triangle->setHalfCorner(hfc3_back);

	hfc2_4->setLabelSide(label_side_3);
	hfc2_4_back->setLabelSide(!label_side_3);

	// for second triangle:
	if (label_side_4 == 0)
		second_triangle->setHalfCorner(hfc4);
	else
		second_triangle->setHalfCorner(hfc4_back);

	hfc1_3->setLabelSide(label_side_4);
	hfc1_3_back->setLabelSide(!label_side_4);

	// set connectivity in second triangle:
	hfc1_3->setNext(hfc1_4);
	hfc1_3->setPrev(hfc4);
	hfc1_3_back->setNext(hfc4_back);
	hfc1_3_back->setPrev(hfc1_4_back);

	hfc1_4->setNext(hfc4);
	hfc1_4->setPrev(hfc1_3);
	hfc1_4_back->setNext(hfc1_3_back);
	hfc1_4_back->setPrev(hfc4_back);

	hfc4->setNext(hfc1_3);
	hfc4->setPrev(hfc1_4);
	hfc4_back->setNext(hfc1_4_back);
	hfc4_back->setPrev(hfc1_3_back);

	// set connectivity in first triangle:
	hfc2_3->setNext(hfc3);
	hfc2_3->setPrev(hfc2_4);
	hfc2_3_back->setNext(hfc2_4_back);
	hfc2_3_back->setPrev(hfc3_back);

	hfc2_4->setNext(hfc2_3);
	hfc2_4->setPrev(hfc3);
	hfc2_4_back->setNext(hfc3_back);
	hfc2_4_back->setPrev(hfc2_3_back);

	hfc3->setNext(hfc2_4);
	hfc3->setPrev(hfc2_3);
	hfc3_back->setNext(hfc2_3_back);
	hfc3_back->setPrev(hfc2_4_back);
	// Mesh3DVertex *vert1, *vert2, *vert3;

	// debug
	// printf("v1, v2, v3, v4: %p, %p, %p, %p\n", v1, v2, v3, v4);
	// triangle->getVerts(&vert1, &vert2, &vert3);
	// printf("triangle: %p, %p, %p\n", vert1, vert2, vert3);
	// second_triangle->getVerts(&vert1, &vert2, &vert3);
	// printf(" 2nd triangle: %p, %p, %p\n", vert1, vert2, vert3);

	// eo debug

	// set opposites:
	hfc3->setOppos(hfc1_4->getOppos());
	hfc1_4->getOppos()->setOppos(hfc3);
	hfc3_back->setOppos(hfc1_4_back->getOppos());
	hfc1_4_back->getOppos()->setOppos(hfc3_back);

	hfc4->setOppos(hfc2_3->getOppos());
	hfc2_3->getOppos()->setOppos(hfc4);
	hfc4_back->setOppos(hfc2_3_back->getOppos());
	hfc2_3_back->getOppos()->setOppos(hfc4_back);

	hfc1_4->setOppos(hfc2_3);
	hfc2_3->setOppos(hfc1_4);
	hfc1_4_back->setOppos(hfc2_3_back);
	hfc2_3_back->setOppos(hfc1_4_back);

	Mesh3DHalfCorner *opp_24 = hfc2_4->getOppos(), *opp_24_back = hfc2_4_back->getOppos();
	hfc2_4->setOppos(hfc1_3->getOppos());
	hfc1_3->getOppos()->setOppos(hfc2_4);
	hfc2_4_back->setOppos(hfc1_3_back->getOppos());
	hfc1_3_back->getOppos()->setOppos(hfc2_4_back);

	hfc1_3->setOppos(opp_24);
	opp_24->setOppos(hfc1_3);
	hfc1_3_back->setOppos(opp_24_back);
	opp_24_back->setOppos(hfc1_3_back);
	return true;
}
