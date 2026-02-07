/* Mesh3DCornerTableManipulation.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru
 *
 * This is the implementation file for the mesh corner table, containing implementations of
 * functions related to retrieving information about the mesh.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <limits>

#include "Mesh3DCornerTable.h"
#include "Mesh3DHalfCorner.h"
#include "Mesh3DTriangle.h"
#include "Mesh3DVertex.h"
#include "absl/container/flat_hash_map.h"
#include "absl/container/flat_hash_set.h"

//------------------------------------------------------------
// functions
//------------------------------------------------------------

// returns number of mesh triangles
int Mesh3DCornerTable::getNumberTris() const { return mesh_triangles_list.size(); }

// returns number of mesh vertices
int Mesh3DCornerTable::getNumberVerts() const { return mesh_vertices_list.size(); }

// adds to input vector one HC per extending vertex of mesh edge opposite input HC
void Mesh3DCornerTable::walkAroundEdge(Mesh3DHalfCorner* start_halfcorner,
                                       std::vector<Mesh3DHalfCorner*>& output_corners,
                                       bool include_start_halfcorner) {
	if (include_start_halfcorner) {
		output_corners.push_back(start_halfcorner);
	}
	Mesh3DHalfCorner* current_halfcorner = start_halfcorner->getOppos()->getDual();
	while (current_halfcorner != start_halfcorner) {
		output_corners.push_back(current_halfcorner);
		current_halfcorner = current_halfcorner->getOppos()->getDual();
	};
}

// finds and stores into the input vectors the smallest and largest x,y,z-coordinates from among all
// the vertices in the mesh
void Mesh3DCornerTable::getMeshBounds(Vec3d& mesh_min, Vec3d& mesh_max) {
	mesh_min = (*mesh_vertices_list.begin())->getCoords();
	mesh_max = mesh_min;
	for (Mesh3DVertex* vertex : mesh_vertices_list) {
		if (mesh_min[0] > vertex->getCoord(0)) {
			mesh_min[0] = vertex->getCoord(0);
		}
		if (mesh_min[1] > vertex->getCoord(1)) {
			mesh_min[1] = vertex->getCoord(1);
		}
		if (mesh_min[2] > vertex->getCoord(2)) {
			mesh_min[2] = vertex->getCoord(2);
		}
		if (mesh_max[0] < vertex->getCoord(0)) {
			mesh_max[0] = vertex->getCoord(0);
		}
		if (mesh_max[1] < vertex->getCoord(1)) {
			mesh_max[1] = vertex->getCoord(1);
		}
		if (mesh_max[2] < vertex->getCoord(2)) {
			mesh_max[2] = vertex->getCoord(2);
		}
	}
}

bool Mesh3DCornerTable::isEdgeNonmanifold(Mesh3DHalfCorner* opp_edge_corner) const {
	return opp_edge_corner->getOppos()->getDual()->getOppos() != opp_edge_corner->getDual();
}

double Mesh3DCornerTable::getAngle(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3) const {
	Vec3d v1_coords = v1->getCoords();
	Vec3d v2_coords = v2->getCoords();
	Vec3d v3_coords = v3->getCoords();

	Vec3d side1 = v1_coords - v2_coords;
	Vec3d side2 = v3_coords - v2_coords;
	double len1 = mag(side1);
	if (len1 == 0) {
		return -1;
	}
	double len2 = mag(side2);
	if (len2 == 0) {
		return -1;
	}
	double cos = dot(side1, side2) / (len1 * len2);
	if (cos >= 1.0) {
		return 0;
	}
	if (cos <= -1.0) {
		return M_PI;
	}
	return acos(cos);
};

double Mesh3DCornerTable::getAngle(Mesh3DHalfCorner* hfc) const {
	return getAngle(hfc->getNext()->getVertex(), hfc->getVertex(), hfc->getPrev()->getVertex());
}

double Mesh3DCornerTable::getAngleCos(Mesh3DVertex* v1, Mesh3DVertex* v2, Mesh3DVertex* v3) const {
	Vec3d v1_coords = v1->getCoords();
	Vec3d v2_coords = v2->getCoords();
	Vec3d v3_coords = v3->getCoords();

	Vec3d side1 = v1_coords - v2_coords;
	Vec3d side2 = v3_coords - v2_coords;
	double len1 = mag(side1);
	if (len1 == 0) {
		return -2;
	}
	double len2 = mag(side2);
	if (len2 == 0) {
		return -2;
	}
	return dot(side1, side2) / (len1 * len2);
};

double Mesh3DCornerTable::getAngleCos(Mesh3DHalfCorner* hfc) const {
	return getAngleCos(hfc->getNext()->getVertex(), hfc->getVertex(), hfc->getPrev()->getVertex());
}

Mesh3DTriangle* Mesh3DCornerTable::getCommonTriangle(Mesh3DVertex* v1, Mesh3DVertex* v2) const {
	const auto& hfcs = vertex_to_hfc_map.at(v1);
	std::vector<Mesh3DTriangle*> v1_tris;
	v1_tris.reserve(hfcs.size());
	for (Mesh3DHalfCorner* hfc : hfcs) {
		v1_tris.push_back(hfc->getTri());
	}

	for (Mesh3DHalfCorner* hfc : vertex_to_hfc_map.at(v2)) {
		for (Mesh3DTriangle* tri : v1_tris) {
			if (tri == hfc->getTri()) {
				return tri;
			}
		}
	}
	return nullptr;
}

double Mesh3DCornerTable::getAverageEdgeLength() const {
	double averagelen = 0.0;
	for (Mesh3DTriangle* tri : mesh_triangles_list) {
		std::vector<Mesh3DVertex*> triverts = tri->getVerts();
		for (int i = 0; i < 3; ++i) {
			Vec3d v0 = triverts.at(i % 3)->getCoords();
			Vec3d v1 = triverts.at((i + 1) % 3)->getCoords();
			averagelen += mag(v1 - v0);
		}
	}
	return averagelen / (3.0 * getNumberTris());
}

double Mesh3DCornerTable::getMinEdgeLength() const {
	double min_length = std::numeric_limits<double>::max();
	for (Mesh3DTriangle* tri : mesh_triangles_list) {
		std::vector<Mesh3DVertex*> triverts = tri->getVerts();
		for (int i = 0; i < 3; ++i) {
			Vec3d v0 = triverts.at(i % 3)->getCoords();
			Vec3d v1 = triverts.at((i + 1) % 3)->getCoords();
			min_length = std::min(mag(v1 - v0), min_length);
		}
	}
	return min_length;
}

double Mesh3DCornerTable::getMaxEdgeLength() const {
	double max_length = std::numeric_limits<double>::min();
	for (Mesh3DTriangle* tri : mesh_triangles_list) {
		std::vector<Mesh3DVertex*> triverts = tri->getVerts();
		for (int i = 0; i < 3; ++i) {
			Vec3d v0 = triverts.at(i % 3)->getCoords();
			Vec3d v1 = triverts.at((i + 1) % 3)->getCoords();
			max_length = std::max(mag(v1 - v0), max_length);
		}
	}
	return max_length;
}

// return a map that to a mesh vertex associates a set of adjacent mesh triangles
absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DTriangle*>>
Mesh3DCornerTable::buildVertexTriangleAdjacency() const {
	absl::flat_hash_map<Mesh3DVertex*, absl::flat_hash_set<Mesh3DTriangle*>> adjacent_triangles;
	adjacent_triangles.reserve(mesh_vertices_list.size());
	for (Mesh3DTriangle* tri : mesh_triangles_list) {
		for (Mesh3DVertex* vert : tri->getVerts()) {
			adjacent_triangles[vert].insert(tri);
		}
	}
	return adjacent_triangles;
}

// return the number of triangles adjacent to the mesh edge opposite of input `opp_edge_corner`
int Mesh3DCornerTable::edgeValence(Mesh3DHalfCorner* opp_edge_corner) {
	int valence = 0;
	Mesh3DHalfCorner* current_halfcorner = opp_edge_corner;
	do {
		current_halfcorner = current_halfcorner->getOppos()->getDual();
		valence++;
	} while (current_halfcorner != opp_edge_corner);

	return valence;
}

absl::flat_hash_set<Mesh3DHalfCorner*> Mesh3DCornerTable::getEdgesAroundVertex(
    const Mesh3DVertex* center_vertex) const {
	absl::flat_hash_set<Mesh3DHalfCorner*> result;
	for (Mesh3DHalfCorner* hfc : vertex_to_hfc_map.at(center_vertex)) {
		result.insert(hfc->getNext());
		result.insert(hfc->getPrev());
	}
	return result;
}

absl::flat_hash_set<Mesh3DTriangle*> Mesh3DCornerTable::getTrianglesAroundVertex(
    Mesh3DVertex* vertex) const {
	absl::flat_hash_set<Mesh3DTriangle*> tris_around_vertex;
	for (Mesh3DHalfCorner* hfc : vertex_to_hfc_map.at(vertex)) {
		tris_around_vertex.insert(hfc->getTri());
	}
	return tris_around_vertex;
};

std::vector<Mesh3DTriangle*> Mesh3DCornerTable::getTriangleVectorAroundVertex(
    Mesh3DVertex* vertex) const {
	const auto& hfcs = vertex_to_hfc_map.at(vertex);
	std::vector<Mesh3DTriangle*> tris_around_vertex;
	tris_around_vertex.reserve(hfcs.size() / 2);
	for (Mesh3DHalfCorner* hfc : hfcs) {
		Mesh3DTriangle* tri = hfc->getTri();
		bool inside = false;
		for (Mesh3DTriangle* inside_tri : tris_around_vertex) {
			if (inside_tri == tri) {
				inside = true;
				break;
			}
		}
		if (!inside) {
			tris_around_vertex.push_back(hfc->getTri());
		}
	}
	return tris_around_vertex;
};

std::vector<Mesh3DHalfCorner*> Mesh3DCornerTable::getHalfCornersAroundEdge(Mesh3DVertex* v1,
                                                                           Mesh3DVertex* v2) const {
	std::vector<Mesh3DHalfCorner*> hfcs;
	for (Mesh3DTriangle* tri : getTrianglesAroundEdge(v1, v2)) {
		Mesh3DHalfCorner* hfc = tri->getHalfCorner();
		while (hfc->getVertex() == v1 || hfc->getVertex() == v2) {
			hfc = hfc->getNext();
		}
		hfcs.push_back(hfc);
	}
	return hfcs;
}

std::vector<Mesh3DTriangle*> Mesh3DCornerTable::getTrianglesAroundEdge(Mesh3DVertex* v1,
                                                                       Mesh3DVertex* v2) const {
	std::vector<Mesh3DTriangle*> tris;
	const auto v2_tris = getTriangleVectorAroundVertex(v2);
	for (Mesh3DTriangle* tri : getTriangleVectorAroundVertex(v1)) {
		for (Mesh3DTriangle* tri2 : v2_tris) {
			if (tri == tri2) {
				tris.push_back(tri);
			}
		}
	}
	return tris;
}

const absl::flat_hash_set<Mesh3DHalfCorner*>& Mesh3DCornerTable::getHalfCornersAtVertex(
    Mesh3DVertex* vertex) const {
	return vertex_to_hfc_map.at(vertex);
}

void Mesh3DCornerTable::printTriangleVertexIndices(Mesh3DTriangle* triangle) const {
	std::cout << getVertexIndex(triangle->getVertex(0)) << " "
	          << getVertexIndex(triangle->getVertex(1)) << " "
	          << getVertexIndex(triangle->getVertex(2)) << '\n';
}

bool Mesh3DCornerTable::isVertexInMesh(Mesh3DVertex* v) const {
	return mesh_vertices_list.contains(v);
}

bool Mesh3DCornerTable::isHalfCornerInMesh(Mesh3DHalfCorner* h) const {
	return mesh_half_corners_list.contains(h);
}

bool Mesh3DCornerTable::isTriangleInMesh(const Mesh3DTriangle* t) const {
	return mesh_triangles_list.contains(t);
}

double Mesh3DCornerTable::getTotalArea() const {
	double area = 0.0;
	for (Mesh3DTriangle* tri : mesh_triangles_list) {
		area += tri->getArea();
	}
	return area;
}

// TODO: include variables other than velocity in this calculation
double Mesh3DCornerTable::getTotalKineticEnergy() const {
	const absl::flat_hash_map<Mesh3DVertex*, double> areas = getVertexAreas();
	double energy = 0.0;
	for (Mesh3DVertex* vert : mesh_vertices_list) {
		energy += areas.at(vert) * mag2(vert->getVelocity());
	}
	return energy;
}

absl::flat_hash_map<Mesh3DVertex*, double> Mesh3DCornerTable::getVertexAreas() const {
	absl::flat_hash_map<Mesh3DVertex*, double> areas;
	for (Mesh3DTriangle* tri : mesh_triangles_list) {
		// Split triangle areas between vertices.
		double area = tri->getArea() / 3.0;
		for (Mesh3DVertex* vert : tri->getVerts()) {
			areas[vert] += area;
		}
	}
	return areas;
}

bool Mesh3DCornerTable::areEdgesAroundManifold(const Mesh3DVertex* v) const {
	absl::flat_hash_set<Mesh3DHalfCorner*> edges = getEdgesAroundVertex(v);
	for (Mesh3DHalfCorner* edge : getEdgesAroundVertex(v)) {
		if (isEdgeNonmanifold(edge)) {
			return false;
		}
	}
	return true;
}