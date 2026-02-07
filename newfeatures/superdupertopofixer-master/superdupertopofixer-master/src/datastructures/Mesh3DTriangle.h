/* Mesh3DTriangle.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2021
 *
 * This is the header for the mesh triangle class.
 */

#pragma once

//------------------------------------------------------------
// includes
#include <assert.h>

#include <cstring>
#include <vector>
//------------------------------------------------------------
#include <cstddef>

#include "../utilities/vec.h"
#include "Mesh3DVertex.h"

//------------------------------------------------------------
// declarations
//------------------------------------------------------------

class Mesh3DVertex;
class Mesh3DHalfCorner;

//---------------------------------------------------------
// classes
//------------------------------------------------------------

// this class represents a mesh triangle
class Mesh3DTriangle {
 public:
	Mesh3DTriangle();
	Mesh3DTriangle(Vec2i labels_);
	~Mesh3DTriangle();

	// ----------------- labels

	// get the material labels on the triangle
	void getLabels(int& lr, int& ll) const;
	Vec2i getLabels() const { return labels; };
	int getLabel(bool side) const { return labels[side]; }

	// set two material labels of the triangle; the first label is considered to correspond to the
	// triangle side determined by triangle orientation obtained by taking the vertex at `half_corner`
	// and following along `next` pointers, and by the right hand rule
	void setLabels(int lr, int ll);
	void setLabels(std::pair<int, int> label_pair);
	void setLabels(Vec2i labels_);

	// ----------------- vertices

	// get vertices of the triangle; the order of retrieved vertices is given by taking the vertex at
	// `half_corner` and following the `next` pointers; this is the same order that is implicitely
	// assumed to define the orientation of the triangle for the purposes of assigning labels to
	// triangle sides
	Mesh3DVertex* getVertex(int index) const;
	std::vector<Mesh3DVertex*> getVerts() const;
	void getVerts(Mesh3DVertex** v0, Mesh3DVertex** v1, Mesh3DVertex** v2) const;
	// get the vector of vertices of the triangle in increasing order of their pointer values
	std::vector<Mesh3DVertex*> getPointerAscendVertsVector() const;

	// ----------------- half corners

	// get the reference half-corner associated with the triangle
	Mesh3DHalfCorner* getHalfCorner() const { return half_corner; }
	// get a half-corner of this triangle at the input `vertex` (half-corner on label side 0 is
	// returned); if `vertex` is not one of the three vertices of this triangle, return nullptr
	Mesh3DHalfCorner* getHalfCornerAtVertex(Mesh3DVertex* vertex) const;
	// get all half-corners associated with the triangle, first three on label side 0, last three on
	// label side 1
	std::vector<Mesh3DHalfCorner*> getHalfCorners() const;

	// set the pointer to the reference half-corner of the triangle
	// WARNING: can flip the implicit assignment of material labels to triangle sides. This assignment
	// depends on two pieces of information: the orientation of the triangle and the right hand rule.
	// The orientation of the triangle is determined by taking the triangle's vertices as they are
	// visited when we follow `half_corner`'s `next` pointers. At the same time, mutually dual
	// half-corners' `next` pointers define opposite triangle orientations. Together, this means that
	// setting `half-corner` of a triangle to one of the 3 HCs on one side vs to one of the 3 dual HCs
	// on the other side will result in a different assignment of labels to triangle sides.
	void setHalfCorner(Mesh3DHalfCorner* half_corner_);

	// ----------------- other functions

	// Checks whether the edge (`edge_v0`,`edge_v1`) is oriented the same way as this triangle (as
	// determined by retrieveing the vertex at `half_corner` and following `next` pointers). Return
	// value is undefined if `edge_v0` and `edge_v1` are not two distinct vertices of this triangle.
	// Additionally, saves into `opposing_hfc` the address of the pointer to the half-corner opposite
	// of the input edge, which is associated with the triangle orientation compatible with the input
	// edge orientation (i.e. we take the primal HC if the function would return true, and dual HC if
	// it would return false). This is another way of saying that assuming the right hand rule, we
	// return the HC that lies on the side of the triangle that has orientation compatible with the
	// input edge.
	bool isEdgeOrientedSameAsTriangle(Mesh3DVertex* edge_v0, Mesh3DVertex* edge_v1,
	                                  Mesh3DHalfCorner** opposing_hfc) const;

	inline Vec3d getNaiveNormal() const;
	inline double getArea() const { return mag(getNaiveNormal()) * 0.5; }

 private:
	// ----------------- data members

	// triangle reference half-corner, can be used to reconstruct triangle's mesh neighborhood
	Mesh3DHalfCorner* half_corner;

	// two material labels of the triangle
	Vec2i labels;  // label[0] is the material that rhs rule normal is pointing to
	               // label[1] is the material that lhs rule normal is pointing to
};

inline Vec3d Mesh3DTriangle::getNaiveNormal() const {
	const std::vector<Mesh3DVertex*> v = getVerts();
	return cross(v[1]->getCoords() - v[0]->getCoords(), v[2]->getCoords() - v[0]->getCoords());
}
