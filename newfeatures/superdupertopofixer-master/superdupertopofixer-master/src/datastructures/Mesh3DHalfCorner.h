/* Mesh3DHalfCorner.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the header for the mesh half-corner class. Half-corner, because there are two corners per
 * triangle, one per label (i.e. one per adjacent material).
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include <algorithm>
#include <utility>

//------------------------------------------------------------
// declarations
//------------------------------------------------------------

class Mesh3DVertex;
class Mesh3DTriangle;
class Mesh3DCornerTable;

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// this class represents a mesh half-corner
class Mesh3DHalfCorner {
	friend Mesh3DCornerTable;

 public:
	Mesh3DHalfCorner();
	Mesh3DHalfCorner(Mesh3DVertex* v, Mesh3DTriangle* triangle_, bool label_side_);
	~Mesh3DHalfCorner();

	void setTri(Mesh3DTriangle* triangle_) { triangle = triangle_; }
	void setLabelSide(bool label_side_) { label_side = label_side_; }
	void setLocalConnectivity(Mesh3DHalfCorner* next_, Mesh3DHalfCorner* prev_,
	                          Mesh3DHalfCorner* dual_);
	void setNext(Mesh3DHalfCorner* next_) { next = next_; }
	void setPrev(Mesh3DHalfCorner* prev_) { prev = prev_; }
	void setOppos(Mesh3DHalfCorner* oppos_) { oppos = oppos_; }
	void linkOppos(Mesh3DHalfCorner* oppos_candidate);
	void setDual(Mesh3DHalfCorner* dual_) { dual = dual_; }

	Mesh3DVertex* getVertex() const { return vertex; }
	Mesh3DTriangle* getTri() const { return triangle; }
	bool getLabelSide() const { return label_side; }
	int getLabel() const;
	Mesh3DHalfCorner* getNext() { return next; }
	Mesh3DHalfCorner* getPrev() { return prev; }
	Mesh3DHalfCorner* getOppos() { return oppos; }
	Mesh3DHalfCorner* getDual() { return dual; }
	const Mesh3DHalfCorner* getNext() const { return next; }
	const Mesh3DHalfCorner* getPrev() const { return prev; }
	const Mesh3DHalfCorner* getOppos() const { return oppos; }
	const Mesh3DHalfCorner* getDual() const { return dual; }

	// drawing:
	void setHalfCorner(Mesh3DHalfCorner* half_corner);

 private:
	// Users should use function from the mesh interface to reassign the vertex.
	void setVertex(Mesh3DVertex* vertex_to_set) { vertex = vertex_to_set; }

	// data members
	Mesh3DVertex* vertex;
	Mesh3DTriangle* triangle;
	Mesh3DHalfCorner *next, *prev, *oppos, *dual;
	bool label_side;  // 0 if on the side of label[0] of triangle, 1 if on the side of label[1] of
	                  // triangle
};

class SortedMeshEdge {
 public:
	SortedMeshEdge(Mesh3DVertex* v1, Mesh3DVertex* v2)
	    : v1_(std::min(v1, v2)), v2_(std::max(v1, v2)) {}

	Mesh3DVertex* getSmaller() const { return v1_; }
	Mesh3DVertex* getLarger() const { return v2_; }
	template <typename H>
	friend H AbslHashValue(H h, const SortedMeshEdge& e) {
		return H::combine(std::move(h), e.v1_, e.v2_);
	}

 private:
	Mesh3DVertex* v1_;
	Mesh3DVertex* v2_;
};

bool operator==(const SortedMeshEdge& e1, const SortedMeshEdge& e2);
bool operator!=(const SortedMeshEdge& e1, const SortedMeshEdge& e2);
