/* Mesh3DHalfCorner.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, 2022
 *
 * This is the implementation file for the mesh half-corner class. Half-corner, because there are
 * two corners per triangle, one per label (i.e. one per adjacent material).
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "Mesh3DHalfCorner.h"

#include "Mesh3DTriangle.h"
#include "Mesh3DVertex.h"

//------------------------------------------------------------
// constructors
//------------------------------------------------------------

// default constructor
Mesh3DHalfCorner::Mesh3DHalfCorner()
    : vertex(nullptr),
      triangle(nullptr),
      next(nullptr),
      prev(nullptr),
      oppos(nullptr),
      label_side(false) {}

// parametrized constructor
Mesh3DHalfCorner::Mesh3DHalfCorner(Mesh3DVertex* v, Mesh3DTriangle* triangle_, bool label_side_)
    : vertex(v),
      triangle(triangle_),
      next(nullptr),
      prev(nullptr),
      oppos(nullptr),
      label_side(label_side_) {}

// default destructor
Mesh3DHalfCorner::~Mesh3DHalfCorner() {}

//------------------------------------------------------------
// functions
//------------------------------------------------------------

void Mesh3DHalfCorner::setHalfCorner(Mesh3DHalfCorner* half_corner) {
	setVertex(half_corner->getVertex());
	setTri(half_corner->getTri());
	setLabelSide(half_corner->getLabelSide());
	setNext(half_corner->getNext());
	setPrev(half_corner->getPrev());
	setOppos(half_corner->getOppos());
	setDual(half_corner->getDual());
}

// set the next, prev, dual poitners of a half-corner, that is, the pointers within the same
// triangle
void Mesh3DHalfCorner::setLocalConnectivity(Mesh3DHalfCorner* next_, Mesh3DHalfCorner* prev_,
                                            Mesh3DHalfCorner* dual_) {
	next = next_;
	prev = prev_;
	dual = dual_;
}

// set opposite pointers between this and parameter half corners, while observing labels; if the
// labels don't match, set the opposite pointers arbitrarily (non-mfld case)
void Mesh3DHalfCorner::linkOppos(Mesh3DHalfCorner* oppos_candidate) {
	// if this and oppos_candidate match labels, and their duals also match labels, link them
	if (triangle->getLabel(label_side) ==
	        oppos_candidate->getTri()->getLabel(oppos_candidate->getLabelSide()) ||
	    triangle->getLabel(!label_side) ==
	        oppos_candidate->getTri()->getLabel(!oppos_candidate->getLabelSide())) {
		oppos = oppos_candidate;
		oppos_candidate->setOppos(this);
		dual->setOppos(oppos_candidate->getDual());
		oppos_candidate->getDual()->setOppos(dual);
		return;
	}
	// if this and oppos_candidate match flipped labels, and their duals also match flipped labels,
	// link them in a flipped way
	if (triangle->getLabel(!label_side) ==
	        oppos_candidate->getTri()->getLabel(oppos_candidate->getLabelSide()) ||
	    triangle->getLabel(label_side) ==
	        oppos_candidate->getTri()->getLabel(!oppos_candidate->getLabelSide())) {
		oppos = oppos_candidate->getDual();
		oppos_candidate->setOppos(dual);
		dual->setOppos(oppos_candidate);
		oppos_candidate->getDual()->setOppos(this);
		return;
	}
	// if there is no label match, link this and oppos_candidate randomly
	oppos = oppos_candidate;
	oppos_candidate->setOppos(this);
	dual->setOppos(oppos_candidate->getDual());
	oppos_candidate->getDual()->setOppos(dual);
}

int Mesh3DHalfCorner::getLabel() const { return triangle->getLabel(label_side); }

bool operator==(const SortedMeshEdge& e1, const SortedMeshEdge& e2) {
	return (e1.getSmaller() == e2.getSmaller()) && (e1.getLarger() == e2.getLarger());
}

bool operator!=(const SortedMeshEdge& e1, const SortedMeshEdge& e2) { return !(e1 == e2); }