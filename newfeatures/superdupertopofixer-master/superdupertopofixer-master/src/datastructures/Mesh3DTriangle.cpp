/* Mesh3DTriangle.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, 2021
 *
 * This is the implementation file for the mesh triangle class.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "Mesh3DTriangle.h"

#include "Mesh3DHalfCorner.h"
#include "Mesh3DVertex.h"

//------------------------------------------------------------
// constructors
//------------------------------------------------------------

// default constructor
Mesh3DTriangle::Mesh3DTriangle() : half_corner(nullptr) {}

//
Mesh3DTriangle::Mesh3DTriangle(Vec2i labels_) : half_corner(nullptr), labels(labels_){};

// default destructor
Mesh3DTriangle::~Mesh3DTriangle() {}

//------------------------------------------------------------
// functions
//------------------------------------------------------------

//------------------------------------------------------------
// labels
//------------------------------------------------------------

void Mesh3DTriangle::getLabels(int& lr, int& ll) const {
	lr = labels[0];
	ll = labels[1];
}

void Mesh3DTriangle::setLabels(int lr, int ll) {
	labels[0] = lr;
	labels[1] = ll;
}

void Mesh3DTriangle::setLabels(std::pair<int, int> label_pair) {
	labels[0] = label_pair.first;
	labels[1] = label_pair.second;
}

void Mesh3DTriangle::setLabels(Vec2i labels_) { labels = labels_; }

//------------------------------------------------------------
// vertices
//------------------------------------------------------------

Mesh3DVertex* Mesh3DTriangle::getVertex(int index) const {
	// ASSERT: index must be among 0,1,2
	assert(index == 0 || index == 1 || index == 2);

	if (index == 0) {
		return half_corner->getVertex();
	} else if (index == 1) {
		return half_corner->getNext()->getVertex();
	} else if (index == 2) {
		return half_corner->getPrev()->getVertex();
	}

	return nullptr;
}

std::vector<Mesh3DVertex*> Mesh3DTriangle::getVerts() const {
	return std::vector<Mesh3DVertex*>({half_corner->getVertex(), half_corner->getNext()->getVertex(),
	                                   half_corner->getPrev()->getVertex()});
}

void Mesh3DTriangle::getVerts(Mesh3DVertex** v0, Mesh3DVertex** v1, Mesh3DVertex** v2) const {
	*v0 = half_corner->getVertex();
	*v1 = half_corner->getNext()->getVertex();
	*v2 = half_corner->getPrev()->getVertex();
}

std::vector<Mesh3DVertex*> Mesh3DTriangle::getPointerAscendVertsVector() const {
	Mesh3DVertex* w0 = half_corner->getVertex();
	Mesh3DVertex* w1 = half_corner->getNext()->getVertex();
	Mesh3DVertex* w2 = half_corner->getPrev()->getVertex();
	Mesh3DVertex *v0, *v1, *v2;

	// order `w0`,`w1`,`w2` based on their pointer values
	if (w0 < w1) {
		if (w0 < w2) {
			v0 = w0;
			if (w1 < w2) {
				v1 = w1;
				v2 = w2;
			} else {
				v1 = w2;
				v2 = w1;
			}
		} else {
			v0 = w2;
			v1 = w0;
			v2 = w1;
		}
	} else {
		if (w0 < w2) {
			v0 = w1;
			v1 = w0;
			v2 = w2;
		} else {
			v2 = w0;
			if (w1 < w2) {
				v0 = w1;
				v1 = w2;
			} else {
				v0 = w2;
				v1 = w1;
			}
		}
	}

	return std::vector<Mesh3DVertex*>{v0, v1, v2};
}

//------------------------------------------------------------
// half-corners
//------------------------------------------------------------

std::vector<Mesh3DHalfCorner*> Mesh3DTriangle::getHalfCorners() const {
	return {half_corner,
	        half_corner->getNext(),
	        half_corner->getPrev(),
	        half_corner->getDual(),
	        half_corner->getDual()->getNext(),
	        half_corner->getDual()->getPrev()};
}

Mesh3DHalfCorner* Mesh3DTriangle::getHalfCornerAtVertex(Mesh3DVertex* vertex) const {
	if (half_corner->getVertex() == vertex) {
		return half_corner;
	}
	if (half_corner->getNext()->getVertex() == vertex) {
		return half_corner->getNext();
	}
	if (half_corner->getPrev()->getVertex() == vertex) {
		return half_corner->getPrev();
	}
	return nullptr;
}

void Mesh3DTriangle::setHalfCorner(Mesh3DHalfCorner* half_corner_) { half_corner = half_corner_; }

//------------------------------------------------------------
// other functions
//------------------------------------------------------------

bool Mesh3DTriangle::isEdgeOrientedSameAsTriangle(Mesh3DVertex* edge_v0, Mesh3DVertex* edge_v1,
                                                  Mesh3DHalfCorner** opposing_hfc) const {
	// ASSERT: this function is only defined if `edge_v0` and `edge_v1` are two distinct vertices of
	// this triangle
	assert((half_corner->getVertex() == edge_v0 || half_corner->getNext()->getVertex() == edge_v0 ||
	        half_corner->getPrev()->getVertex() == edge_v0));
	assert((half_corner->getVertex() == edge_v1 || half_corner->getNext()->getVertex() == edge_v1 ||
	        half_corner->getPrev()->getVertex() == edge_v1));
	assert(edge_v0 != edge_v1);

	if (half_corner->getVertex() == edge_v0) {
		if (half_corner->getNext()->getVertex() == edge_v1) {
			*opposing_hfc = half_corner->getPrev();
			return true;
		} else {
			*opposing_hfc = half_corner->getNext()->getDual();
			return false;
		}
	}
	if (half_corner->getVertex() == edge_v1) {
		if (half_corner->getPrev()->getVertex() == edge_v0) {
			*opposing_hfc = half_corner->getNext();
			return true;
		} else {
			*opposing_hfc = half_corner->getPrev()->getDual();
			return false;
		}
	}
	if (half_corner->getNext()->getVertex() == edge_v0) {
		*opposing_hfc = half_corner;
		return true;
	} else {
		*opposing_hfc = half_corner->getDual();
		return false;
	}
}