/* GridMeshIntersection.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, 2021
 *
 * This is the implementation of structures representing intersection between mesh and grid.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "GridMeshIntersection.h"

#include <algorithm>

#include "../utilities/vec.h"
#include "Grid3DInterface.h"

//------------------------------------------------------------
// constructors
//------------------------------------------------------------

GridEdgeMeshFaceIntersection::GridEdgeMeshFaceIntersection(Mesh3DTriangle* triangle,
                                                           const long long edge_id, const Vec3d pos,
                                                           const Vec3d bary,
                                                           const bool is_tri_norm_edge_aligned)
    : triangle_(triangle),
      vertex_(nullptr),
      edge_id_(edge_id),
      pos_(pos),
      bary_(bary),
      is_normal_aligned_(is_tri_norm_edge_aligned){};

void GridEdgeMeshFaceIntersection::setVertex(Mesh3DVertex* vertex) {
	vertex_ = vertex;
	if (vertex_ != nullptr) {
		vertex_->setCoords(pos_);
	}
}

void GridEdgeMeshFaceIntersection::setBary(Vec3d bary) { bary_ = bary; }

GridFaceMeshEdgeIntersection::GridFaceMeshEdgeIntersection(
    const long long face_id, Mesh3DVertex* first, const bool is_first_inside, Mesh3DVertex* second,
    const bool is_second_inside, const double bary_coord, Mesh3DVertex* vertex)
    : face_id_(face_id),
      first_(first),
      second_(second),
      bary_coord_(bary_coord),
      is_first_inside_(is_first_inside),
      is_second_inside_(is_second_inside),
      vertex_(vertex) {
	if (vertex_ != nullptr) {
		vertex_->setCoords((1 - bary_coord_) * first_->getCoords() +
		                   bary_coord_ * second_->getCoords());
	}
};

GridFaceMeshEdgeIntersection::GridFaceMeshEdgeIntersection(GridFaceMeshEdgeIntersection&& other) {
	*this = std::move(other);
}

Vec3d GridFaceMeshEdgeIntersection::getPosition() const {
	if (vertex_ != nullptr) {
		return vertex_->getCoords();
	}
	return (1 - bary_coord_) * first_->getCoords() + bary_coord_ * second_->getCoords();
}

void GridFaceMeshEdgeIntersection::setVertex(Mesh3DVertex* vertex) {
	vertex_ = vertex;
	if (vertex_ != nullptr) {
		vertex_->setCoords((1 - bary_coord_) * first_->getCoords() +
		                   bary_coord_ * second_->getCoords());
	}
}

void GridFaceMeshEdgeIntersection::setBaryCoord(double bary) {
	bary_coord_ = bary;
	if (vertex_ != nullptr) {
		vertex_->setCoords((1 - bary_coord_) * first_->getCoords() +
		                   bary_coord_ * second_->getCoords());
	}
}

//------------------------------------------------------------
// operators
//------------------------------------------------------------

GridFaceMeshEdgeIntersection& GridFaceMeshEdgeIntersection::operator=(
    GridFaceMeshEdgeIntersection&& other) {
	if (this != &other) {
		face_id_ = other.face_id_;
		first_ = other.first_;
		second_ = other.second_;
		bary_coord_ = other.bary_coord_;
		is_first_inside_ = other.is_first_inside_;
		is_second_inside_ = other.is_second_inside_;
		vertex_ = other.vertex_;

		other.face_id_ = 0;
		other.first_ = nullptr;
		other.second_ = nullptr;
		other.bary_coord_ = 0.0;
		other.is_first_inside_ = false;
		other.is_second_inside_ = false;
		other.vertex_ = nullptr;
	}
	return *this;
}

GridFaceMeshEdgeCmp::GridFaceMeshEdgeCmp(Grid3DInterface& grid, Mesh3DVertex* first,
                                         Mesh3DVertex* second)
    : grid_(grid) {
	const Vec3d first_coords = first->getCoords();
	const Vec3d second_coords = second->getCoords();
	for (int i = 0; i < 3; ++i) {
		if (first_coords[i] < second_coords[i]) {
			direction_[i] = 1;
		} else if (first_coords[i] == second_coords[i]) {
			direction_[i] = 0;
		} else {
			direction_[i] = -1;
		}
	}
}

bool GridFaceMeshEdgeCmp::operator()(const GridFaceMeshEdgeIntersection& first,
                                     const GridFaceMeshEdgeIntersection& second) {
	Vec4ll first_coords;
	Vec4ll second_coords;
	grid_.get_edge_coords(first.getFaceId(), first_coords[0], first_coords[1], first_coords[2],
	                      first_coords[3]);
	grid_.get_edge_coords(second.getFaceId(), second_coords[0], second_coords[1], second_coords[2],
	                      second_coords[3]);
	for (int dir = 0; dir < 3; ++dir) {
		// If no change in coordinate is happening, no test can be performed.
		if (direction_[dir] == 0) {
			continue;
		}
		// Find if faces are comparable along the positive direction `dir.
		int result = cmpGridFaces(first_coords, second_coords, dir);
		if (result != 0) {
			// Faces are comparable. Return if first face comes earlier based on the orientation of mesh
			// edge.
			return direction_[dir] == result;
		}
	}
	// If faces are incomparable, don't change the order.
	return true;
}

int GridFaceMeshEdgeCmp::cmpGridFaces(Vec4ll first, Vec4ll second, int orientation) {
	if (first[orientation] < second[orientation]) {
		return 1;
	}
	if (first[orientation] > second[orientation]) {
		return -1;
	}
	bool first_same_orient = first[3] == orientation;
	bool second_same_orient = second[3] == orientation;
	if (first_same_orient && !second_same_orient) {
		return 1;
	}
	if (second_same_orient && !first_same_orient) {
		return -1;
	}
	return 0;
}

//------------------------------------------------------------
// functions
//------------------------------------------------------------