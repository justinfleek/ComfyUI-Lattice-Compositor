/* VertexProperties.cpp
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, Arian Etemadi 2023
 *
 * This is the implementation file for the vertex properties struct.
 */

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "VertexProperties.h"

//------------------------------------------------------------
// constructors
//------------------------------------------------------------

// default constructor
VertexProperties::VertexProperties() { setZero(); }

VertexProperties::VertexProperties(Vec3d vel, Vec3d flow_v, double th_v, double uth_v) {
	vector_props_[0] = vel;
	vector_props_[1] = flow_v;
	scalar_props_[0] = th_v;
	scalar_props_[1] = uth_v;
}

// copy constructor
VertexProperties::VertexProperties(const VertexProperties& vert_props)
    : vector_props_(vert_props.vector_props_), scalar_props_(vert_props.scalar_props_) {}

// default destructor
VertexProperties::~VertexProperties() {}

//------------------------------------------------------------
// functions
//------------------------------------------------------------

const VertexProperties VertexProperties::linearInterpolation(const VertexProperties& p1,
                                                             const VertexProperties& p2,
                                                             double alpha) {
	VertexProperties ret;
	for (int i = 0; i < ret.vector_props_.size(); i++) {
		ret.vector_props_[i] = (1 - alpha) * p1.vector_props_[i] + alpha * p2.vector_props_[i];
	}
	for (int i = 0; i < ret.scalar_props_.size(); i++) {
		ret.scalar_props_[i] = (1 - alpha) * p1.scalar_props_[i] + alpha * p2.scalar_props_[i];
	}
	return ret;
}

void VertexProperties::setZero() {
	for (Vec3d& prop : vector_props_) {
		prop = Vec3d(0);
	}
	for (double& prop : scalar_props_) {
		prop = 0.0;
	}
}

void VertexProperties::iadd(const VertexProperties& other) { iadd(other, 1); }

void VertexProperties::iadd(const VertexProperties& other, double scale) {
	for (int i = 0; i < vector_props_.size(); i++) {
		vector_props_[i] += other.vector_props_[i] * scale;
	}
	for (int i = 0; i < scalar_props_.size(); i++) {
		scalar_props_[i] += other.scalar_props_[i] * scale;
	}
}

void VertexProperties::idiv(double scale) {
	for (Vec3d& vp : vector_props_) {
		vp /= scale;
	}
	for (double& sp : scalar_props_) {
		sp /= scale;
	}
}

void VertexProperties::imul(double scale) {
	for (Vec3d& vp : vector_props_) {
		vp *= scale;
	}
	for (double& sp : scalar_props_) {
		sp *= scale;
	}
}

VertexProperties VertexProperties::div(double scale) const {
	VertexProperties ret(*this);
	ret.idiv(scale);
	return ret;
}
