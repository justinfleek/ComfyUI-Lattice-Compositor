/* VertexProperties.h
 *
 * Peter Synak, Chris Wojtan, Huidong Yang, Aleksei Kalinov, Malina Strugaru, Arian Etemadi 2023
 *
 * This is the header for the vertex properties struct.
 */

#pragma once

//------------------------------------------------------------
// includes
//------------------------------------------------------------

#include "../utilities/vec.h"

//------------------------------------------------------------
// classes
//------------------------------------------------------------

// struct of properties that are stored per vertex of the mesh,
// including velocity, thickness, derivative of thickness, and surface flow,
// two of which are double values and two Vec3d values.

struct VertexProperties {
 public:
	// constructors
	VertexProperties();
	VertexProperties(Vec3d vel, Vec3d flow_v, double th_v, double uth_v);
	VertexProperties(const VertexProperties& vert_props);
	~VertexProperties();

	// returns a VertexProperties struct with linearly interpolated values
	const static VertexProperties linearInterpolation(const VertexProperties& p1,
	                                                  const VertexProperties& p2, double alpha);

	// getters and setters
	Vec3d getVelocity() const { return vector_props_[0]; }
	Vec3d getFlowV() const { return vector_props_[1]; }
	double getThickness() const { return scalar_props_[0]; }
	double getUThickness() const { return scalar_props_[1]; }
	void setVelocity(Vec3d vel) { vector_props_[0] = vel; }
	void setFlowV(Vec3d flow_v) { vector_props_[1] = flow_v; }
	void setThickness(double th_v) { scalar_props_[0] = th_v; }
	void setUThickness(double uth_v) { scalar_props_[1] = uth_v; }

	// functions
	void setZero();
	void iadd(const VertexProperties& other);
	void iadd(const VertexProperties& other, double scale);
	void idiv(double scale);
	void imul(double scale);
	VertexProperties div(double scale) const;

	// override operator>>, for reading lines with keyword v_props from .obj files
	friend std::istream& operator>>(std::istream& is, VertexProperties& vert_props) {
		for (Vec3d& prop : vert_props.vector_props_) {
			is >> prop;
		}
		for (double& prop : vert_props.scalar_props_) {
			is >> prop;
		}
		return is;
	}

	// override operator<<, for writing lines with keyword v_props in .obj files and debug prints
	friend std::ostream& operator<<(std::ostream& os, const VertexProperties& vert_props) {
		for (const Vec3d& prop : vert_props.vector_props_) {
			os << prop << ' ';
		}
		for (const double prop : vert_props.scalar_props_) {
			os << prop << ' ';
		}
		return os;
	}

 private:
	std::array<Vec3d, 2> vector_props_;
	std::array<double, 2> scalar_props_;
};
