#include "Sphere.h"

namespace FrictionFrenzy {
namespace CollisionObject {
void Sphere::initializeFCLObject() {
	Affine scaled;
	Isometry rigid;
	Scalar vol;
	std::vector<Vector3> transVertices;
	preprocessMesh(rigid, scaled, transVertices, vol);

	// Compute a sphere that best matches the inertia tensor.
	Matrix3 m = momentOfInertia(transVertices, *mp_mesh->indices_Eigen);
	Eigen::JacobiSVD svd(m);
	svd.compute(m, Eigen::ComputeFullU | Eigen::ComputeFullV);
	Vector3 svFac = 5.f / vol * svd.singularValues();
	Scalar sSums = svFac.sum() / 2;
	Vector3 sides = (sSums - svFac.array()).sqrt();
	m_radius = std::pow(sides.prod(), 0.33333333);
	mp_geo = std::make_unique<fcl::Sphere<Scalar>>(m_radius);

	// Force the rotation to have positive determinant.
	Matrix3 r = svd.matrixU();
	if (r.determinant() < 0) {
		r.row(2) *= -1;
	}

	// Initialize FCL object and transformations.
	rigid.linear() = rigid.linear() * r;
	Affine meshScaled = scaled;
	meshScaled.linear() = r.transpose() * meshScaled.linear();
	scaled.linear() = (m_radius * Vector3::Ones(3)).asDiagonal();
	scaled.translation().setZero();

	m_dist2 = 0.8 * M_PI * std::pow(m_radius, 5);

	initializeConfig(rigid, scaled, meshScaled);
}
Scalar Sphere::obbMinLength() const {
	auto* sphere = dynamic_cast<fcl::Sphere<Scalar>*>(mp_geo.get());
	return sphere->radius;
}
std::string Sphere::toString() const {
	std::stringstream ss;
	ss << "Type: sphere\n"
	   << "radius: " << m_radius << "\n"
	   << RigidObjectBase::toString();
	return ss.str();
}
}  // namespace CollisionObject
}  // namespace FrictionFrenzy
