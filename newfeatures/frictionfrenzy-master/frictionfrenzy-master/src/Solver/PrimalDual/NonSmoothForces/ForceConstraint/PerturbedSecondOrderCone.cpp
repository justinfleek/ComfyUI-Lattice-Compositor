#include "PerturbedSecondOrderCone.h"

namespace FrictionFrenzy {
namespace Solver {
Scalar PerturbedSecondOrderCone::constraint(
	const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Scalar r = in[1] * in[1] + in[2] * in[2] + m_perturbation;
	Scalar f = *mp_frictionCoeff;
	Scalar c = std::sqrt(r) - f * in[0] - std::sqrt(m_perturbation);
	return c;
}
VectorX PerturbedSecondOrderCone::gradient(
	const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Scalar r2 = in[1] * in[1] + in[2] * in[2] + m_perturbation;
	Scalar r = std::sqrt(r2);
	Scalar f = *mp_frictionCoeff;
	Vector3 ret;
	ret << -f, in[1] / r, in[2] / r;
	return ret;
}
MatrixX PerturbedSecondOrderCone::hessian(
	const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Scalar p = std::max(m_perturbation, 1e-6);
	Scalar r2 = in[1] * in[1] + in[2] * in[2] + p;
	Matrix3 ret = Matrix3::Zero();
	Scalar r3 = std::pow(r2, -1.5);
	Vector2 zmy;
	zmy << in[2], -in[1];
	ret.block<2, 2>(1, 1) << zmy * zmy.transpose() + p * Matrix2::Identity();
	ret *= r3;
	return ret;
}
VectorX PerturbedSecondOrderCone::project(const Eigen::Ref<const VectorX> in,
                                          const Eigen::Ref<const VectorX> start,
                                          Scalar target) const {
	Scalar f = *mp_frictionCoeff;
	Scalar sineMu = std::sqrt(1 / f / f + 1);
	Scalar coneTip = target * sineMu;
	Scalar bLen = std::sqrt(in[1] * in[1] + in[2] * in[2]);
	Scalar centerPoint = in[0] + bLen * f;
	if (centerPoint < coneTip) {
		return Vector3(coneTip, 0, 0);
	}
	Scalar sLen = bLen - in[0] * f;
	Scalar dToCone = sLen / std::sqrt(1 + f * f);
	Vector3 dir;
	dir << bLen * f, -in[1], -in[2];
	dir = dir.normalized();
	VectorX out = in + dir * (dToCone - target / std::sqrt(1 + f * f));

	return out;
}
Scalar PerturbedSecondOrderCone::radiusAt(Scalar i0) const {
	Scalar f = *mp_frictionCoeff;
	Scalar k = f * i0 + std::sqrt(m_perturbation);
	Scalar r = std::sqrt(k * k - m_perturbation);
	return r;
}
}  // namespace Solver
}  // namespace FrictionFrenzy
