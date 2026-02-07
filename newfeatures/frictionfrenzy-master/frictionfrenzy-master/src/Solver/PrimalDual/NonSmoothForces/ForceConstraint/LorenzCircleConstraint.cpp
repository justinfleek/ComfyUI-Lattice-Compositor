#include "LorenzCircleConstraint.h"

namespace FrictionFrenzy {
namespace Solver {
Scalar LorenzCircleConstraint::constraint(
	const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Scalar r = in[1] * in[1] + in[2] * in[2] + m_perturbation;
	Scalar f = *mp_frictionCoeff;
	Scalar c =
		std::sqrt(r) - f * in[0] - std::sqrt(m_perturbation) - m_shift;
	return c;
}
VectorX LorenzCircleConstraint::gradient(
	const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Scalar r2 = in[1] * in[1] + in[2] * in[2] + m_perturbation;
	Scalar r = std::sqrt(r2);
	Vector2 ret;
	ret << in[1] / r, in[2] / r;
	return ret;
}
MatrixX LorenzCircleConstraint::hessian(
	const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Scalar p = std::max(m_perturbation, 1e-6);
	Scalar r2 = in[1] * in[1] + in[2] * in[2] + p;
	Matrix2 ret = Matrix2::Zero();
	Scalar r3 = std::pow(r2, -1.5);
	Vector2 zmy;
	zmy << in[2], -in[1];
	ret << zmy * zmy.transpose() + p * Matrix2::Identity();
	ret *= r3;
	return ret;
}
VectorX LorenzCircleConstraint::project(const Eigen::Ref<const VectorX> in,
                                        const Eigen::Ref<const VectorX> start,
                                        Scalar target) const {
	Vector3 out = in;
	if (in(0) < 0) {
		out(0) = 0;
	}
	if (constraint(out) > target) {
		Scalar r = std::max(radiusAt(in(0)) + target, Scalar(0));
		out.tail(2) *= r / out.tail(2).norm();
	}

	return out;
}
Scalar LorenzCircleConstraint::radiusAt(Scalar i0) const {
	Scalar f = *mp_frictionCoeff;
	Scalar k = f * i0 + std::sqrt(m_perturbation) + m_shift;
	Scalar r = std::sqrt(k * k - m_perturbation);
	return r;
}
}  // namespace Solver
}  // namespace FrictionFrenzy
