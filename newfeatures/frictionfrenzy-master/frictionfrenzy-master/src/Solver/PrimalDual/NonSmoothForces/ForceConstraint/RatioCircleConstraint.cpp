#include "RatioCircleConstraint.h"

namespace FrictionFrenzy {
namespace Solver {
Scalar RatioCircleConstraint::constraint(
	const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Scalar r = in[1] * in[1] + in[2] * in[2];
	Scalar mf = *mp_frictionCoeff * in[0] + m_perturbation;

	Scalar c = r / mf - mf;
	return c;
}
VectorX RatioCircleConstraint::gradient(
	const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Vector2 ret;
	Scalar mf = *mp_frictionCoeff * in[0] + m_perturbation;
	ret << 2 * in[1], 2 * in[2];
	return ret / mf;
}
MatrixX RatioCircleConstraint::hessian(
	const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Matrix2 ret = Matrix2::Zero();
	Scalar mf = *mp_frictionCoeff * in[0] + m_perturbation;
	ret = 2 * Matrix2::Identity() / mf;
	return ret;
}
VectorX RatioCircleConstraint::project(const Eigen::Ref<const VectorX> in,
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
Scalar RatioCircleConstraint::radiusAt(Scalar i0) const {
	Scalar mf = *mp_frictionCoeff * i0 + m_perturbation;
	return mf;
}
}  // namespace Solver
}  // namespace FrictionFrenzy
