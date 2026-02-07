#include "CylinderConstraint.h"

namespace FrictionFrenzy {
namespace Solver {
Scalar CylinderConstraint::constraint(
	const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Scalar r = in[1] * in[1] + in[2] * in[2];
	Scalar c = r - 1;
	return in[0] * c;
}
VectorX CylinderConstraint::gradient(const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Vector2 ret;
	ret << 2 * in[1], 2 * in[2];
	return in[0] * ret;
}
MatrixX CylinderConstraint::hessian(const Eigen::Ref<const VectorX> in) const {
	assert(in.size() == 3);
	Matrix2 ret = Matrix2::Zero();
	ret = 2 * Matrix2::Identity();
	return in[0] * ret;
}
VectorX CylinderConstraint::project(const Eigen::Ref<const VectorX> in,
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
Scalar CylinderConstraint::radiusAt(Scalar i0) const {
	return 1;
}
}  // namespace Solver
}  // namespace FrictionFrenzy
