#pragma once

#include "Common/MatrixTypes.h"

namespace FrictionFrenzy {
namespace Solver {
class ForceConstraintBase {
   public:
	virtual ~ForceConstraintBase() {}
	virtual Scalar constraint(const Eigen::Ref<const VectorX> in) const = 0;
	virtual VectorX gradient(const Eigen::Ref<const VectorX> in) const = 0;
	virtual MatrixX hessian(const Eigen::Ref<const VectorX> in) const = 0;
	virtual Scalar radiusAt(Scalar i0) const { return 0; }
	virtual VectorX project(const Eigen::Ref<const VectorX> in,
	                        const Eigen::Ref<const VectorX> start,
	                        Scalar target = 0) const {
		VectorX out = start;
		Scalar l = 0;
		for (int i = 0; i < 30; ++i) {
			Scalar c = constraint(out);
			Scalar cDiff = target - c;
			VectorX g = gradient(out);
			VectorX diff = (out - in) - l * g;
			if (diff.norm() < 1e-10 && std::abs(cDiff) < 1e-10) {
				break;
			}
			MatrixX h = MatrixX::Identity(in.size(), in.size());
			h -= l * hessian(out);
			MatrixX lhs(in.size() + 1, in.size() + 1);
			VectorX rhs(in.size() + 1);
			lhs << h, -g, -g.transpose(), 0;
			rhs << -diff, -cDiff;
			lhs.block(0, 0, in.size(), in.size()) +=
				MatrixX::Identity(in.size(), in.size()) * diff.norm();
			Eigen::JacobiSVD svd(lhs,
			                     Eigen::ComputeFullU | Eigen::ComputeFullV);
			VectorX x = svd.solve(rhs);
			Scalar dl = x(x.size() - 1);
			VectorX dx = x.block(0, 0, x.size() - 1, 1);
			Scalar step = 1.0;
			for (int j = 0; j < 30; ++j) {
				VectorX testOut = out + step * dx;
				Scalar testL = l + step * dl;
				Scalar testC = constraint(testOut);
				Scalar testCDiff = target - testC;
				VectorX testG = gradient(testOut);
				VectorX testDiff = (testOut - in) - testL * testG;
				if (testDiff.squaredNorm() + testCDiff * testCDiff <
				    diff.squaredNorm() + cDiff * cDiff) {
					out = testOut;
					l = testL;
					break;
				}
				step *= 0.5;
			}
		}
		return out;
	}
};

}  // namespace Solver
}  // namespace FrictionFrenzy
