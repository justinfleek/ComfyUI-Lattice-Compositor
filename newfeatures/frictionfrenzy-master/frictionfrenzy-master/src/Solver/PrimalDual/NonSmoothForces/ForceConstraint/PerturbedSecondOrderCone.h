#pragma once
#include "ForceConstraintBase.h"
#include <memory>
namespace FrictionFrenzy {
namespace Solver {
class PerturbedSecondOrderCone : public ForceConstraintBase {
   public:
	PerturbedSecondOrderCone(std::shared_ptr<Scalar> frictionCoeff)
		: mp_frictionCoeff(frictionCoeff) {}
	Scalar constraint(const Eigen::Ref<const VectorX> in) const override;
	VectorX gradient(const Eigen::Ref<const VectorX> in) const override;
	MatrixX hessian(const Eigen::Ref<const VectorX> in) const override;
	VectorX project(const Eigen::Ref<const VectorX> in,
	                const Eigen::Ref<const VectorX> start,
	                Scalar target = 0) const override;
	Scalar radiusAt(Scalar i0) const override;

	std::shared_ptr<Scalar> mp_frictionCoeff;
	Scalar m_perturbation = 1e-8;

   protected:
	// FloatType m_adhesion;
};
}  // namespace Solver
}  // namespace FrictionFrenzy
