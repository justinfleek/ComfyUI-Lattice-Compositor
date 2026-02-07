#pragma once
#include "ForceConstraint/PerturbedSecondOrderCone.h"
#include "NonSmoothForceBase.h"

namespace FrictionFrenzy {
namespace Params {
struct SecondOrderConeForce : public NonSmoothForce {
	Scalar restitution;
	Scalar frictionCoeff;
};
}  // namespace Params

namespace Solver {

class SecondOrderConeForce : public NonSmoothForceBase {
   public:
	SecondOrderConeForce(std::shared_ptr<unsigned int> logging)
		: NonSmoothForceBase(logging) {
		mp_frictionCoeff = std::make_shared<Scalar>(0.5);
		mp_constraint =
			std::make_unique<PerturbedSecondOrderCone>(mp_frictionCoeff);
	}
	void fillFromParams(const Params::NonSmoothForce &params) override;
	int dimensions() const override { return 3; }
	int constraintsPerForce() const override { return 1; }
	NonSmoothForceType getType() const override {
		return NonSmoothForceType::SECOND_ORDER_CONE;
	}
	void preprocess(const std::vector<ContactInformation>& contactInfo,
	                const std::vector<RigidObjectBase*>& objects,
	                const Eigen::Ref<const VectorX> vels,
	                const Scalar timestep,
	                const Scalar charMass,
	                const Scalar charSpeed) override;
	void initForces(const std::vector<ContactInformation>& contactInfo,
	                const Scalar timestep,
	                const Scalar charMass,
	                const Scalar charSpeed,
	                VectorX& vels,
	                VectorX& forces,
	                VectorX& lambda) override;
	void calculateConstraints(const Eigen::Ref<const VectorX> vels,
	                          const Eigen::Ref<const VectorX> forces,
	                          const Eigen::Ref<const VectorX> lambda) override;
	void nonSmoothResiduals(const std::vector<ContactInformation>& contactInfo,
	                        const std::vector<RigidObjectBase*>& objects,
	                        const Eigen::Ref<const VectorX> vels,
	                        const Eigen::Ref<const VectorX> forces,
	                        const Eigen::Ref<const VectorX> lambda,
	                        const Scalar mu,
	                        const bool useStoredConstraints,
	                        VectorX& ru,
	                        VectorX& rf,
	                        VectorX& rl) override;
	void linsysAddition(const std::vector<ContactInformation>& contactInfo,
	                    const std::vector<RigidObjectBase*>& objects,
	                    const Eigen::Ref<const VectorX> lambda,
	                    const Eigen::Ref<const VectorX> rf,
	                    const Eigen::Ref<const VectorX> rl,
	                    Scalar eps,
	                    VectorX& y,
	                    std::unordered_map<std::pair<size_t, size_t>, Scalar*>&
	                        matPointers) override;
	void retrieveNonSmoothForceInc(
		const std::vector<ContactInformation>& contactInfo,
		const Eigen::Ref<const VectorX> lambda,
		const Eigen::Ref<const VectorX> du,
		const Eigen::Ref<const VectorX> rf,
		const Eigen::Ref<const VectorX> rl,
		const Scalar mu,
		VectorX& df,
		VectorX& dl) override;
	bool filterLineSearch(const std::vector<ContactInformation>& contactInfo,
	                      const std::vector<RigidObjectBase*>& objects,
	                      const Eigen::Ref<const VectorX> vels,
	                      const Eigen::Ref<const VectorX> velsOld,
	                      const Eigen::Ref<const VectorX> forces,
	                      const Eigen::Ref<const VectorX> lambda,
	                      Scalar mu,
	                      Scalar charMass,
	                      VectorX& du,
	                      VectorX& df,
	                      VectorX& dl) override;
	VectorX calculateTangentialWeight(
		const std::vector<ContactInformation>& contactInfo,
		const std::vector<RigidObjectBase*>& objects,
		const Eigen::Ref<const VectorX> vels,
		const Eigen::Ref<const VectorX> forces,
		const Scalar charMass) override;
	VectorX ACVector(const std::vector<ContactInformation>& contactInfo,
	                 const Eigen::Ref<const VectorX> vels,
	                 const Eigen::Ref<const VectorX> forces) const override {
		VectorX acVec = VectorX::Zero(forces.size());
		acVec.setConstant(std::numeric_limits<Scalar>::infinity());
		return acVec;
	}
	void fillContactForces(
		const Eigen::Ref<const VectorX> forces,
		const Eigen::Ref<const VectorX> lambda,
		const Scalar charMass,
		const Scalar charSpeed,
		const Scalar tolerance,
		const Scalar timestep,
		std::vector<ContactInformation>& contactInfo) override;

	Scalar m_restitution = 0.5;
	std::shared_ptr<Scalar> mp_frictionCoeff;

   protected:
	MatrixX3 m_gradients;
	MatrixX3 m_hessians;
	VectorX m_nonSmoothK;
	VectorX m_invConstraints;
	VectorX m_sf;
	std::vector<Eigen::JacobiSVD<Matrix3>> m_KmatSVD;
};

}  // namespace Solver
}  // namespace FrictionFrenzy
