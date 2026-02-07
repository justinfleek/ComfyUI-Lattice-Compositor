#pragma once
#include "ForceConstraint/RatioCircleConstraint.h"
#include "NonSmoothForceBase.h"

namespace FrictionFrenzy {
namespace Params {
	struct NonSmoothContactForce : public NonSmoothForce {
		bool springBasedForce;
		bool areaBasedSpring;
		Scalar springK;
		Scalar springDamp;
		Scalar restitution;
		Scalar frictionCoeff;
	};
}

namespace Solver {
class NonSmoothContactForce : public NonSmoothForceBase {
   public:
	NonSmoothContactForce(std::shared_ptr<unsigned int> logging)
		: NonSmoothForceBase(logging) {
		mp_frictionCoeff = std::make_shared<Scalar>(0.5);
		mp_constraint =
			std::make_unique<RatioCircleConstraint>(mp_frictionCoeff);
	}
	void fillFromParams(const Params::NonSmoothForce& params) override;
	int dimensions() const override { return 3; }
	int constraintsPerForce() const override { return 2; }
	NonSmoothForceType getType() const override {
		return NonSmoothForceType::NON_SMOOTH_CONTACTS;
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
	Scalar surrogateDualGap(
		const Eigen::Ref<const VectorX> lambda) const override {
		assert(lambda.size() == m_constraintVals.size());
		return -lambda.cwiseProduct(m_constraintVals).mean();
	}
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

	VectorX ACVector(const std::vector<ContactInformation>& contactInfo,
	                 const Eigen::Ref<const VectorX> vels,
	                 const Eigen::Ref<const VectorX> forces) const override;
	VectorX calculateTangentialWeight(
		const std::vector<ContactInformation>& contactInfo,
		const std::vector<RigidObjectBase*>& objects,
		const Eigen::Ref<const VectorX> vels,
		const Eigen::Ref<const VectorX> forces,
		const Scalar charMass) override;
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
	bool m_springBasedForce = false;
	bool m_areaBasedK = false;
	Scalar m_springK = 1e4;
	Scalar m_springDamp = 0.5;

   protected:
	MatrixX2 m_gradients;
	MatrixX2 m_hessians;
	VectorX m_nonSmoothK;
	VectorX m_invConstraintVals;
	VectorX m_KnormInv;
	VectorX m_sf;
	// Scalar m_compliance;
	// Scalar m_reduction;
	VectorX m_compliance;
	VectorX m_reduction;
	std::vector<Matrix3> m_WeightMat;
	std::vector<Eigen::JacobiSVD<Matrix2>> m_KmatSVD;

	std::vector<std::unordered_set<std::pair<size_t, bool>>> m_objToContactMap;

	Scalar m_currAvgMass;
};
}  // namespace Solver
}  // namespace FrictionFrenzy
