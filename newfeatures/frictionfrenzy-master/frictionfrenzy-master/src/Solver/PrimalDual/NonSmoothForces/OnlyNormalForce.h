#pragma once
#include "NonSmoothForceBase.h"

namespace FrictionFrenzy {
namespace Params {
struct OnlyNormalForce : public NonSmoothForce {
	bool springBasedForce;
	bool areaBasedSpring;
	Scalar springK;
	Scalar springDamp;
	Scalar restitution;
};
};  // namespace Params
namespace Solver {
class OnlyNormalForce : public NonSmoothForceBase {
   public:
	OnlyNormalForce(std::shared_ptr<unsigned int> logging)
		: NonSmoothForceBase(logging) {}
	void fillFromParams(const Params::NonSmoothForce& params) override;
	int dimensions() const override { return 1; }
	int constraintsPerForce() const override { return 1; }
	NonSmoothForceType getType() const override {
		return NonSmoothForceType::ONLY_NORMAL_FORCE;
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
	;
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

	VectorX calculateTangentialWeight(
		const std::vector<ContactInformation>& contactInfo,
		const std::vector<RigidObjectBase*>& objects,
		const Eigen::Ref<const VectorX> vels,
		const Eigen::Ref<const VectorX> forces,
		const Scalar charMass) override {
		return VectorX::Ones(forces.size());
	}
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
	void fillContactForces(
		const Eigen::Ref<const VectorX> forces,
		const Eigen::Ref<const VectorX> lambda,
		const Scalar charMass,
		const Scalar charSpeed,
		const Scalar tolerance,
		const Scalar timestep,
		std::vector<ContactInformation>& contactInfo) override;

	Scalar m_restitution = 0.5;
	bool m_springBasedForce = false;
	Scalar m_springK = 1e4;
	Scalar m_springDamp = 0.5;
	bool m_areaBasedK = false;

   protected:
	VectorX m_nonSmoothK;
	VectorX m_invConstraintVals;
	VectorX m_invK;
	VectorX m_sf;
	// Scalar m_compliance;
	// Scalar m_reduction;
	VectorX m_compliance;
	VectorX m_reduction;

	Scalar m_currAvgMass;
};
}  // namespace Solver
}  // namespace FrictionFrenzy
