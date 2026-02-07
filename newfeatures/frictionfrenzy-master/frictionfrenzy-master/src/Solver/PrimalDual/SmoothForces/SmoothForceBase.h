#pragma once

#include "CollisionObject/RigidObjectBase.h"
#include "Contact/ContactInfo.h"

namespace FrictionFrenzy {
namespace Params {
struct SmoothForce {};
}  // namespace Params

namespace Solver {
enum class SmoothForceType { NONE, DYNAMIC_FRICTION };
class SmoothForceBase {
   public:
	virtual ~SmoothForceBase() {}
	virtual void fillFromParams(const Params::SmoothForce& params) = 0;
	virtual SmoothForceType getType() const { return SmoothForceType::NONE; }
	virtual VectorX force(
		const std::vector<Contact::ContactInformation>& contactInfo,
		const std::vector<CollisionObject::RigidObjectBase*>& objects,
		const VectorX& vels,
		const VectorX& forces,
		const int forceSkip,
		const Scalar charSpeed,
		const Scalar charMass,
		const Scalar timestep) = 0;
	virtual void linsysReserve(
		const std::vector<Contact::ContactInformation>& contactInfo,
		const std::vector<CollisionObject::RigidObjectBase*>& objects,
		std::vector<Eigen::Triplet<Scalar>>& triplets,
		std::unordered_set<std::pair<size_t, size_t>>& objectPairs) = 0;
	virtual void addForceGrad(
		const std::vector<Contact::ContactInformation>& contactInfo,
		const std::vector<CollisionObject::RigidObjectBase*>& objects,
		const VectorX& vels,
		const VectorX& forces,
		const int forceSkip,
		const Scalar charSpeed,
		const Scalar charMass,
		const Scalar timestep,
		const Scalar eps,
		std::unordered_map<std::pair<size_t, size_t>, Scalar*>&
			matPointers) = 0;
};

}  // namespace Solver
}  // namespace FrictionFrenzy
